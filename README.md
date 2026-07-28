# speculation-verified

A machine-checked model of optimistic parallel transaction execution with
sequential merge and re-execution on conflict: optimistic concurrency
control with a fixed serialization order, running a linearly ordered block
of transactions concurrently while preserving sequential semantics, over a
language with contract-scoped storage, inter-contract calls, an in-flight
bank, and per-operation gas.

## The model

Execution is parameterized by three read sources: a `reader` answers the
n-th fall-through storage read, a `breader` the n-th balance read, and an
`nreader` the n-th nonce read, with no consistency required between or
within them. Reading a fixed machine is one instance (`spec_of`); torn
views are others. One execution function, one replay lemma, and
state-based speculation inside the quantification by construction.

The machine is contract storage, a bank, and a nonce map, typed apart.
Storage is scoped by executing contract: a key is a contract paired with a
slot, reads and writes touch the executing contract's own scope, and
`TCall` runs another contract's code in that contract's scope and frame.
A reverted frame keeps its read logs and its gas consumption and
surrenders its writes, events, transfers, refunds, and bank deltas, so
reentrant call cycles terminate by gas with per-frame isolation. Gas is
charged per operation through a cost table; clearing a storage slot
accrues a refund, capped at half the consumption. The bank is in-flight:
a transaction's whole gas cost is held up front, `TPay` settles at the
point of pay against the prefix bank adjusted by the transaction's own
holds and settlements and passes success or failure to its continuation,
and `TBal` observes the same in-flight balance; `TNonce` reads the prefix
nonce map. Loop tests are logged, validated reads, so gas bounds
unbounded iteration. An unfunded transaction is rejected against the true
prefix bank before any execution and counts as zero work. Receipts
distinguish completion, revert, and rejection and carry effective gas,
committed writes, events, and transfers in program order.

The merge validates each speculative storage log against the merged prefix
storage, each balance log against the merged prefix bank, and each nonce
log against the merged prefix nonces, by value; agreeing outcomes commit
unchanged, disagreeing ones re-execute. The scheduler `dispatch` runs
transactions in an arbitrary order over a speculative machine evolving by
the same gated step as the reference semantics.

## Theorems

Safety and observational equivalence: `optimistic_correct` equates merged
storage, bank, nonces, and receipts with sequential execution for every
speculation; `speculation_irrelevant` and `scheduler_correct` are its
one-line corollaries.

Scheduling: `fast_path` (perfect speculation re-executes nothing),
`dispatch_in_order` (in-order dispatch reproduces perfect speculation),
`scheduler_in_order_optimal`, and `dispatch_complete` (a permutation
order dispatches every position, so the base-state default arm is dead).
`reexec_bound` bounds re-executions by the block length, and
`reexec_per_tx` decomposes the count into one boolean per position, so
each transaction re-executes at most once.

Retry: the loop is a proof object. `jmach` is the round-indexed
re-speculation, `jmach_progress` the wavefront lemma that after k rounds
the first k positions speculate against their true prefix machines,
`retry_round_progress` the per-round bound, and `retry_loop_converges`
convergence in at most n rounds; `retry_progress` and `retry_converges`
state the underlying prefix-agreement bound.

Work: `executions` counts actual executor invocations in the instrumented
merge; `executions_law` proves it equals the non-rejected count plus
re-executions, `work_upper` and `work_lower` pin it between the
non-rejected count and twice the block length, and `work_inorder` and
`work_disjoint` pin it to exactly the non-rejected count for in-order
scheduling and statically certified conflict-free blocks.

Economics: `money_conservation` is the per-account ledger across gas,
coinbase income, and transfers from any frame, lifted to the merge by
`omerge_money_conservation`; `apply_law` is the settlement ledger;
`supply_conservation` states that the total over the finite bank support
of the engine is invariant, with no hypotheses on the map;
`runp_gas_bound` and `pauper_rejected` pin gas soundness; `nonce_law`
states the nonce ledger: an account's nonce advances by exactly its
non-rejected transaction count.

Conflict freedom is statically checkable: `fp` certifies read and write
footprints on the syntax alone, across calls, with no rule for balance,
pay, or nonce operations; `fp_sound` bounds every run by its certificate,
and `static_disjoint_free` proves a block with certified pairwise
write-read-disjoint footprints merges from base-state speculation without
a single re-execution.

Versioned speculation: `mvstor` presents a position the base storage
overlaid, in index order, with the committed buffers of selected lower
positions. `estimated_order_free` proves that an estimate covering every
forward write-read intersection, under a dispatch order placing estimated
dependencies first, yields zero re-executions. `level_rounds_bound` and
`level_rounds_converge` bound speculation rounds by any height function
that increases along dependencies, the critical path of the dependency
graph.

Operational concurrency: workers over the multi-version store under an
explicit interleaving semantics, executing any pending position at any
time, with a commit wavefront that validates, re-executes, or rejects the
head. `op_safety` equates the committed machine and receipts with
sequential execution for every interleaving; `op_liveness` proves any
schedule with at least as many commit actions as the block is long
finishes it.

Engine: storage, bank, and nonces refine to association maps;
`engine_seq_correct` and `engine_merge_correct` prove the map-level
executor and merge simulate the abstract semantics on receipts and
pointwise machines, and the build extracts the engine to OCaml.

## Examples and randomized validation

Executable `Example`s compute the claims on concrete blocks: conflicts
detected and corrected with exact fees; torn views; stale balance and
stale nonce reads caught by their own logs; in-flight balances visible
under the upfront hold; point-of-pay settlement with observable
insufficiency and the revert idiom as a continuation choice; calls
running in callee scope; a reverted frame surrendering its writes while
its gas stays consumed; a reentrant call cycle terminating by gas;
refunds accruing on storage clears and capped at half the consumption;
loops ending in exactly their gas and divergent loops burning out;
rejection observably distinct from revert; the operational scheduler
replaying out-of-order executions into sequential receipts; and a static
footprint certificate discharged by constructors. A linear-congruential
harness then cross-validates the merge against sequential execution on
three hundred random blocks under random torn speculations, comparing
receipts, sampled state, the work law, the per-position flags, and the
money ledger, all by computation (`harness_300`).

## Related work

Optimistic concurrency control with commit-time validation is Kung and
Robinson (ACM TODS, 1981); serializability theory goes back to
Papadimitriou (JACM, 1979); Block-STM (Gelashvili et al., PPoPP 2023)
develops the same validation discipline for parallel execution over a
fixed serialization order with a multi-version store. This development
mechanizes the ordered-commit protocol and claims no algorithmic novelty;
the contribution is an executable, machine-checked treatment of safety,
observational equivalence, scheduler optimality, retry convergence, work
accounting, static conflict freedom, dependency estimation, parallel
depth, an operational concurrent scheduler with liveness, and the
economic ledgers, under a speculation model wide enough to include
inconsistent read views, over a language with calls and an in-flight
bank.

## Scope

Validation is by value, so ABA passes and is proven harmless for every
observable. The operational model's actions are atomic at transaction
granularity: an execution reads the versioned store at one instant, and
interleaving below that granularity is covered by the read-source
quantification rather than modeled as instruction steps. Balance and
nonce readers of the operational store answer from the committed prefix.
Costs are per constructor, refunds accrue only for storage clears under
the half cap, and there is no dynamic pricing. Contracts read and write
only their own storage scope, and calls carry no value; value moves
through `TPay`. The parallel-depth bound is parameterized by a height
function on positions. The extracted engine is the association-map
executor and merge, with no persistence layer.

## Build

```
coqc OptimisticExecution.v
```

Rocq 9.0. The build computes the examples and the three-hundred-seed
harness, prints `Print Assumptions` for every result at the end of the
file, and extracts the engine to `occ_engine.ml`.
