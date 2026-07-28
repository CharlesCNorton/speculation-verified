# speculation-verified

A machine-checked model of optimistic parallel transaction execution with
sequential merge and re-execution on conflict: optimistic concurrency
control with a fixed serialization order, running a linearly ordered block
of transactions concurrently while preserving sequential semantics, over a
language with contract-scoped storage, inter-contract calls carrying value
and returning values, an in-flight bank, transition-priced gas with warm
and cold access sets, refunds, and a base fee market with nonce-gated
admission.

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
`TCall c arg amt` runs another contract's code in that contract's scope
and frame, passing an argument, settling `amt` in flight, and returning
`Some v` on completion or `None` on revert to the caller's continuation.
A reverted frame keeps its read logs, its gas consumption, and its warm
sets, and surrenders its writes, events, transfers, refunds, and bank
deltas, so reentrant call cycles terminate by gas with per-frame
isolation.

Gas is priced by transition rather than by operation: writing a slot
charges the set price when it moves off zero and the reset price
otherwise, the first touch of a storage key or an account in a
transaction pays a cold surcharge and later touches do not, and clearing a
nonzero slot accrues a refund capped at half the consumption. The warm
sets are journaled: a reverted frame's writes are dropped but the keys and
accounts it touched stay warm. The bank is in-flight: the whole gas cost
is held up front at the effective price, `TPay` settles at the point of
pay against the prefix bank adjusted by the transaction's own holds and
settlements and passes success or failure to its continuation, `TCall`
settles its value the same way, and `TBal` observes the same in-flight
balance. `TNonce` reads the prefix nonce map. Loop tests are logged,
validated reads over an arbitrary boolean test, so gas bounds unbounded
iteration.

An item carries a fee account, a nonce, code, a gas limit, and a tip.
Admission is checked against the true prefix machine before any execution:
the limit covers the intrinsic cost, the nonce is exactly the account's
next, and the account funds the whole limit at base fee plus tip. A
rejected transaction performs no run and counts as zero work. An executed
transaction returns its unconsumed and refunded gas, pays the consumed
portion's tip to the coinbase, burns the consumed portion's base fee, and
bumps its nonce; a reverted transaction pays for what it consumed with no
refund and bumps its nonce all the same. Receipts distinguish completion,
revert, and rejection and carry effective gas, committed writes, events,
and transfers in program order.

## The merge

`cstep` is the single validate-or-re-execute step: the gate is checked
against the true prefix machine first, then the storage log against the
merged prefix storage, the balance log against the merged prefix bank, and
the nonce log against the merged prefix nonces, all by value. Agreement
commits the speculative outcome unchanged; disagreement re-executes
against the true prefix state. The merge, the instrumented merge that
counts executor invocations, the engine, and the operational commit
wavefront all route through that one step, so they cannot drift apart.

## Theorems

Safety and observational equivalence: `optimistic_correct` equates merged
storage, bank, nonces, and receipts with sequential execution for every
speculation; `speculation_irrelevant` and `scheduler_correct` are its
one-line corollaries. `replay` is the underlying lemma: a state agreeing
with every logged read reproduces a run exactly, whatever the read sources
were. `inflight_sound` and `commit_bank_law` connect a frame's in-flight
arithmetic to the settled ledger.

Scheduling: `fast_path` (perfect speculation re-executes nothing),
`dispatch_in_order` (in-order dispatch reproduces perfect speculation),
`scheduler_in_order_optimal`, and `dispatch_complete` (a permutation order
dispatches every position, so the base-state default arm is dead).
`reexec_bound` bounds re-executions by the block length, and
`reexec_per_tx` decomposes the count into one boolean per position, so
each transaction re-executes at most once.

Retry: the loop is a proof object. `jmach` is the round-indexed
re-speculation, `jmach_progress` the wavefront lemma that after k rounds
the first k positions speculate against their true prefix machines,
`retry_round_progress` the per-round bound, and `retry_loop_converges`
convergence in at most n rounds. `retry_work_bound` bounds the total work
of the retry loop, and `retry_flags` with `selective_retry_bound` bound
the selective variant that re-speculates only conflicted positions.

Work: `executions` counts actual executor invocations in the instrumented
merge; `executions_law` proves, with no hypotheses, that it equals the
non-rejected count plus re-executions, `work_upper` and `work_lower` pin
it between the non-rejected count and twice the block length, and
`work_inorder` and `work_disjoint` pin it to exactly the non-rejected
count for in-order scheduling and for statically certified conflict-free
blocks.

Gas and fuel: `runp_gas_bound` bounds consumption by the limit,
`runp_fuel_ext` proves any fuel above the gas budget yields the same run
when every cost is at least one, and `fuel_not_binding` discharges the
fuel parameter for admitted transactions.

Economics: `money_conservation` is the per-account ledger across gas, the
burn, coinbase income, and transfers from any frame, lifted to the merge
by `omerge_money_conservation`; `apply_law` is the settlement ledger;
`supply_conservation_abstract` states that balances plus the burn are
invariant over any duplicate-free cover of the block's parties;
`nonce_law` states that an account's nonce advances by exactly its
non-rejected transaction count; `gate_rejected` and `pauper_rejected` pin
the admission side.

Conflict freedom is statically checkable: `fp` certifies read and write
footprints on the syntax alone, across calls; `fp_sound` bounds every run
by its certificate, and `static_disjoint_free` proves a block with
certified pairwise write-read-disjoint footprints merges from base-state
speculation without a single re-execution. `static_check` is the
executable checker over a first-order surface language and a contract
library, and `checked_disjoint_free` proves a passing block conflict-free,
so the certificate is discharged by computation rather than by hand.

Versioned speculation: `mvstor` presents a position the base storage
overlaid, in index order, with the committed buffers of selected lower
positions. `estimated_order_free` proves that an estimate covering every
forward write-read intersection, under a dispatch order placing estimated
dependencies first, yields zero re-executions. `level_rounds_bound` and
`level_rounds_converge` bound speculation rounds by any height function
that increases along dependencies; `Lcan` is the canonical such function,
the critical path of the dependency graph, with
`canonical_level_increases` and `canonical_rounds_converge`.

Operational concurrency: workers over a multi-version store under an
explicit interleaving semantics, executing or validating any pending
position at any time, with a commit wavefront at the head. Each write
carries a position and an incarnation, and `vercheck_valid` proves version
agreement implies value agreement, so commit-time validation may compare
stamps instead of values. `op_safety` equates the committed machine and
receipts with sequential execution for every interleaving; `op_liveness`
proves any schedule with at least as many commit actions as the block is
long finishes it; `op_fair_completion` finishes it under any schedule
whose windows are commit-dense; `op_reexec_bound` bounds re-executions by
the block length; `op_overlay_true` proves the overlay a position reads is
the true prefix state once its predecessors have run; and `op_fast_path`
proves in-order execution followed by commits produces the sequential
machine and receipts with no re-execution at all.

Engine: storage, bank, and nonces refine to balanced maps, keyed
lexicographically for storage and by account otherwise, with a write of
zero deleting its binding. `engine_correct` proves the map-level merge
reproduces the map-level sequential run for every speculation, through the
same shared step; `engine_supply` is the supply law at map level;
`engine_dump_nonzero` proves no reachable engine state binds zero, so a
dump lists exactly the live slots and funded accounts;
`persistence_roundtrip` and `engine_persist` prove that dumping a state
and reloading it restores every lookup and leaves a block's receipts
unchanged.

## Examples and randomized validation

Executable `Example`s compute the claims on a concrete block: a call that
increments a counter, a nested call that emits its callee's return value,
a stale nonce rejected, a frame that reverts after writing, a loop that
burns out its gas, and a clear that earns the refund, with the resulting
receipts, storage, balances, nonces, and burn all computed. The same
block is run under base-state, junk, and prefix speculation, with the
conflict counts, per-position flags, and executor invocation counts
computed; through the engine, with the dumped state and its reload
computed; through the operational scheduler in three interleavings, two
costing no re-execution and one costing exactly two; and through the
static checker, which passes a disjoint block and rejects this one.

A linear-congruential harness then cross-validates three hundred random
blocks of five transactions over three accounts and a three-contract
library, with per-account nonces sometimes deliberately stale, gas limits
that sometimes bind, and speculations drawn from true prefix states, the
base state, junk, and half-position states, with the speculation list
sometimes short. Each block is checked at every layer: merge receipts
against sequential receipts, merged state against sequential state on the
keys and accounts the receipts name, the engine's receipts and lookups,
the engine merge's receipts and conflict count, the dump round-trip, the
absence of zero bindings, the scheduler's receipts under in-order and
reversed execution with no re-execution when every transaction is
admitted, and supply conservation over the block's parties (`harness_300`).

## Related work

Optimistic concurrency control with commit-time validation is Kung and
Robinson (ACM TODS, 1981); serializability theory goes back to
Papadimitriou (JACM, 1979); Block-STM (Gelashvili et al., PPoPP 2023)
develops the same validation discipline for parallel execution over a
fixed serialization order with a multi-version store. Gas metering with
transition pricing and warm and cold access sets follows EIP-2200 and
EIP-2929; the fee market with a burned base fee and a tip to the coinbase
follows EIP-1559. This development mechanizes the ordered-commit protocol
and claims no algorithmic novelty; the contribution is an executable,
machine-checked treatment of safety, observational equivalence, scheduler
optimality, retry convergence, work accounting, static conflict freedom,
dependency estimation, parallel depth, an operational concurrent scheduler
with liveness and version-stamped validation, a balanced-map engine with
persistence, and the economic ledgers, under a speculation model wide
enough to include inconsistent read views.

## Scope

Validation is by value, so ABA passes and is proven harmless for every
observable; the operational layer additionally validates by version, and
the two are proved to agree. The operational model's actions are atomic
at transaction granularity: an execution reads the versioned store at one
instant, and interleaving below that granularity is covered by the
read-source quantification rather than modeled as instruction steps.
Balance and nonce readers of the operational store answer from the
committed prefix. The base fee is a parameter fixed for the block; there
is no update rule across blocks. Refunds accrue only for storage clears,
under the half cap. Contracts read and write only their own storage
scope. The parallel-depth bound is parameterized by a height function on
positions, with the critical path as the canonical instance. Extracted
numbers are unary naturals, so the driver converts at the boundary.

## Build

```
rocq compile OptimisticExecution.v
```

Rocq 9.0. The build computes the examples and the three-hundred-seed
harness, reports the assumption audit for every principal result, and
writes the extracted engine to `occ_engine.ml`.
