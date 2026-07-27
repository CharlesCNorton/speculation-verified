# speculation-verified

A machine-checked model of optimistic parallel transaction execution with
sequential merge and re-execution on conflict: optimistic concurrency control
with a fixed serialization order, running a linearly ordered block of
transactions concurrently while preserving sequential semantics.

## The model

Execution is parameterized by a read source: a `reader` answers the n-th
fall-through read of a given address, with no consistency required between
answers. Reading a fixed storage is one instance (`of_state`); torn views are
other instances. One execution function, one replay lemma, and state-based
speculation inside the quantification by construction.

The machine is contract storage, a bank, and a nonce map, typed apart:
reads and writes touch storage; gas charging, coinbase crediting, and
transfer settlement touch the bank; nothing else does. The language has
reads, writes, events (`TEmit`), transfers (`TPay`), explicit revert, and
state-dependent loops (`TWhile`); execution recurses on gas, so gas bounds
unbounded iteration, and loop tests are logged, validated reads. Each block
item carries a fee account, a gas limit, and a gas price. Below the cost
ceiling the transaction executes and pays for what it consumed, the payment
is credited to the coinbase, declared transfers settle atomically against
the prefix bank with insufficiency reverting the transaction, and the
sender's nonce advances; above it, the transaction is rejected untouched.
Receipts distinguish completion, revert, and rejection, and carry gas
consumed, committed writes, emitted events, and settled transfers.

The merge validates each speculative read log against the merged prefix
storage by value, commits agreeing outcomes unchanged, re-executes
disagreeing ones. The scheduler `dispatch` runs transactions in an arbitrary
order over a speculative machine evolving by the same gated step as the
reference semantics, each transaction at most once.

## Theorems

Safety and observational equivalence: `optimistic_correct` equates merged
storage, bank, nonces, and receipts with sequential execution for every
speculation; `speculation_irrelevant` and `scheduler_correct` follow for
every speculation and every dispatch order.

Scheduling: `fast_path` (perfect speculation re-executes nothing),
`dispatch_in_order` (in-order dispatch reproduces perfect speculation
exactly), `scheduler_in_order_optimal` (hence zero re-executions for every
block), `reexec_bound` (each transaction re-executes at most once).

Retry convergence: `retry_progress` is the wavefront bound, once the first r
transactions speculate against their true prefix states at most n − r
re-executions remain, and `retry_converges` closes the loop in at most n
rounds.

Work: `executions` counts transaction runs; `work_bound` pins it between n
and 2n, and `work_inorder` and `work_disjoint` pin it to exactly n for
in-order scheduling and conflict-free blocks.

Economics: `money_conservation` is the per-account ledger law across gas,
coinbase income, and transfers, final balance plus debits equals initial
balance plus credits, and `omerge_money_conservation` lifts it to the merge
under every speculation; `settle_law` is the transfer-settlement ledger;
`runp_gas_bound` and `pauper_rejected` pin gas soundness; `nonce_law` states
the nonce ledger: an account's nonce advances by exactly its non-rejected
transaction count.

Conflict freedom: `disjoint_block_free`, derived from `valid_stable` and
`commit_untouched`, proves a block with pairwise-disjoint footprints merges
from base-state speculation without a single re-execution.

Executable `Example`s compute the claims on concrete blocks: stale and
torn-view conflicts detected and corrected with exact fees; the scheduler
perfect in order and recovering out of order; transfers settling and
insufficient transfers reverting yet paying gas; events in receipts and
discarded on revert; nonces advancing; rejection observably distinct from
revert; storage writes to the fee address buying nothing; a countdown loop
ending in exactly its gas; a divergent loop burning out and paying.

## Related work

Optimistic concurrency control with commit-time validation is Kung and
Robinson (ACM TODS, 1981); serializability theory goes back to Papadimitriou
(JACM, 1979); Block-STM (Gelashvili et al., PPoPP 2023) develops the same
validation discipline for parallel execution over a fixed serialization
order. This development mechanizes the ordered-commit protocol and claims no
algorithmic novelty; the contribution is an executable, machine-checked
treatment of safety, observational equivalence, scheduler optimality, retry
convergence, work bounds, conflict freedom, and the economic ledgers, under a
speculation model wide enough to include inconsistent read views.

## Scope

Validation is by value, so ABA passes and is proven harmless for every
observable. Worker interleaving below transaction granularity and dependency
estimation are not proof objects; the reader quantification covers what they
can expose to reads, and the retry theorems cover their convergence
obligation. Per-opcode gas costs are uniform; there are no refunds beyond
charging only what was consumed, and no wall-clock claims beyond the work
theorems.

## Build

```
coqc OptimisticExecution.v
```

Rocq 9.0. `Print Assumptions` for every result is included at the end of the
file.
