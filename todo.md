# Outstanding work

1. Align `_CoqProject` with the README build line by compiling under `-Q . OCC` or dropping the unused mapping.
2. Rewrite the README to present `scheduler_correct` and `speculation_irrelevant` as the one-line corollaries of `optimistic_correct` they are, to describe `reexec_bound` as an aggregate bound, and to disclose in Scope the absence of contracts, calls, and reentrancy.
3. Remove the dead `++ sps'` from `retry_converges`, where `firstn (length ts) (prefix_specs m ts)` is already the whole list and the appended tail is never consumed.
4. Factor the eight-constructor destruct boilerplate repeated across the five `runp` inductions into one generalized lemma or a custom tactic, before any language extension multiplies it.
5. Prove the per-transaction re-execution bound, that each position contributes at most one re-execution, so the claim exists as a theorem and not as a reading of the aggregate.
6. Gate rejection ahead of execution so a rejected transaction performs no run and counts as zero work.
7. Define an operational counter of `runp` invocations through `step` and `omerge`, and prove `executions` equal to it, so "executions counts transaction runs" is a theorem rather than a stipulation.
8. Restrict `dispatch` to complete orders, permutations of the block indices, removing the silent base-state default for never-dispatched positions.
9. Derive the hypotheses of `disjoint_block_free` from syntactic over-approximations, a no-`TBal` predicate and static read and write footprints, so conflict freedom is checkable without computing the runs it constrains.
10. Define the retry loop as a proof object: a round-indexed iteration that re-speculates failed transactions against merged prefix states.
11. Prove the per-pass progress lemma, that each pass extends the prefix of speculations agreeing with true prefix states by at least one position, and re-derive convergence in at most n rounds from it, so "closes the loop" is a theorem rather than narrative.
12. Parameterize gas by a per-constructor cost function and add refund semantics, replacing the uniform unit cost.
13. Add a nonce-read instruction with its own logged, validated read path.
14. Extend `TBal` and `TPay` to an in-flight bank, deducting gas up front as the EVM does and settling transfers at the point of `TPay` with an observable outcome, and reprove the ledgers under it.
15. Add contract-scoped storage and inter-contract calls with per-frame revert semantics, bringing reentrancy inside the model rather than inside the disclosure.
16. Add QuickChick generators over random blocks and speculations to stress validation across the extended language beyond the hand-built examples.
17. Refine storage, bank, and nonces from total functions on `nat` to finite maps, and extract an executable engine.
18. State global supply conservation as a sum over the finite account support, lifting `money_conservation` from per-account to total.
19. Model concurrency operationally, concurrent workers over a multi-version store under an explicit interleaving semantics, so parallelism stops living entirely inside the quantifier over read sources and `dispatch` stops being a sequential fold.
20. Prove liveness of that scheduler: every transaction commits in every fair interleaving.
21. Prove a parallel-depth bound as the critical path over the dependency graph, giving the work theorems a wall-clock companion.
22. Formalize dependency estimation and prove that orders respecting estimated dependencies tighten the re-execution count below the generic bound.
