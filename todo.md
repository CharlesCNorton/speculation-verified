# Outstanding work

1. Rewrite the README over the extended development: state the model, the theorem set, and the build, with Scope carrying only what the final artifact still excludes.
2. Derive the hypotheses of `disjoint_block_free` from syntactic over-approximations, a no-`TBal` predicate and static read and write footprints, so conflict freedom is checkable without computing the runs it constrains.
3. Add QuickChick generators over random blocks and speculations to stress validation across the extended language beyond the hand-built examples.
4. Refine storage, bank, and nonces from total functions on `nat` to finite maps, and extract an executable engine.
5. State global supply conservation as a sum over the finite account support, lifting `money_conservation` from per-account to total.
6. Model concurrency operationally, concurrent workers over a multi-version store under an explicit interleaving semantics, so parallelism stops living entirely inside the quantifier over read sources and `dispatch` stops being a sequential fold.
7. Prove liveness of that scheduler: every transaction commits in every fair interleaving.
8. Prove a parallel-depth bound as the critical path over the dependency graph, giving the work theorems a wall-clock companion.
9. Formalize dependency estimation and prove that orders respecting estimated dependencies tighten the re-execution count below the generic bound.
