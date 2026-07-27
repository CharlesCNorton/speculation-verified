# Outstanding work

1. Rewrite the README over the extended development: state the model, the theorem set, and the build, with Scope carrying only what the final artifact still excludes.
2. Add QuickChick generators over random blocks and speculations to stress validation across the extended language beyond the hand-built examples.
3. Refine storage, bank, and nonces from total functions on `nat` to finite maps, and extract an executable engine.
4. State global supply conservation as a sum over the finite account support, lifting `money_conservation` from per-account to total.
5. Model concurrency operationally, concurrent workers over a multi-version store under an explicit interleaving semantics, so parallelism stops living entirely inside the quantifier over read sources and `dispatch` stops being a sequential fold.
6. Prove liveness of that scheduler: every transaction commits in every fair interleaving.
