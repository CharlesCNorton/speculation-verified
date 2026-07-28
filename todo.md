# Outstanding work

1. Version-stamped validation: commit-time version agreement with a
   soundness lemma reducing it to value agreement.
2. Multi-version balance and nonce overlays for the operational store, so
   speculation ahead of the wavefront sees executed lower positions' bank
   and nonce effects.
3. A theorem connecting the idealized versioned-store optimality results
   to the operational store's speculative buffers.
4. Incarnation counters, eager validation, and abort in the operational
   scheduler.
5. Fairness-based completion, an operational fast path, and a bound on
   operational re-executions.
6. Engine on balanced maps with deletion on zero and a persistence
   round-trip.
7. A map-level randomized harness and a compiled run of the extracted
   engine.
8. Harness comparison sets derived from receipts rather than fixed
   samples.
9. The operational commit arm and the map-level merge routed through the
   shared validate-or-re-execute step.
