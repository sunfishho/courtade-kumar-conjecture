The completed-certificate Courtade–Kumar theorem passed Comparator's statement comparison, permitted-axiom check, and full fresh kernel replay on Lean 4.28.0. The recorded replay took 311.56 minutes and checked a graph of 328,920 declarations, including all 42 compact-V batches and 9,457 kernel arithmetic chunks.

The checked roots are `CourtadeKumar.courtadeKumar_via_completed_certificates` and `CourtadeKumar.mutual_information_le_capacity_via_completed_certificates`, in `InformationTheory/CourtadeKumar/CompactCertificateClosure.lean`. The theorem has no certificate hypotheses and depends only on `propext`, `Quot.sound`, and `Classical.choice`. It has no admitted or native-computation proof dependencies. This describes the selected theorem's proof graph; historical, unused repository declarations are outside this result.

The challenge independently defines the conjecture statement using the basic probability and information model. Its two `sorry` bodies are Comparator challenge placeholders; they never enter the solution or its permitted axioms. The check establishes the formal statement against that model and is not a separate mathematical review of the model's adequacy.

The upstream comparison and axiom modules are unchanged. The unchanged Lean4Checker replayer is pinned to `b7398199245524275543dec6113229c9bb4902e5`, the dependency used by Comparator v4.28.0. The local driver loads existing local objects with extension loading disabled, collects the dependency graph, then runs the mathematical checks and replays into a kernel with zero imported declarations. This avoids the very large text export. It does not provide stock Comparator's Linux isolation against malicious object files. See `recorded/comparator_driver_changes.patch` and `recorded/provenance.json` for the exact adaptation.

To reproduce with Lean/Elan and Python 3 installed, run from the repository root:

```sh
python3 verification/comparator/recheck.py --controls-only
python3 verification/comparator/recheck.py
```

The first command builds the preserved checker and runs four controls: a valid proof, a changed statement, a forbidden axiom, and a malformed proof term. The second additionally builds the challenge and solution and replays the complete CK proof graph. Building the certificate sources and replaying the graph are substantial computations. Dependencies follow the repository's pinned Lake manifest; this portable setup uses an ordinary path dependency on the repository, while the recorded local run used a precedence-preserving artifact overlay. The malformed-term fixtures are compressed text exports of the tiny controls, not trusted proof axioms.

New transcripts and receipts are written under `.lake/check-runs/` beside this file. `recorded/` contains the completed original run, exact source hashes, and its four control results; machine-specific paths in those receipts document that original run. `tools/` preserves the compiled checker source and `upstream/` its unmodified reference sources. See the [upstream Comparator documentation](https://github.com/leanprover/comparator).
