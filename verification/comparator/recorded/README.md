The completed-certificate Courtade–Kumar theorem passed Comparator's statement comparison, permitted-axiom check, and full replay into an empty Lean 4.28 kernel environment.

Checked roots:

- `CourtadeKumar.courtadeKumar_via_completed_certificates : CourtadeKumar.Statement`
- `CourtadeKumar.mutual_information_le_capacity_via_completed_certificates`

The challenge separately defines the existing conjecture statement and imports only the basic probability/information model. Its two placeholder proof bodies specify the requested statements. The solution imports the completed theorem; challenge placeholders are never imported into that solution. Comparator permits exactly `propext`, `Quot.sound`, and `Classical.choice`, with no definition holes. The compared statement quantifies over every dimension, every Boolean function, and every BSC crossover parameter at most one half, with information in bits.

The solution dependency graph contains all 42 compact-V batch facts and all 9,457 kernel arithmetic chunk facts. The transcript confirms successful statement/primitive comparison, permitted-axiom checking, zero declarations in the starting replay environment, kernel acceptance, and Comparator's final success marker. In particular, the checked theorem does not rely on native-computation axioms or admitted proofs.

Four controls passed: a valid proof was accepted, a changed statement was rejected, an unauthorized axiom was rejected, and a deliberately malformed proof term passed comparison/axiom checks but was rejected by the kernel.

The full run took 18693.675 seconds. Recorded peak child RSS was 5.642 GiB. The sampled macOS physical-footprint counter reached 17.214 GiB; RSS alone understates this run's memory requirements. See `comparator_resource_summary.json`. This is a check of the complete selected proof graph, including relevant previously cached proof bodies; it is not a clean source rebuild of every unrelated repository or library module.

Platform and implementation scope: this Mac cannot run the stock Linux Landrun workflow. Command-line GitHub downloads also failed DNS resolution. The checker source was retrieved from complete official raw-source views. The upstream comparison and axiom-checking modules are unchanged. The replay implementation is the unchanged upstream Lean4Checker dependency pinned by Comparator v4.28.0. Main has documented compatibility and memory adaptations, preserved in `comparator_driver_changes.patch`.

The successful run used `--local-objects`: it read our existing local build artifacts with extension loading disabled, collected their transitive declarations, invoked Comparator's comparison and axiom checks, and replayed them into a new empty kernel. This preserves the mathematical checks but does not claim stock Comparator's isolation against maliciously crafted object files. The original text-export route was stopped because its representation grew to tens of millions of records and several GiB; those interrupted attempts are not counted as passes.

`comparator_local.log` and its receipt contain the result. `local_inputs.json` identifies the exact checked tool and challenge sources. `upstream/`, `tools/`, and the driver patch expose the implementation. `publication_source_manifest.json` captures the current source import closure being prepared for GitHub. The copied scripts record the original work-directory workflow; their saved absolute paths are not a standalone checkout.

Upstream documentation: https://github.com/leanprover/comparator
