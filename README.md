# Courtade–Kumar in Lean

This branch contains the completed-certificate Courtade–Kumar formalization for
Lean 4.28.0 and its pinned Mathlib dependency. The public entry point is
`InformationTheory.lean`, which imports the completed theorem:

```lean
import InformationTheory

#check CourtadeKumar.courtadeKumar_via_completed_certificates
#check CourtadeKumar.mutual_information_le_capacity_via_completed_certificates
```

The theorem bounds the mutual information between an arbitrary Boolean function
of a uniform Boolean input and its noisy observation by the binary symmetric
channel capacity. It quantifies over every dimension and crossover probability
between zero and one half, without certificate hypotheses.

With Elan installed, run from this directory:

```sh
lake exe cache get
lake build InformationTheory
```

The certificate proofs are substantial computations. The final theorem's proof
graph passed Comparator statement comparison, an axiom whitelist check, and
fresh replay into an empty Lean kernel. Its only axioms are `propext`,
`Quot.sound`, and `Classical.choice`; it has no admitted or native-computation
proof dependencies. The recorded full replay took approximately 5 hours and
12 minutes. See [verification/comparator](verification/comparator/README.md)
for receipts, controls, reproducible commands, and the documented macOS adapter's
scope. That adapter retains the mathematical checks but does not provide the
stock Linux isolation against hostile object files.

This cleanup retains all 1,062 local modules in the checked theorem's import
closure, including four shared modules in `InformationTheory/Discrete` and
`InformationTheory/General`. Their source bytes, the pinned dependency files,
and the existing Comparator evidence are unchanged from verified commit
`9a667b0f786c5e6e082c55239db8c1f29d683dd2`. Individual unused declarations inside
required modules have not been pruned. Historical check receipts describe the
original run; this cleanup does not claim a second full replay.

The branch `archive/pre-ck-cleanup` preserves that broader committed snapshot,
including the non-CK material, exploratory scripts, and checkpoints. `main` and
`codex/ck-only-main` contain this focused snapshot. The cleanup was prepared in a
separate checkout; uncommitted research in the original working directory was
left there and is not claimed to be part of the archive commit.
