#!/usr/bin/env python3
"""Read-only regression check: relocated production definitions are unchanged."""
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[1]
BASE = "80e1961a2e8ad4694fd62fb171f4874643d364ff"
OWNERS = [
    [
        "LRHighShapeCertificateCoordinatesCore",
        "lrCertificateE"
    ],
    [
        "LRHighShapeCertificateCoordinatesCore",
        "lrCertificateX"
    ],
    [
        "LRHighShapeCertificateCoordinatesCore",
        "lrCertificateV"
    ],
    [
        "LRCertificateOmega",
        "lrCertificateB"
    ],
    [
        "LRCertificateOmega",
        "lrCertificateOmega"
    ],
    [
        "LRHighShapeKernelAssembly",
        "lrCertificateY0"
    ],
    [
        "LRHighShapeKernelAssembly",
        "lrCertificateW"
    ],
    [
        "LRHighShapeKernelAssembly",
        "lrCertificatePWValue"
    ],
    [
        "LRHighShapeKernelAssembly",
        "lrCertificatePW"
    ],
    [
        "LRCertificateG0",
        "lrCertificateG0"
    ],
    [
        "LRHighShapeGAssembly",
        "lrCertificateGShapeValue"
    ],
    [
        "LRHighShapeGAssembly",
        "lrCertificateGShape"
    ],
    [
        "LRHighShapeABAssembly",
        "lrCertificateBFlowValue"
    ],
    [
        "LRHighShapeABAssembly",
        "lrCertificateBFlow"
    ],
    [
        "LRDeterminantD1",
        "lrDeterminantY"
    ],
    [
        "LRDeterminantD1",
        "lrDeterminantD1"
    ],
    [
        "LRDeterminantFlowCoordinates",
        "lrDeterminantPsi"
    ],
    [
        "LRDeterminantFlowCoordinates",
        "lrDeterminantDelta"
    ],
    [
        "LRDeterminantSignAlgebra",
        "lrDeterminantFirstBracket"
    ],
    [
        "LRDeterminantRegionInterfaces",
        "LRDeterminantFirstBracketAt"
    ]
]
CORE = REPO / "InformationTheory/CourtadeKumar/LRDeterminantScalarTargetCore.lean"

def declaration(text, name):
    matches = re.findall(
        r"^(?:noncomputable )?def " + re.escape(name) + r"\b[\s\S]*?(?=\n\n)",
        text, re.M)
    if len(matches) != 1:
        raise ValueError(f"Expected exactly one declaration of {name}, got {len(matches)}")
    return matches[0]

def main():
    core = CORE.read_text()
    cache = {}
    for owner, name in OWNERS:
        original_owner = ("LRHighShapeCertificateCoordinates"
                          if owner == "LRHighShapeCertificateCoordinatesCore" else owner)
        relative = f"InformationTheory/CourtadeKumar/{original_owner}.lean"
        if relative not in cache:
            cache[relative] = subprocess.check_output(
                ["git", "show", f"{BASE}:{relative}"], cwd=REPO, text=True)
        if declaration(cache[relative], name) != declaration(core, name):
            raise ValueError(f"Production definition changed: {name}")
        current = (REPO / f"InformationTheory/CourtadeKumar/{owner}.lean").read_text()
        if re.search(r"^(?:noncomputable )?def " + re.escape(name) + r"\b", current, re.M):
            raise ValueError(f"Old owner still redeclares {name}")
        if "import InformationTheory.CourtadeKumar.LRDeterminantScalarTargetCore" not in current:
            raise ValueError(f"Old owner does not import the new core: {owner}")
    print(f"PASS: all {len(OWNERS)} production declarations are byte-for-byte unchanged.")
    print("Only module ownership changed; this check does not replace Lean compilation.")

if __name__ == "__main__":
    main()
