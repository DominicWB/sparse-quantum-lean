#!/usr/bin/env python3
"""Check the current release package; mathematical verification is done by Lean.

Run with Python 3.9+ from any directory. No third-party Python packages or
historical source files are needed.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AXIOMS = "[propext, Classical.choice, Quot.sound]"
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
AUDIT_COUNTS = {"SparseHamiltonian": 91, "SparseODE": 497, "SparseLinearSystems": 709,
                "GateEfficientHamiltonian": 142, "TimeDependentHamiltonian": 110,
                "TimeDependentODE": 154, "GateEfficientTimeDependent": 58,
                "GateEfficientODE": 471, "GeneralODE": 358, "LinearSystemLowerBound": 318,
                "SparseLowerBounds": 1047, "GateEfficientNative": 335,
                "AdaptiveHamiltonianLowerBound": 102, "ChebyshevFilter": 117,
                "TimeDependentExtensions": 135, "SparseLowerBounds/ODE": 253,
                "GeneralODEZeroTime": 22, "LowerBoundRemarks": 123, "GateEfficientBinary": 474,
                "GateEfficientBinaryTime": 27,
                "GateEfficientSynthesis": 71, "GateEfficientBinaryODE": 391,
                "ODELowerBoundExtensions": 720, "GateEfficientBinaryODETime": 97,
                "ChebyshevLinearSystem": 96, "GateEfficientSynthesisTrials": 49,
                "GateEfficientODEBudget": 55, "ChebyshevLinearSystemFinite": 114,
                "ZeroTimeRemarks": 65, "UnitaryImplementationPrecision": 59,
                "AdaptiveODELowerBound": 131, "UnitaryImplementationExtensions": 79,
                "IntegrablePathSimulation": 75, "ZeroTimeGateODE": 152,
                "TimeDependentHamiltonianLowerBound": 133,
                "ConstantODELowerBound": 49, "PhysicalODELowerBound": 102,
                "DysonSingleProgram": 103, "GateEfficientMesh": 98,
                "GateEfficientBitBudget": 116, "GateEfficientRemarks": 170,
                "DeferredMeasurementLowerBounds": 273, "AdaptiveUnitaryLowerBound": 41,
                "GateEfficientSigned": 35, "GateEfficientSelect": 86,
                "GateEfficientQuadrature": 58,
                "GateEfficientBinarySelect": 206,
                "MeasuredUnitaryLowerBound": 100, "DysonGeneralAccess": 44,
                "TimeDependentLowerBoundExtensions": 165, "ReleasedODESolverLowerBounds": 142,
                "GateEfficientBinaryNodes": 226,
                "GateEfficientSelective": 109,
                "QLSHoeffding": 41,
                "GateEfficientSchedule": 61}
# A checked audit block fixes Lean's exact axiom report for one declaration.
AUDIT_PATTERN = re.compile(
    r"/--\s*info: '(\S+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    r"\s*-\/\s*#guard_msgs\s*\(whitespace\s*:=\s*lax\)\s+in\s*#print\s+axioms\s+(\S+)")
MATHLIB_COMMIT = "520045ab14e26149ee970e2e617ca04b09bde5d6"
PROHIBITED = {"sorry", "admit", "axiom", "native_decide", "unsafe", "implemented_by"}


def standard_report(listed):
    """True when a reported axiom list is a subset of the standard three, in Lean's order."""
    names = [name.strip() for name in listed.split(",")] if listed.strip() else []
    return names == [name for name in STANDARD_AXIOMS if name in names]


def strip_lean(text, erase_strings=False):
    """Blank nested Lean comments, optionally strings, preserving line numbers.

    This is a source-hygiene lexer, not a replacement for the Lean parser.
    Ordinary quoted strings and their escapes are protected from comment parsing.
    """
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            char = text[i]
            out.append(" " if erase_strings and char != "\n" else char)
            i += 1
            if char == "\\" and i < len(text):
                out.append(" " if erase_strings and text[i] != "\n" else text[i])
                i += 1
            elif char == '"':
                quoted = False
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.append(" " * (end - i))
            i = end
        else:
            char = text[i]
            quoted = char == '"'
            out.append(" " if quoted and erase_strings else char)
            i += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    reference = json.loads((ROOT / "scripts/release_manifest.json").read_text(encoding="utf-8"))
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    # Check exactly the current Lean source inventory and pinned configuration.
    sources = sorted(ROOT.glob("*.lean"))
    for track in AUDIT_COUNTS:
        sources += sorted((ROOT / track).rglob("*.lean"))
        sources.append(ROOT / (track + ".lean"))
    sources = sorted(set(sources))
    paths = sources + [ROOT / p for p in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    actual = {p.relative_to(ROOT).as_posix(): p for p in paths}
    expected = reference["files"]
    require(set(actual) == set(expected),
            f"file inventory differs: missing {sorted(set(expected) - set(actual))}; "
            f"unexpected {sorted(set(actual) - set(expected))}")
    for name, path in actual.items():
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected.get(name),
                "release hash mismatch: " + name)

    # This supplementary source scan is not a Lean parser or kernel check.
    texts = {p.relative_to(ROOT).as_posix(): p.read_text(encoding="utf-8") for p in sources}
    prints = guards = 0
    for name, text in texts.items():
        clean = strip_lean(text, True)
        forbidden = PROHIBITED.intersection(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", clean))
        require(not forbidden, f"prohibited proof token in {name}: {sorted(forbidden)}")
        require(not re.search(r"\bset_option\s+linter(?:\.[\w.]+)?\s+false\b", clean),
                "linter suppression in " + name)
        prints += len(re.findall(r"#print\s+axioms\b", clean))
        guards += len(re.findall(r"#guard_msgs\b", clean))
    total_audits = sum(AUDIT_COUNTS.values())
    require(prints == guards == total_audits,
            f"expected exactly {total_audits} checked axiom reports")

    partial = 0
    for track, count in AUDIT_COUNTS.items():
        blocks = AUDIT_PATTERN.findall(texts[track + "/Audit.lean"])
        require(len(blocks) == count, f"expected {count} checked audit blocks in {track}")
        require(all(message == declaration for message, _, declaration in blocks),
                "audit message/declaration mismatch in " + track)
        require(all(standard_report(listed) for _, listed, _ in blocks),
                "audit report outside the standard axioms in " + track)
        partial += sum("[" + listed + "]" != AXIOMS for _, listed, _ in blocks)
        require([declaration for _, _, declaration in blocks] == reference["audits"][track],
                "audited declarations differ from release manifest: " + track)
        module = track.replace("/", ".")
        root_imports = re.findall(r"^import\s+(\S+)\s*$", texts[track + ".lean"], re.MULTILINE)
        require(root_imports == [module + ".Statements", module + ".Audit"],
                "default library must import its statements and audits: " + track)

    # The configuration hashes above cover every transitive dependency pin.
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.1",
            "unexpected Lean toolchain")
    dependencies = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    mathlib = [p for p in dependencies if p["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0].get("rev") == MATHLIB_COMMIT
            and mathlib[0].get("inputRev") == "v4.32.1", "unexpected Mathlib revision")
    require(all(re.fullmatch(r"[0-9a-f]{40}", p.get("rev", "")) for p in dependencies),
            "dependency revision is not a full Git commit")

    version = reference["release_version"]
    require(bool(re.search(r'^version\s*=\s*"' + re.escape(version) + r'"\s*$',
                           (ROOT / "lakefile.toml").read_text(), re.MULTILINE)),
            "Lake package version differs from release manifest")
    require(bool(re.search(r'^version:\s*' + re.escape(version) + r'\s*$',
                           (ROOT / "CITATION.cff").read_text(), re.MULTILINE)),
            "citation version differs from release manifest")
    require("**Package:** " + version + "." in (ROOT / "README.md").read_text(encoding="utf-8"),
            "README version differs from release manifest")

    if errors:
        for error in errors:
            print("FAIL:", error, file=sys.stderr)
        return 1
    print(f"PASS: {len(sources)} Lean source files and pinned configuration match the release hashes.")
    print(f"PASS: {total_audits} checked axiom audit blocks "
          f"({AUDIT_COUNTS['SparseHamiltonian']} Hamiltonian, "
          f"{AUDIT_COUNTS['SparseODE']} ODE, "
          f"{AUDIT_COUNTS['SparseLinearSystems']} linear-system, "
          f"{AUDIT_COUNTS['GateEfficientHamiltonian']} gate-level, "
          f"{AUDIT_COUNTS['TimeDependentHamiltonian']} time-dependent Hamiltonian, "
          f"{AUDIT_COUNTS['TimeDependentODE']} time-dependent ODE, "
          f"{AUDIT_COUNTS['GateEfficientTimeDependent']} gate-level time-dependent, "
          f"{AUDIT_COUNTS['GateEfficientODE']} gate-level ODE, "
          f"{AUDIT_COUNTS['GeneralODE']} general ODE, "
          f"{AUDIT_COUNTS['LinearSystemLowerBound']} linear-system lower bound, "
          f"{AUDIT_COUNTS['SparseLowerBounds']} Hamiltonian lower bound, "
          f"{AUDIT_COUNTS['GateEfficientNative']} native gate-level, "
          f"{AUDIT_COUNTS['AdaptiveHamiltonianLowerBound']} adaptive Hamiltonian lower bound, "
          f"{AUDIT_COUNTS['ChebyshevFilter']} Chebyshev filter, "
          f"{AUDIT_COUNTS['TimeDependentExtensions']} time-dependent extensions, "
          f"{AUDIT_COUNTS['SparseLowerBounds/ODE']} ODE lower bound, "
          f"{AUDIT_COUNTS['GeneralODEZeroTime']} zero-time general ODE, "
          f"{AUDIT_COUNTS['LowerBoundRemarks']} lower-bound remarks, "
          f"{AUDIT_COUNTS['GateEfficientBinary']} binary-data gate-level, "
          f"{AUDIT_COUNTS['GateEfficientBinaryTime']} time-dependent binary-data gate-level, "
          f"{AUDIT_COUNTS['GateEfficientSynthesis']} finite-gate-set synthesis, "
          f"{AUDIT_COUNTS['GateEfficientBinaryODE']} binary-data gate-level ODE, "
          f"{AUDIT_COUNTS['ODELowerBoundExtensions']} ODE lower-bound extensions, "
          f"{AUDIT_COUNTS['GateEfficientBinaryODETime']} time-dependent binary-data gate-level ODE, "
          f"{AUDIT_COUNTS['ChebyshevLinearSystem']} Chebyshev linear-system, "
          f"{AUDIT_COUNTS['GateEfficientSynthesisTrials']} synthesised trials, "
          f"{AUDIT_COUNTS['GateEfficientODEBudget']} binary-data ODE budget, "
          f"{AUDIT_COUNTS['ChebyshevLinearSystemFinite']} finite-gate linear-system, "
          f"{AUDIT_COUNTS['ZeroTimeRemarks']} zero-time remarks, "
          f"{AUDIT_COUNTS['UnitaryImplementationPrecision']} unitary-precision, "
          f"{AUDIT_COUNTS['AdaptiveODELowerBound']} adaptive ODE lower bound, "
          f"{AUDIT_COUNTS['UnitaryImplementationExtensions']} unitary-implementation extensions, "
          f"{AUDIT_COUNTS['IntegrablePathSimulation']} integrable-path simulation, "
          f"{AUDIT_COUNTS['ZeroTimeGateODE']} zero-time gate-level ODE, "
          f"{AUDIT_COUNTS['TimeDependentHamiltonianLowerBound']} "
          "time-dependent Hamiltonian lower bound, "
          f"{AUDIT_COUNTS['ConstantODELowerBound']} constant-coefficient ODE lower bound, "
          f"{AUDIT_COUNTS['PhysicalODELowerBound']} physical-oracle ODE lower bound, "
          f"{AUDIT_COUNTS['DysonSingleProgram']} single-program Dyson, "
          f"{AUDIT_COUNTS['GateEfficientMesh']} gate-level mesh, "
          f"{AUDIT_COUNTS['GateEfficientBitBudget']} bit-length budget, "
          f"{AUDIT_COUNTS['GateEfficientRemarks']} gate-level remarks, "
          f"{AUDIT_COUNTS['DeferredMeasurementLowerBounds']} deferred-measurement lower bounds, "
          f"{AUDIT_COUNTS['AdaptiveUnitaryLowerBound']} adaptive unitary lower bound, "
          f"{AUDIT_COUNTS['GateEfficientSigned']} signed-time gate-level, "
          f"{AUDIT_COUNTS['GateEfficientSelect']} coherent-selection gate-level, "
          f"{AUDIT_COUNTS['GateEfficientQuadrature']} source-quadrature, "
          f"{AUDIT_COUNTS['GateEfficientBinarySelect']} binary coherent-selection, "
          f"{AUDIT_COUNTS['MeasuredUnitaryLowerBound']} measured unitary lower bound, "
          f"{AUDIT_COUNTS['DysonGeneralAccess']} general-access Dyson, "
          f"{AUDIT_COUNTS['TimeDependentLowerBoundExtensions']} "
          "time-dependent lower-bound extensions, "
          f"{AUDIT_COUNTS['ReleasedODESolverLowerBounds']} released ODE solver lower bound, "
          f"{AUDIT_COUNTS['GateEfficientBinaryNodes']} computed source-node, "
          f"{AUDIT_COUNTS['GateEfficientSelective']} selective-synthesis, "
          f"{AUDIT_COUNTS['QLSHoeffding']} Hoeffding-schedule, "
          f"{AUDIT_COUNTS['GateEfficientSchedule']} manuscript-schedule); "
          f"{partial} report a strict subset of {AXIOMS}; source hygiene.")
    print("PASS: Lean/Mathlib 4.32.1; package, README and citation versions agree.")
    print("Packaging checks only; run lake build to verify the proofs and axiom audits.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
