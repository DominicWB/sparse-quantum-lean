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
AUDIT_COUNTS = {"SparseHamiltonian": 91, "SparseODE": 497}
MATHLIB_COMMIT = "520045ab14e26149ee970e2e617ca04b09bde5d6"
PROHIBITED = {"sorry", "admit", "axiom", "native_decide", "unsafe", "implemented_by"}


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

    pattern = re.compile(
        r"/--\s*info: '([^'\s]+)' depends on axioms: " + re.escape(AXIOMS) +
        r"\s*-\/\s*#guard_msgs\s*\(whitespace\s*:=\s*lax\)\s+in\s*#print\s+axioms\s+(\S+)")
    for track, count in AUDIT_COUNTS.items():
        pairs = pattern.findall(texts[track + "/Audit.lean"])
        require(len(pairs) == count, f"expected {count} checked audit blocks in {track}")
        require(all(message == declaration for message, declaration in pairs),
                "audit message/declaration mismatch in " + track)
        require([declaration for _, declaration in pairs] == reference["audits"][track],
                "audited declarations differ from release manifest: " + track)
        root_imports = re.findall(r"^import\s+(\S+)\s*$", texts[track + ".lean"], re.MULTILINE)
        require(root_imports == [track + ".Statements", track + ".Audit"],
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
          f"{AUDIT_COUNTS['SparseODE']} ODE); source hygiene.")
    print("PASS: Lean/Mathlib 4.32.1; package, README and citation versions agree.")
    print("Packaging checks only; run lake build to verify the proofs and axiom audits.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("FAIL:", error, file=sys.stderr)
        sys.exit(1)
