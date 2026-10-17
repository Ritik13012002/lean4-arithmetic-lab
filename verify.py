"""Build every project module and enforce the transitive theorem axiom policy."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parent
    sources = [root / "LeanArithmeticLab.lean", *sorted((root / "LeanArithmeticLab").rglob("*.lean"))]
    if len(sources) < 7 or any(not path.is_file() for path in sources):
        raise RuntimeError("Required project source files are missing")
    modules = [".".join(path.relative_to(root).with_suffix("").parts) for path in sources]
    required = {"LeanArithmeticLab", "LeanArithmeticLab.Arithmetic", "LeanArithmeticLab.FiniteSums",
                "LeanArithmeticLab.Counterexamples", "LeanArithmeticLab.AxiomAudit",
                "LeanArithmeticLab.Division", "LeanArithmeticLab.Congruences"}
    if not required.issubset(modules):
        raise RuntimeError("Required project modules are missing")
    # A conservative source check supplements, but does not replace, the environment audit.
    forbidden = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\s|debug\.skipKernelTC|addDeclWithoutChecking")
    for path in sources:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if forbidden.search(line):
                raise RuntimeError(f"Forbidden construct at {path.relative_to(root)}:{number}")
    subprocess.run(["lake", "build", *modules], cwd=root, check=True)
    # Import the complete discovered module set, including the root and audit module.
    # This fresh command runs even when Lake reuses compiled build artifacts.
    with tempfile.TemporaryDirectory(prefix="verify-", dir=root / ".lake") as temp:
        audit = Path(temp) / "AuditAll.lean"
        audit.write_text("module\n" + "\n".join(f"import all {module}" for module in modules)
                         + "\n#audit_project\n", encoding="utf-8")
        subprocess.run(["lake", "env", "lean", str(audit)], cwd=root, check=True)
    print(f"Verified {len(modules)} modules; source check and transitive axiom audit passed.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
