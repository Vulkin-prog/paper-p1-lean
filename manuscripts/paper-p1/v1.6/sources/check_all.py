#!/usr/bin/env python3
"""Build P1 V1.6 and run its document checks and selected finite identities.

This command is not a verifier for the asymptotic mathematical proofs.
The exact scope of each diagnostic is listed in README.txt.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / "build" / "checks"
LOGS.mkdir(parents=True, exist_ok=True)
DIAGNOSTICS = (
    ("heterogeneous_formal_checks.py", "heterogeneous_formal_checks.json"),
    ("stopped_exact_checks.py", "stopped_exact_checks.json"),
    ("coefficient_exact_checks.py", "coefficient_exact_checks.json"),
    ("channel_and_triple_checks.py", "channel_and_triple_checks.json"),
    ("certify_biquadratic.py", "biquadratic_certificate.json"),
)
STEPS = [
    ("build_articles", [sys.executable, "build.py"], None),
    *[(name[:-3], [sys.executable, f"diagnostics/{name}"], f"diagnostics/{output}")
      for name, output in DIAGNOSTICS],
    ("references", [sys.executable, "editorial/check_references.py"],
     "editorial/references_audit.json"),
    ("build_note", ["sh", "editorial/build_note.sh"], None),
]
report = {
    "edition": "P1 V1.6, 31 October 2026",
    "started_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Document integrity and selected exact finite identities; no certification of the asymptotic theorems.",
    "runs": [],
}


def save_report():
    (ROOT / "editorial" / "verification_run.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n")


for label, command, output in STEPS:
    print(f"Running {label} ...", flush=True)
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True,
                            text=True, errors="replace", timeout=600)
    log = result.stdout + result.stderr
    (LOGS / f"{label}.txt").write_text(log)
    item = {"step": label, "command": command[1:] if command[0] == sys.executable else command,
            "returncode": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log_sha256": hashlib.sha256(log.encode()).hexdigest()}
    if output and (ROOT / output).exists():
        item["result"] = json.loads((ROOT / output).read_text())
    report["runs"].append(item)
    if result.returncode:
        report["status"] = "failed"
        save_report()
        print(log[-12000:])
        raise SystemExit(f"Failed: {label}; see build/checks/{label}.txt")
    print(f"Passed: {label}.", flush=True)

report["status"] = "passed"
report["completed_utc"] = datetime.now(timezone.utc).isoformat()
save_report()
print("All document and finite checks passed. The asymptotic proofs remain mathematical arguments.")
