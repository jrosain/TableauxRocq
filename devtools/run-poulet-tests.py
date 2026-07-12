from subprocess import PIPE, run
import glob
from pathlib import Path
import os

PATH="../checker/_build/default/bin/main.exe"

def sanitize(s):
    return s.encode('utf-8', errors='ignore').decode(errors='ignore')

def sh(command):
    result = run(command, stdout=PIPE, stderr=PIPE, universal_newlines=True, shell=True, encoding='utf-8')
    return (sanitize(result.stdout), sanitize(result.stderr), result.returncode)

def run_success_tests(dirname):
    failed = []
    for f in glob.glob(f"tests/{dirname}/*.p"):
        args = ""
        if dirname == "inner":
            args = "-skolem inner"
        print(f"POULET {args} {f}")
        _, err, code = sh(f"{PATH} {args} {f}")
        if code != 0:
            failed = failed.append((f, err))
    return failed

def run_failure_tests(dirname):
    failed = []
    for f in glob.glob(f"tests/{dirname}/*.p"):
        print(f"POULET {f} (expect failure)")
        expected = Path(f).with_suffix(".out")
        actual, _, code = sh(f"{PATH} {f}")
        if code != 1:
            failed = failed.append((f, "Should have failed but didn't fail."))
        with open(expected) as e:
            txt = e.read()
            if actual != txt:
                failed.append((f, f"Expected output: \"{txt}\"\nActual output: \"{actual}\""))
    return failed

if not os.path.exists(PATH):
    sh("cd .. && make poulet")

succeed = ["basic", "inner"]
fail    = ["should_fail"]

failed = []
for succeed in succeed:
    failed += run_success_tests(succeed)

wrong_failed = []
for fail in fail:
    wrong_failed += run_failure_tests(fail)

print("\n========================================")
print("                RESULTS                 ")
print("========================================\n")

if len(failed) > 0 or len(wrong_failed) > 0:
    print("\n".join(f"{filename}: {reason}" for (filename, reason) in failed))
    print("\n".join(f"{filename}\n{reason}\n" for (filename, reason) in wrong_failed))
    exit(1)
else:
    print("All tests have been successfully passed.")
    exit(0)
