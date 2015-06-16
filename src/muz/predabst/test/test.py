import os
import subprocess
import sys
import glob
import re
import shutil
import difflib
import time

OUTFILE = "test.log"
Z3TRCFILE = ".z3-trace"
TRCFILE = "test.trc"
Z3OPTS = [
    "-smt2",
    "fixedpoint.engine=predabst",
    "fixedpoint.print_answer=true",
    "fixedpoint.print_certificate=true",
    "fixedpoint.print_statistics=true",
    "timeout=300000", # 5 minutes
]

debug = True
use_asserts = True
use_tracing = True
filter = sys.argv[1:]

z3root = os.path.join(os.path.dirname(__file__), r"..\..\..\..")

if debug:
    z3cmd = [os.path.join(z3root, "build", "z3")] + Z3OPTS
    if use_asserts:
        z3cmd.append("-dbg:predabst")
    if use_tracing:
        z3cmd.append("-tr:predabst")
else:
    z3cmd = [os.path.join(z3root, "build-release", "z3")] + Z3OPTS

def writeHeader(f, filename):
    print >>f, "=" * 80
    print >>f, ">>> Running %s" % filename
    f.flush()

def writeFooter(f, msg):
    print >>f, ">>> %s" % msg
    f.flush()

def normspace(s):
    s = re.sub(' +', ' ', s)
    s = re.sub('^ *', '', s)
    s = re.sub(' *$', '', s)
    return s

def compareOutput(expected, actual):
    expectedLines = normspace(' '.join(expected.splitlines()))
    actualLines = normspace(' '.join(actual.splitlines()))
    return expectedLines == actualLines

numPassed = 0
numFailed = 0

PASSED = object()
FAILED = object()

with open(OUTFILE, "w") as outfile:
    with open(TRCFILE, "w") as trcfile:
        for inFilename in glob.glob("*.smt2"):
            testname = os.path.splitext(inFilename)[0]
            if filter and not any(testname.startswith(f) for f in filter):
                continue
            outFilename = testname + ".out"
            if os.path.exists(outFilename):
                expectedOutput = file(outFilename).read()
            else:
                expectedOutput = None
            writeHeader(outfile, inFilename)
            writeHeader(trcfile, inFilename)
            try:
                start = time.time()
                try:
                    output = subprocess.check_output(z3cmd + [inFilename], stderr=subprocess.STDOUT)
                finally:
                    end = time.time()
                    duration = end - start
                if expectedOutput is not None:
                    if compareOutput(expectedOutput, output):
                        status = PASSED
                        msg = "PASSED"
                    else:
                        status = FAILED
                        msg = "FAILED: output not as expected:\n" + "\n".join(difflib.ndiff(expectedOutput.splitlines(), output.splitlines()))
                else:
                    if '-sat-' in testname and 'sat' not in output.splitlines():
                        status = FAILED
                        msg = "FAILED: didn't find 'sat'"
                    elif '-unsat-' in testname and 'unsat' not in output.splitlines():
                        status = FAILED
                        msg = "FAILED: didn't find 'unsat'"
                    elif any('leak' in line for line in output.splitlines()):
                        status = FAILED
                        msg = "FAILED: memory leak"
                    else:
                        status = PASSED
                        msg = "PASSED (but no .out file to compare with)"
            except subprocess.CalledProcessError as e:
                output = e.output
                status = FAILED
                msg = "FAILED: exited with status %d" % e.returncode
            outfile.write(output)
            with open(Z3TRCFILE, "r") as z3trcfile:
                shutil.copyfileobj(z3trcfile, trcfile)
            writeFooter(outfile, msg)
            writeFooter(trcfile, msg)
            print "%s: %s (in %.2f seconds)" % (inFilename, msg, duration)
            if status is PASSED:
               numPassed += 1
            else:
               assert status is FAILED
               numFailed += 1

print
if numFailed:
    print "%d of %d test(s) failed" % (numFailed, numPassed + numFailed)
else:
    print "All %d test(s) passed" % numPassed
