import os
import subprocess
import sys
import glob
import re
import shutil
import difflib

OUTFILE = "test.log"
Z3TRCFILE = ".z3-trace"
TRCFILE = "test.trc"
Z3CMD = [r"..\..\..\..\build\z3", "-smt2", "fixedpoint.engine=predabst", "-dbg:predabst", "-tr:predabst"]

filter = sys.argv[1:]

def writeHeader(f, filename):
    print >>f, "=" * 80
    print >>f, ">>> Running %s" % filename
    f.flush()

def writeFooter(f, status):
    print >>f, ">>> %s" % status
    f.flush()

with open(OUTFILE, "w") as outfile:
    with open(TRCFILE, "w") as trcfile:
        for inFilename in glob.glob("*.smt2"):
            testname = os.path.splitext(inFilename)[0]
            if filter and testname not in filter:
                continue
            outFilename = testname + ".out"
            if os.path.exists(outFilename):
                expectedOutput = file(outFilename).read()
            else:
                expectedOutput = None
                
            writeHeader(outfile, inFilename)
            writeHeader(trcfile, inFilename)
            try:
                output = subprocess.check_output(Z3CMD + [inFilename], stderr=subprocess.STDOUT)
                if expectedOutput is not None:
                    if expectedOutput.splitlines() == output.splitlines():
                        status = "VALIDATED"
                    else:
                        status = "VALIDATION FAILED\n" + "\n".join(difflib.ndiff(expectedOutput.splitlines(), output.splitlines()))
                else:
                    status = "PASSED"
            except subprocess.CalledProcessError as e:
                output = e.output
                status = "FAILED"
            outfile.write(output)
            with open(Z3TRCFILE, "r") as z3trcfile:
                shutil.copyfileobj(z3trcfile, trcfile)
            writeFooter(outfile, status)
            writeFooter(trcfile, status)
            print "%s: %s" % (inFilename, status)
