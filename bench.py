import subprocess
import sys
from timeit import default_timer as timer

RUNS = int(sys.argv[2])
counter = 0

filename = sys.argv[1]

resultfile = open("dummy_timing_100_runs.txt", "w+")

while counter < RUNS:
    start = timer()
    result = subprocess.check_output(["./eff", "--explicit-subtyping", filename]).__str__()[2:]
    stop = timer()
    resultfile.write(((stop-start)*1000).__str__() + "; ")
    counter += 1

    result_lines = result.split("\\n")
    sum = 0
    i = 0
    while not result_lines[i].strip(" ").startswith("- :"):
        sum += int(result_lines[i].strip(" "))
        i += 1

    resultfile.write(sum.__str__() + "\n")


resultfile.close()