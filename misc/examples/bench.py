import subprocess
import sys
from timeit import default_timer as timer

RUNS = 10
counter = 0

filename = sys.argv[1]

resultfile = open("timing.txt", "w+")

while counter < RUNS:
    start = timer()
    result = subprocess.check_output("../eff --explicit-subtyping " + filename)
    print ("RESULT:: " + result.__str__())
    stop = timer()
    resultfile.write((start-stop).__str__() + "\n")
    counter += 1

resultfile.close()
