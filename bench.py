import os
import sys

from timeit import default_timer as timer

RUNS = int(sys.argv[1])
counter = 0

filename = sys.argv[2]

resultfile = open("timing.txt", "w+")

while (counter < RUNS):
    start = timer() 
    result = os.system("./eff --explicit-subtyping " + filename)
    print "RESULT:: " + result.__str__()
    stop = timer()
    resultfile.write( ((stop-start)*1000.0).__str__() + "\n" )
    counter += 1

resultfile.close()
