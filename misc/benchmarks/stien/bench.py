import subprocess
import sys
from timeit import default_timer as timer

RUNS = int(sys.argv[2])
counter = 0

filename = sys.argv[1]

resultfile_time = open(filename + "_timing.txt" , "w+")
resultfile_nb = open(filename + "_constraints.txt" , "w+")
resultfile_type = open(filename + "_type.txt" , "w+")

for num in range(10, 101, 10):
    print(num.__str__())
    counter = 0
    while counter < RUNS:
        result = subprocess.check_output(["./eff", "--explicit-subtyping", filename + num.__str__() + ".eff"]).__str__()[2:]
        counter += 1

        result_lines = result.split("\\n")
        sum = 0
        typesum = 0

        i = 1
        while not result_lines[i].strip(" ").startswith("TYPESTART"):
            sum += int(result_lines[i].strip(" "))
            i += 1
        while not result_lines[i].strip(" ").startswith("TYPEEND"):
            typesum += result_lines[i].strip(" ").__len__()
            i += 1
        while not result_lines[i].strip(" ").startswith("TIME: "):
            i += 1
        resultfile_time.write((float(result_lines[i][6:])*1000.0).__str__() + "\n")

        if counter == RUNS-1:
            resultfile_nb.write(sum.__str__() + "\n")
            resultfile_type.write(typesum.__str__() + "\n")

resultfile_time.close()
resultfile_nb.close()
resultfile_type.close()
