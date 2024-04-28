import subprocess
import os

compile_path = "..\\nativeCpp\\grail\\*.cpp"
compile_args = ["C:\\MinGW\\bin\\g++.exe", compile_path, "-o", "grail"] #change the path to your directory of c++ executable


src_file = "..\\..\\TestCS-CS.gra" #change to the graph file to test
trg_file = "..\\..\\TestCS-CS.test" #change to the path with test queries

std_input = "./grail "+src_file+" -test "+trg_file+" -dim 2"

data,temp = os.pipe()

os.write(temp, bytes(std_input, "utf-8"))

os.close(temp)

#output_file = open("results1.csv", "w")
print("filename, merging time, labelling time, query time, No of success, Total no of queries")

compile_process = subprocess.run(compile_args, stdin=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

#if the compilation is success
if compile_process.returncode == 0:
    subprocess.call(["./grail", src_file,"-test",trg_file,"-dim","2"])

else:
    print("The compilation was failed. Error Message:")
    error = compile_process.stderr.decode()
    print(error)
