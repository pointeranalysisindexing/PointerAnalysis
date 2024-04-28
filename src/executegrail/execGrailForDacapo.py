import subprocess
import os

src_folder = "..\\..\\dacapoOutput\\IndexingGraphCS"
files = os.listdir(src_folder)
print("files::",files)

trg_folder = "..\\..\\dacapoQueries\\Reachable_Queries" #sample queries are already in the folder, change it if needed
compile_path = "..\\nativeCpp\\grail\\*.cpp"
num_of_iterations = 5
i = 0

output_file = open("results.csv", "w")
#output_file.write("merging time, labelling time, query time")

while i < num_of_iterations:
    print("*********************Iteration *********************", i)
    i = i + 1
    for dir in files:
        print("Current folder::", dir)
        src_path = src_folder + "\\" + dir
        for graphFile in os.listdir(src_path):
            src_fileName = graphFile
            src_path = src_path + "\\" + src_fileName
            print("src path::", src_path)

            trg_fileName = src_fileName.lower()
            trg_fileName = trg_fileName.replace(".gra", ".test")
            trg_path = trg_folder + "\\" + trg_fileName
            print("target file::", trg_path)

            compile_args = ["C:\\MinGW\\bin\\g++.exe", compile_path, "-o", "grail"]
            std_input = ("./grail " +
                         src_path +
                         " -test " +
                         #trg_path +
                         " -dim 2")
            data,temp = os.pipe()
            os.write(temp, bytes(std_input, "utf-8"))
            os.close(temp)

            compile_process = subprocess.run(compile_args, stdin=data, stdout= subprocess.PIPE, stderr=subprocess.PIPE)

            #if the compilation is success
            if compile_process.returncode == 0:
                subprocess.call(["./grail",
                                 src_path,
                                 "-test",
                                 trg_path,
                                 "-dim",
                                 "2"], stdout=output_file)
            else:
                print("The compilation was failed. Error Message:")
                error = compile_process.stderr.decode()
                print(error)