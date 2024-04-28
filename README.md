Overview of our analysis
   -Given an input program, it builds the points-to graph, finds the matched paths for context-sensitive(CS) 
and field-sensitive edges (FS),
create an simple directed graph (indexing graph) in .gra format with matched paths and valid edges
   -This indexing graph is given as input to grail to check reachability.
(CS or FS reachability to conventional graph reachability)

1) To run the program, provide 2 arguments
     * args[0] - filename to run Eg: build/classes/java/test/TestCS.class
     * args[1] - 0 or 1 (0 to run Context-sensitive analysis or 1 to run Field-sensitive analysis)
    - This generates the graph to be indexed in the .gra format to be used for indexing and 
   a .test file which contains the queries to test
      - Both the files are under the root repository
      - Eg: if pointsTo(a, c) is the query given in the program, the reachability query file will contain an entry
        (15 5 1). Where 15 is the node c, 5 is node a and 1 indicates that this checks if both the nodes are reachable.
      - arguments given in the invoke statement pointsTo(p1,p2) are taken as input queries to check in the program
      - We can also change it to -1 to check if they are not reachable.
    - To run indexing scheme on the graph and check the reachability, execute the program src/executegrail/execGrail.py
      - The console output displays the times taken and the no of queries succeeded.
    - We can also manually verify the paths by traversing in the .gra file
      - start from 15 and traverse along the paths. If 5 is reached, it is reachable, else not reachable
    If reachability is found, then it confirms 15(c) points-to 5(a)
2) To evaluate with the Dacapo benchmark, run the program DacapoRunner under src/main/java/experiments/DacapoRunner.java
   - This generates the indexing graph files under folder dacapoOutput/IndexingGraphCS and
   test queries under folder dacapoQueries
   - Execute the python script under src/executegrail/execGrailForDacapo.py 
   to run the indexing graph files with Grail indexing scheme
   - The results of the evaluation such as Merging SCC time, Index construction time and querying times 
   are written to a csv file - results.csv under the same folder
3) To evaluate with the PointerBench benchmark, run the program PointerBench under src/main/java/experiments/PointerBenchRunner.java
   - This generates the indexing graph files under folder dacapoOutput/IndexingGraphCS and
     test queries under root repository. 
   - Sample query files are already available under PointerBenchQueries
   - Sample graph files are already available under pointerBenchOutput
     - Execute the python script under src/executegrail/execGrailForPointerBench.py
       to run the indexing graph files with Grail indexing scheme
     - The results of the evaluation such as Merging SCC time, Index construction time and querying times and success rates
       are produced in console output
 