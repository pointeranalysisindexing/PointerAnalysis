package indexing;

import com.ibm.wala.classLoader.*;
import com.ibm.wala.core.util.config.AnalysisScopeReader;
import com.ibm.wala.core.util.strings.Atom;
import com.ibm.wala.core.viz.PDFViewUtil;
import com.ibm.wala.demandpa.flowgraph.*;
import com.ibm.wala.demandpa.util.ArrayContents;
import com.ibm.wala.demandpa.util.MemoryAccessMap;
import com.ibm.wala.demandpa.util.SimpleMemoryAccessMap;
import com.ibm.wala.examples.drivers.PDFCallGraph;
import com.ibm.wala.examples.drivers.PDFTypeHierarchy;
import com.ibm.wala.examples.properties.WalaExamplesProperties;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.cha.CHACallGraph;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.*;
import com.ibm.wala.ipa.callgraph.propagation.cfa.CallerSiteContext;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.properties.WalaProperties;
import com.ibm.wala.shrike.shrikeBT.*;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.types.annotations.Annotation;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.collections.*;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.viz.DotUtil;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class PointerFlowGraph extends AbstractDemandFlowGraph implements IFlowGraph {
    private Map<PointerKey, Set<PointerKey>> inverseEdges = HashMapFactory.make();
    private Map<Object, Set<Object>> returnEdgesWithPrime = new HashMap<>();
    private Map<Object, Set<Object>> matchedPathsInverseEdges = HashMapFactory.make();
    final private String METHOD_NAME_CHECK ="pointsTo";//To be changed if given a different invoke statement for querying

    //If a single variable is given to query like pointsToQuery(b), then we get put them in a set
    //and compare it with all root nodes to find the one it points-to - for PointerBench microbenchmark
    private Set<Integer> pts_to_queries = new HashSet<>();

    //Given two variables to check if they points-to each other
    //We normal check our analysis this way
    //Eg: pointsToQuery(a, b) -->
    private static Map<Integer, Integer> pts_queries = new HashMap<>();
    private static int cs_matchedEdges_Count = 0;

    private PointerFlowGraph(CallGraph cg, HeapModel heapModel, MemoryAccessMap mam, IClassHierarchy cha) {
        super(cg, heapModel, mam, cha);
    }

    /**
     * To run the program, provide 2 arguments
     * args[0] - filename to run Eg: build/classes/java/test/TestCS.class
     * args[1] - 0 to run Context-sensitive analysis or 1 to run Field-sensitive analysis
     * */
    public static void main(String[] args) throws IOException, WalaException, CancelException {

        // 1. BUILDING THE CALL GRAPH FILE FROM INPUT FILE
        String fileName = "", outputFilePath = "";
        boolean viz = false; //to generate a pdf view of the points-to graph
        String classPath = args[0];
        int option = Integer.parseInt(args[1]);

        //write randomly generated reachability and un-reachability queries to the file for Grail - only added for Dacapo benchmarks
        //sample queries are already in the folder, uncomment to generate new queries
        //String queryPath = "dacapoQueries\\";

        if (args.length == 2 ) {
            fileName = classPath.substring(classPath.lastIndexOf('\\')+1, classPath.lastIndexOf('.'));
            fileName = fileName.substring(fileName.lastIndexOf('/')+1);
            outputFilePath = fileName;
        } else {
            classPath = args[0] + "\\" + args[2] + ".jar";
            fileName = args[2];
            //fileName = fileName.replace(".jar", "");
            outputFilePath = args[3] + "\\" + fileName;
        }
        System.out.println("classpath::"+classPath);
        System.out.println("fileName::"+fileName);
        System.out.println("outputpath::"+outputFilePath);

        String exclusionFile = "src\\main\\resources\\Java60RegressionExclusions.txt";
        // Construct the AnalysisScope from the class path
        AnalysisScope scope = AnalysisScopeReader.instance.makeJavaBinaryAnalysisScope(classPath, new File(exclusionFile));

        // We need a baseline call graph.  Here we use a CHACallGraph based on a ClassHierarchy.
        ClassHierarchy cha = ClassHierarchyFactory.make(scope);
        CHACallGraph chaCG = new CHACallGraph(cha);
        chaCG.init(Util.makeMainEntrypoints(cha));

        //We also need a heap model to create InstanceKeys for allocation sites, etc.
        //Here we use a 0-1 CFA builder, which will give a heap abstraction similar to
        //context-insensitive Andersen's analysis
        AnalysisOptions options = new AnalysisOptions();
        IAnalysisCacheView cache = new AnalysisCacheImpl();
        HeapModel heapModel = Util.makeZeroOneCFABuilder(Language.JAVA, options, cache, cha); //1 - CS analysis
        //HeapModel heapModel = Util.makeNCFABuilder(1, options, cache, cha);

        // The MemoryAccessMap helps the demand analysis find matching field reads and writes
        MemoryAccessMap mam = new SimpleMemoryAccessMap(chaCG, heapModel, false); //AS - use??
        System.out.println(CallGraphStats.getStats(chaCG));

        //2. BUILDING THE POINTS-TO GRAPH WITH EDGES
        long start = System.currentTimeMillis();
        PointerFlowGraph fGraph = new PointerFlowGraph(chaCG, heapModel, mam, cha);
        FlowStatementVisitor visitor;

        //2.1 for every method in the call graph, iterate through all instructions and visit them through flow graph
        for (CGNode node : chaCG) {
            if (!node.getMethod().getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application)) {
                continue;
            }
            if (fGraph.isApplicationInit(node) || fGraph.shouldIgnore(node)) {
                continue;
            }
            IR ir = node.getIR();
            if (ir == null) continue;

            visitor = fGraph.makeVisitor(node);

            //Visiting instructions by traversing through blocks
            for (Iterator<ISSABasicBlock> it = ir.getBlocks(); it.hasNext(); ) {
                ISSABasicBlock block = it.next();
                visitor.setBasicBlock(block);

                //for every instruction in the block, visit through flow graph
                for (SSAInstruction ins : block) {
                    ins.visit(visitor);
                }
            }
        }
        System.out.println("Visited all instructions..");
        //System.out.println("FGraph:::" + fGraph);
        //System.out.println("Inverse edges::"+fGraph.inverseEdges);

        //2.2 memory allocation for adjacency list
        Map<Integer, Set<Integer>> adjacencyList = new HashMap<>();

        //2.3 For all the methods in the call graph - add edges from actual parameter to formal parameter and return value to the call site
        int contextSummaryCount = 0;
        for (CGNode node : chaCG) {
            if (!node.getMethod().getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application)) {
                continue;
            }
            if (fGraph.isApplicationInit(node)) continue;
            if (node.getIR() == null) continue;
            if (fGraph.shouldIgnore(node)) continue;
            contextSummaryCount += fGraph.addNodesForParametersAndReturns(node, node.getIR(), chaCG, adjacencyList);
        }
        //System.out.println("FGraph::: \n" + fGraph + "\n");
        //System.out.println("Adjacency list::"+adjacencyList);

        long fGraphEnd = System.currentTimeMillis();
        System.out.println("Points-to Graph building time::"+(fGraphEnd-start) +"ms");
        System.out.println("Number of nodes::"+fGraph.getNumberOfNodes());

        //2.4 since this is like a spanning tree forest, get all root nodes - for adjacency list
        Set<Object> rootNodes = HashSetFactory.make();
        for (Object obj : Iterator2Iterable.make(fGraph.iterator())) {
            if (fGraph.getPredNodeCount(obj) <= 0) {
                rootNodes.add(obj);
            }
        }
        System.out.println("Found root nodes!!"+rootNodes.size());
        //System.out.println("\n Root nodes:"+rootNodes);
        //leaf nodes are object instantiations and set/get ends

        /*
        //Since SPDS analysis takes an invoke statement and trigger the backward query for its parameter to compute the points-to,
        //we write the method names to a file to give it as input to the analysis
        Set<Object> leafNodes = HashSetFactory.make();
        Set<Integer> src_list = new HashSet<>();
        Set<String> method_list = new HashSet<>();
        for (Object obj : Iterator2Iterable.make(fGraph.iterator())) {
            if (fGraph.getSuccNodeCount(obj) <= 0) {
                String methodName = obj.toString();
                if (methodName.split(",").length > 2) {
                    methodName = methodName.split(",")[2];
                    if (!methodName.contains("("))
                        continue;
                    methodName = methodName.substring(1, methodName.indexOf('('));
                    //System.out.println("method Name::" + methodName);
                    method_list.add(methodName);
                }
            }
        }
        //fGraph.writeMethodNamesToFile(method_list, outputFilePath+"methods.txt");
        */

        /*Write queries from root node to leaf node
        Set<Object> leafNodes = HashSetFactory.make();
        Set<Integer> src_list = new HashSet<>();
        for (Object obj : Iterator2Iterable.make(fGraph.iterator())) {
            if (fGraph.getSuccNodeCount(obj) <= 0) {
                leafNodes.add(obj);
                src_list.add(fGraph.getNumber(obj));
                //System.out.println("leaf::"+obj+"at "+fGraph.getNumber(obj));
            }
            System.out.println("Found leaf nodes!!" + leafNodes.size());
        }
        //generate test files for Grail with the root nodes and leaf nodes as the queries
        fGraph.writeTestFile(rootNodes, outputFilePath+"-CS.test", src_list , 0);
        */

        int returnPrimeEdgesCount = 0;

        switch (option) {
            case 0: {
                //3. PREPARE ADJACENCY LIST FOR CS - input for grail
                System.out.println("\n CONTEXT SENSITIVE##########################");
                long startCS = System.currentTimeMillis();

                //Adding remaining nodes in adjacency list
                for (int i=0; i < fGraph.getNumberOfNodes() ; i++) {
                    if (!adjacencyList.containsKey(i)) {
                        adjacencyList.put(i, new HashSet<>());
                    }
                    //System.out.println("Node::"+fGraph.getNode(i)+" at i: "+i);
                }
                System.out.println("Adjacency list build completed!!");
                //System.out.println("Graph\n::"+fGraph);

                //set of root and child combination visited so that we don't have to revisit for next rootNode
                Set<Pair<Object,Object>> visitedPair = new HashSet<>();

                //System.out.println("returnEdgesWithPrime::"+fGraph.returnEdgesWithPrime);
                for (Object key : fGraph.returnEdgesWithPrime.keySet()) {
                    Set<Object> visited = new HashSet<>();
                    visited.add(key);
                    Set<Object> leafs = fGraph.returnEdgesWithPrime.get(key);
                    visited.addAll(leafs);
                    //traverse the predecessors of this node up to root node or alloc node(not needed)
                    Set<Object> roots = fGraph.fetchReturnOrRootNode(key, visited, rootNodes, visitedPair);
                    for (Object leaf : leafs) {
                        for (Object root : roots) {
                            fGraph.checkAndAddAdjacencyList(root, leaf, adjacencyList);
                            returnPrimeEdgesCount++;
                            visitedPair.add(Pair.make(root, leaf));
                        }
                        if (roots.isEmpty()) {
                            fGraph.checkAndAddAdjacencyList(key, leaf, adjacencyList);
                            returnPrimeEdgesCount++;
                            visitedPair.add(Pair.make(key, leaf));
                        }
                    }
                }
                fGraph.returnEdgesWithPrime.clear();
                System.out.println("Return Edges added to adjacency list!!");

                Map<Pair<Object, CallerSiteContext>, Object> visitedParamNodes = new HashMap<>();//each (return, this) has unique label
                for (Object root : rootNodes) {
                    fGraph.addToIndexingGraphForCS(root, adjacencyList, visitedPair, visitedParamNodes);
                }
                System.out.println("Added Points-to graph to Adjacency list!!");

                //3.4 Write the adjacency list to output file
                writeAdjacencyListToFile(adjacencyList, outputFilePath+"-CS.gra");
                System.out.println("Adjacency list written to the file!!");

                //To write a query file, which takes "pointsTo(d)" as argument and checks it with all root nodes to find reachability
                //If grail indexing schemes indicates if the query is success, then they belong to points-to set
                //useful in cases, where you have a single variable and want to compute the points-to set
                //fGraph.writeTestFile(rootNodes,outputFilePath+"-cs.test",fGraph.pts_to_queries, 1);

                long endCS = System.currentTimeMillis();
                System.out.println("Time taken to prepare CS Input adjacency list::"+(endCS-startCS)+ " ms");
                adjacencyList.clear();
                System.out.println("No of context summary edges::"+cs_matchedEdges_Count);
                System.out.println("No of Return Prime edges::"+returnPrimeEdgesCount);
                //System.out.println("No of Matched Edges::"+cs_summaryEdges_Count);
                System.out.println("No of edges::"+visitedPair.size());

                //write randomly generated reachability and non-reachability queries to the file for Grail - only for Dacapo for macrobenchmark
                /*
                fGraph.generateQueries(1000, queryPath+ "Reachable_Queries\\"+ fileName +"-cs.test", 1);
                fGraph.generateQueries(1000, queryPath + "UnReachable_Queries\\"+fileName+"-cs.test", 0);
                */
                //write the reachability query from the input program to a file
                writeQueryTestFile(fileName+"-cs.test", 1);
                break;
            }
            case 1: {
                //4. PREPARE FIELD SENSITIVE ADJACENCY LIST - input for grail
                System.out.println("\n FIELD SENSITIVE##########################");
                long startFS = System.currentTimeMillis();

                Map<Object, Set<Object>> fieldSummaryEdges = new HashMap<>();

                Map<Integer, Set<Integer>> adjacencyListFS = new HashMap<>();
                for (int i=0; i < fGraph.getNumberOfNodes() ; i++) {
                    adjacencyListFS.put(i, new HashSet<>());
                    //System.out.println(fGraph.getNode(i)+" at i:"+i);
                }
                System.out.println("Allocating memory for FS Adjacency list!!");

                long FS_Adjlist_Start = System.currentTimeMillis();
                Set<Pair<Object,Object>> visitedPair = new HashSet<>();
                for (Object root: rootNodes) {
                    fGraph.addToIndexingGraphForFS(root, adjacencyListFS, fieldSummaryEdges, visitedPair);
                }
                long FS_Adjlist_End = System.currentTimeMillis();
                int noOfEdgesFS = visitedPair.size();
                visitedPair.clear();
                System.out.println("Adjacency list for Field Sensitive analysis build completed!!");
                System.out.println("Time taken::"+(FS_Adjlist_End-FS_Adjlist_Start)+" ms");

                //4.4 write the adjacency list to output file
                writeAdjacencyListToFile(adjacencyListFS, outputFilePath+"-FS.gra");
                System.out.println("Adjacency list written to the file");

                long endFS = System.currentTimeMillis();
                System.out.println("Total Time taken to build Field sensitive Input adjacency list::"+(endFS-startFS)+ " ms");
                adjacencyListFS.clear();

                //System.out.println("No of Matched Edges::"+matchedEdgesCount);
                //System.out.println("No of field summary edges::"+fieldSummaryEdges.size());
                //System.out.println("No of context summary edges::"+contextSummaryCount);
                System.out.println("No of Edges::"+noOfEdgesFS);

                //write randomly generated reachability and un-reachability queries to the file for Grail - only for Dacapo macrobenchmark
                /*
                fGraph.generateQueries(1000, queryPath+ "Reachable_Queries\\"+ fileName +"-fs.test", 1);
                fGraph.generateQueries(1000, queryPath + "UnReachable_Queries\\"+fileName+"-fs.test", 0);
                */

                //write the reachability query from the input program to a file
                writeQueryTestFile(fileName+"-fs.test", 1);
                break;
            }
        }
        long end = System.currentTimeMillis();

        //STATISTICS
        System.out.println("\n Pointer graph statistics#########");
        System.out.println("Number of nodes::"+fGraph.getNumberOfNodes());
        System.out.println("Total time taken::"+(end-start)+ " ms");
        System.out.println("\n");

        //PDF views of the graph
        if (viz)
            fGraph.visualizeGraph(fileName, chaCG);
    }
    /* *
     * visualization of the graphs*
     * */
    private void visualizeGraph(String fileName, CallGraph chaCG) {
        try {
            Properties wp = WalaProperties.loadProperties();
            wp.putAll(WalaExamplesProperties.loadProperties());
            String psFile =
                    wp.getProperty(WalaProperties.OUTPUT_DIR) + File.separatorChar + fileName + ".pdf";
            String dotFile =
                    wp.getProperty(WalaProperties.OUTPUT_DIR)
                            + File.separatorChar
                            + PDFTypeHierarchy.DOT_FILE;
            String dotExe = wp.getProperty(WalaExamplesProperties.DOT_EXE);
            String gvExe = wp.getProperty(WalaExamplesProperties.PDFVIEW_EXE);

            //To see the PDF view pointer flow graph
            DotUtil.dotify(this, null, dotFile, psFile, dotExe);
            PDFViewUtil.launchPDFView(psFile, gvExe);

            //To see the pdf view of the call graph
            Graph<CGNode> g = PDFCallGraph.pruneForAppLoader(chaCG);
            String callgraphFile =
                    wp.getProperty(WalaProperties.OUTPUT_DIR) + File.separatorChar + fileName+ "-callgraphFile";
            //DotUtil.dotify(g, null, dotFile, callgraphFile, dotExe);
            //PDFViewUtil.launchPDFView(callgraphFile, gvExe);
        } catch (WalaException e) {
            System.out.println("Exception thrown while visualization the graph using dot!!");
        }
    }

    protected int addNodesForParametersAndReturns(CGNode caller, IR ir, CallGraph cg, Map<Integer, Set<Integer>> adjacencyList) {
        int summaryCount = 0;
        //get the possible callsites for this node - compare the node with all other nodes
        for (CGNode callee : cg) {
            if (shouldIgnore(callee)) { continue;}
            //TODO added this to remove iteration of all other library methods like - equals, hashcode() from javax, javafx
            if (!isApplicationNode(callee)) {continue;}
            for (CallSiteReference site : Iterator2Iterable.make(cg.getPossibleSites(caller, callee))) {
                SSAAbstractInvokeInstruction[] callInstructions = ir.getCallInstructionIndices(site) == null
                        ? new SSAAbstractInvokeInstruction[0]
                        : caller.getIR().getCalls(site);
                for (SSAAbstractInvokeInstruction callInstr : callInstructions) {
                    //create the context for the call and return sites
                    CallerSiteContext context = new CallerSiteContext(caller, site);
                    //If the instruction has parameters and return values, then make a summary edge
                    boolean hasReturn = false;
                    if (callInstr.getNumberOfPositionalParameters() > 0 && callInstr.hasDef()) {
                        hasReturn = true;
                        //System.out.println("param::"+callInstr.getNumberOfPositionalParameters());
                        buildParamEdges(caller, callInstr, context, callee, hasReturn, adjacencyList);

                        buildReturnEdges(caller, callInstr, context, callee);
                    }
                    //if the instruction has only parameters, then connect formal parameters with actual parameters
                    else if (callInstr.getNumberOfPositionalParameters() > 0) {
                        buildParamEdges(caller, callInstr, context, callee, hasReturn, adjacencyList); //param edges adj list
                        //since more open parenthesis are acceptable, add them to the adjacency list
                        //edge from formal parameter to the actual parameter
                    }
                    //if the instruction has only return value defined by a variable, then connect the return value back to the pointer key at call site
                    else if (callInstr.hasDef()) {
                        //if inverse edges, make return edge with this parameter
                        //if this with no inverse edges, make paramBar and don't call return
                        buildReturnEdges(caller, callInstr, context, callee);
                    }
                }
            }
        }
        return summaryCount;
    }

    /*
    * make parameter edges for a method
    *
    * */
    private Set<PointerKey> buildParamEdges(CGNode caller, SSAAbstractInvokeInstruction callInstr, CallerSiteContext context, CGNode callee, boolean hasReturn, Map<Integer, Set<Integer>> adjacencyList) {
        Set<PointerKey> paramPointerKeys = new HashSet<>();
        String methodName = callee.getMethod().getName().toString();
        int noOfParameters = callee.getMethod().getNumberOfParameters();

        //if (!callInstr.isSpecial()) {
        //for every parameter of the call node

        //for (int parameter : Iterator2Iterable.make(new PointerParamValueNumIterator(callee))) {
        for (int parameter = 1; parameter <= noOfParameters; parameter++) {
            //create the node for formal parameter
            PointerKey formalPk = heapModel.getPointerKeyForLocal(callee, parameter);
            addNode(formalPk);

            //get the corresponding actual parameter for the formal parameter pointer key
            LocalPointerKey formalLocalPK = (LocalPointerKey) formalPk;
            PointerKey actualPk = heapModel.getPointerKeyForLocal(caller, callInstr.getUse(formalLocalPK.getValueNumber() - 1));
            addNode(actualPk);

            //add the edge to connect formal parameter and actual parameter
            addEdge(actualPk, formalPk, ParamEdge.make(context));

            //If the instruction is not static, then the first parameter is a 'this' parameter and if it has no return value, add an inverse edge
            //Eg: x -> this(set)
            //if (!callInstr.isStatic() && parameter == 1) {
            //if this had a field write to it
            if (inverseEdges.containsKey(formalPk)) {
                //then add the inverse or prime edge
                addEdge(formalPk, actualPk, ParamBarEdge.make(context));
                //add this to matched paths list
                matchedPathsInverseEdges.computeIfAbsent(formalPk, k -> new HashSet<>());
                matchedPathsInverseEdges.get(formalPk).add(actualPk);
                //System.out.println("MatchedPathsInverseEdges::"+matchedPathsInverseEdges);
                continue;
            }
            paramPointerKeys.add(actualPk);
        }
        //To prepare queries
        if (methodName.contains(METHOD_NAME_CHECK)) {
            //Then we know there are two parameters
            //if the method is points-to query or mayAlias or any, take the parameters to prepare query
            //pointsTo(a, b), we take a & b and add them to the query file to give it to indexing scheme
            LocalPointerKey formalPK1 = (LocalPointerKey) heapModel.getPointerKeyForLocal(callee, 1);
            PointerKey param1 = heapModel.getPointerKeyForLocal(caller, callInstr.getUse(formalPK1.getValueNumber() - 1));
            int queryNode1 = this.getNumber(param1);
            //add them to a list
            System.out.println("\n Query arg::" + queryNode1);

            if (noOfParameters > 1) {
                //LocalPointerKey formalLocalPK = (LocalPointerKey) param1;
                //PointerKey param2 = heapModel.getPointerKeyForLocal(caller, callInstr.getUse(formalLocalPK.getValueNumber() - 1));

                LocalPointerKey formalPK2 = (LocalPointerKey) heapModel.getPointerKeyForLocal(callee, 2);
                PointerKey param2 = heapModel.getPointerKeyForLocal(caller, callInstr.getUse(formalPK2.getValueNumber() - 1));
                int queryNode2 = this.getNumber(param2);
                System.out.println("\n Query arg 2::" + queryNode2);
                pts_queries.put(queryNode1, queryNode2);
            } else {
                //make test file with queryNodes --- Pointerbench Analysis
                pts_to_queries.add(queryNode1);
            }
        }
        return paramPointerKeys;
    }

    /*
    * make return edges for the functions
    * also adds the return match edges for the return edge with no parameter
    * */
    private PointerKey buildReturnEdges(CGNode caller, SSAAbstractInvokeInstruction callInstr, CallerSiteContext context, CGNode callee) {
        PointerKey callerSiteKey = heapModel.getPointerKeyForLocal(caller, callInstr.getDef());
        addNode(callerSiteKey);
        LocalPointerKey pk = (LocalPointerKey) callerSiteKey;
        boolean isExceptional = pk.getValueNumber() == callInstr.getException();
        //nodes for the exception and check for the return exception value
        PointerKey returnKey =
                isExceptional
                        ? heapModel.getPointerKeyForExceptionalReturnValue(callee)
                        : heapModel.getPointerKeyForReturnValue(callee);
        //PointerKey returnKey = heapModel.getPointerKeyForReturnValue(callee);
        addNode(returnKey);
        final ReturnEdge returnLabel = ReturnEdge.make(context);
        addEdge(returnKey, callerSiteKey, returnLabel);

        //if the call instruction is static and has no parameters (no this and no other params)
        if (callInstr.isStatic() && callInstr.getNumberOfPositionalParameters() == 0) {
            //Eg: A z = foo(), ret() -> z
            addEdge(callerSiteKey, returnKey, new ReturnBarEdge(context));
            //storing return edges with prime, so it can be used to make matched path later
            returnEdgesWithPrime.computeIfAbsent(returnKey, k -> new HashSet<>());
            returnEdgesWithPrime.get(returnKey).add(callerSiteKey);
        }
        return callerSiteKey;
    }

    /**
     * usage: traverse the points-to graph to prepare an adjacency list for the Context-Sensitive analysis
     * */
    private void addToIndexingGraphForCS(Object rootNode, Map<Integer, Set<Integer>> adjacencyList, Set<Pair<Object,Object>> visitedPair, Map<Pair<Object, CallerSiteContext>, Object> visitedParamNodes) {
        Stack<Pair<Object, Object>> worklist = new Stack<>();
        this.getSuccNodes(rootNode).forEachRemaining(node -> {
            worklist.push(Pair.make(rootNode, node));
        });
        Set<Object> visited = new HashSet<>();//inside the same root Node - to avoid cycles
        Set<String> paramLabelSet = new HashSet<>();
        boolean paramsFound = false;
        while (!worklist.empty()) {
            Pair<Object, Object> objectPair = worklist.pop();
            Object root = objectPair.fst;
            Object child = objectPair.snd;
            if (visitedPair.contains(objectPair)) //to avoid traversing same root-child pair in diff root node
                continue;
            visitedPair.add(objectPair);
            //visited.add(child);
            //more than one edge between a root and a child
            for (IFlowLabel label : this.getEdgeLabels(root, child)) {
                if (isParamEdge(label)) {
                    //if this param node is already visited for this context, retrieve it from map, else find the matched path
                    CallerSiteContext context = ((ParamEdge)label).context;
                    Pair<Object, CallerSiteContext> childLabelPair = Pair.make(child, context);
                    if (visitedParamNodes.containsKey(childLabelPair)) {
                        Object ret = visitedParamNodes.get(childLabelPair);//context is unique
                        //if the child for this param exists, traverse
                        if (ret != null) {
                            checkAndAddAdjacencyList(root, ret, adjacencyList);
                            cs_matchedEdges_Count++;
                            //addEdge(ret, ret, MatchEdge.make(context));
                            this.getSuccNodes(ret).forEachRemaining(node -> {
                                if (!visitedPair.contains(Pair.make(ret, node))) {
                                    worklist.push(Pair.make(ret, node));
                                }
                            });
                        }
                        //visited, still no child - unbalanced open parenthesis
                        continue;
                    }
                    paramsFound = true;
                    paramLabelSet.add(label.toString()); continue;
                }
                if (isParamBarEdge(label)) {continue;}
                if (isReturnBarEdge(label)) {
                    //unbalanced closed parenthesis acceptable
                    continue;
                }
                if (isAssignEdge(label) || isNewEdge(label) || isGetFieldEdge(label) || isPutFieldEdge(label) || isReturnEdge(label)) {
                    checkAndAddAdjacencyList(root, child, adjacencyList);
                    this.getSuccNodes(child).forEachRemaining(node -> {
                        if (!visitedPair.contains(Pair.make(child, node))) {
                            worklist.push(Pair.make(child, node));}
                    });
                }
            }
            //between a root and a child, there could be more param labels a --(18(21--> p, so iterate all params first then find matched edge
            if (paramsFound) {
                paramsFound = false;
                if (this.getSuccNodeCount(child) > 0) {
                    //find return or prime
                    Set<Object> returnNodes = findMatchEdge(root, child, paramLabelSet, visitedParamNodes, adjacencyList, visitedPair);
                    //traverse child
                    for (Object returnNode : returnNodes) {
                        //pass the visited here and add a check
                        this.getSuccNodes(returnNode).forEachRemaining(node -> {
                            if (!visitedPair.contains(Pair.make(returnNode, node))) {
                                worklist.push(Pair.make(returnNode, node));
                            }
                        });
                    }
                }
                else {
                    //only one unbalanced open params, (18 , no more followups, so add it to the list
                    checkAndAddAdjacencyList(root, child, adjacencyList);
                }
                // if no match edge, then it's unbalanced open parenthesis, so add it to the list
            }
        }
        //System.out.println("finished adding adjacency list to rootNode::"+rootNode);
    }
    /**
     * find the matched paths for the parameter node (i - either return or returnBar
     **/
    private Set<Object> findMatchEdge(Object rootNode, Object paramNode, Set<String> initialParamSet, Map<Pair<Object, CallerSiteContext>, Object> visitedParamNodes,
                                      Map<Integer, Set<Integer>> adjacencyList, Set<Pair<Object,Object>> visitedPair) {
        //when the node has two children and one of them got the required prime edge
        //then wait for the node to finish both the child and then move through the next child
        //should have either paramPrime edge or a return edge. if either of those is found, then quit it and move on to the next param node as the starting and do the loop again
        //this should run until a return or paramBar edge is found

        Stack<Pair<Object,Object>> worklist = new Stack<>();
        this.getSuccNodes(paramNode).forEachRemaining(node -> {
            if (!visitedPair.contains(Pair.make(paramNode, node))) {
                worklist.push(Pair.make(paramNode, node));
            }
        });
        Set<Object> visited = new HashSet<>(); //to avoid traversing loops
        Set<Object> returnNodes = new HashSet<>();
        Set<Object> leafNodes = new HashSet<>();
        while (!worklist.isEmpty()) {
            Pair<Object, Object> objectPair = worklist.pop();
            Object root = objectPair.fst;
            Object child = objectPair.snd;
            visitedPair.add(objectPair);
            if (visited.contains(child))
                continue;
            visited.add(child);
            Stack<IFlowLabel> paramLabelStack = new Stack<>();
            for (IFlowLabel label : this.getEdgeLabels(root, child)) {
                if (isParamBarEdge(label) || isReturnEdge(label)) {
                    //the last added paramEdge should match with return or prime edge, else mismatch
                    //the last added edge could also be a set a --(18(21--> p
                    CallerSiteContext targetContext = isParamBarEdge(label) ? ((ParamBarEdge) label).context : ((ReturnEdge) label).context;
                    visitedParamNodes.put(Pair.make(paramNode, targetContext), child);

                    //if stack empty, check the originalParam
                    if (paramLabelStack.isEmpty()) {
                        IFlowLabel expectedParamLabel = ParamEdge.make(targetContext);
                        if (initialParamSet.contains(expectedParamLabel.toString())) { //make the param edge with context
                            checkAndAddAdjacencyList(rootNode, child, adjacencyList); //a--(35--> --|35-->x
                            //addEdge(rootNode, child, MatchEdge.make(targetContext));
                            cs_matchedEdges_Count++;
                        } //else mismatch
                        returnNodes.add(child); //adding this, so that we can skip the traversal of these nodes a--(35-->p-- --|)41-->y, --|)35-->x
                    } else {
                        //if more params were added since the first param - matching it with first return
                        IFlowLabel paramEdge = paramLabelStack.pop();
                        CallerSiteContext paramContext = ((ParamEdge) paramEdge).context;
                        if (paramContext == targetContext) {
                            checkAndAddAdjacencyList(rootNode, child, adjacencyList);
                            //addEdge(rootNode, child, MatchEdge.make(targetContext));
                            cs_matchedEdges_Count++;
                        } //else mismatch, but still have to loop other labels
                        returnNodes.add(child); //match or mismatch, we still have to iterate from the last visited return/paramBar child
                    }
                    continue;
                }
                if (isParamEdge(label)) { //more open parenthesis acceptable
                    //use stack because the return/prime edge should match the last open parenthesis encountered
                    paramLabelStack.push(label); // (14
                    //checkAndAddAdjacencyList(rootNode, child, adjacencyList);

                }
                if (isReturnBarEdge(label)) { //already added to the adjacency list
                    continue;
                }
                if (this.getSuccNodeCount(child) > 0) {
                    //new, assign, putField, getField
                    this.getSuccNodes(child).forEachRemaining(node -> {
                        if (!visitedPair.contains(Pair.make(child, node))) {
                            worklist.push(Pair.make(child, node));
                        }
                    });
                } else {
                    checkAndAddAdjacencyList(rootNode, child, adjacencyList);
                    leafNodes.add(child);
                }
            }
        }
        //return the last traversed child, when its unbalanced open parenthesis or no more child to traverse
       /* if (returnNodes.isEmpty()) {
            //add to adjacency list
            returnNodes.add(child);
            //or when its unbalanced as soon as second param encountered, add the node from first parameter to second parameter
        }*/
        //only stops when a return/paramBar encountered or no more child to traverse
        if (!returnNodes.isEmpty())
            return returnNodes;
        else
            return leafNodes;
    }

    private void checkAndAddAdjacencyList(Object root, Object child, Map<Integer, Set<Integer>> adjacencyList) {
        int src_index = this.getNumber(root);
        int trg_index = this.getNumber(child);
        adjacencyList.computeIfAbsent(trg_index, k -> new HashSet<>());
        adjacencyList.get(trg_index).add(src_index);
    }

    private Set<Object> getSummaryFS(Object rootNode, Object fieldNode, GetFieldLabel getFieldLabel, Map<Integer, Set<Integer>> adjacencyListFS,  Set<Pair<Object,Object>> visitedPair
                                    , Map<Pair<Object, IFlowLabel>, Set<Object>> visitedFieldNodes) {
        Set<Object> returnNodes = new HashSet<>();
        Stack<Pair<Object,Object>> workList = new Stack<>();
        this.getSuccNodes(fieldNode).forEachRemaining(child -> {
            if (!visitedPair.contains(Pair.make(fieldNode, child))) {
                workList.push(Pair.make(fieldNode, child));
            }
        });
        Stack<PutFieldLabel> stack = new Stack<>();
        Set<Object> visited = new HashSet<>();
        while (!workList.isEmpty()) {
            Pair<Object,Object> objectPair = workList.pop();
            Object root = objectPair.fst;
            Object child = objectPair.snd;
            visitedPair.add(objectPair);
            if (visited.contains(child))
                continue;
            visited.add(child);
            for (IFlowLabel currLabel : this.getEdgeLabels(root, child)) {
                if (isGetFieldEdge(currLabel)) {
                    if (stack.isEmpty()) {
                        //should be the load for the last visited field store
                        if (getFieldLabel.equals(currLabel)) {//[f]f
                            checkAndAddAdjacencyList(rootNode, child, adjacencyListFS);
                            Pair<Object, IFlowLabel> childWithLabel = Pair.make(fieldNode, currLabel);
                            visitedFieldNodes.computeIfAbsent(childWithLabel, k -> new HashSet<>());
                            visitedFieldNodes.get(childWithLabel).add(child);
                            //fs_summary_count++;
                        }//mismatch [f ]g - no iteration, add it to the
                        returnNodes.add(child);
                    } else {
                        PutFieldLabel fieldEdge = stack.pop();
                        GetFieldLabel stackLabel = GetFieldLabel.make(fieldEdge.getField());
                        if (stackLabel.equals(currLabel)) { //[f [g ]g
                            //fs_summary_count++;
                            //continue iterating
                            this.getSuccNodes(child).forEachRemaining(node -> {
                                if (!visitedPair.contains(Pair.make(child, node))) {
                                    workList.push(Pair.make(child, node));
                                }
                            });
                        } else { //[f [g ]f
                            //mismatch - stop iterating and add this to the return nodes
                            returnNodes.add(child);
                        }
                    }
                    continue;
                }
                if (isPutFieldEdge(currLabel)) {
                    stack.push((PutFieldLabel)currLabel);
                    continue;
                }
                if (isNewEdge(currLabel)) {checkAndAddAdjacencyList(root, child, adjacencyListFS);}
                //if (this.getSuccNodeCount(child) > 0) {
                this.getSuccNodes(child).forEachRemaining(node -> {
                    if (!visitedPair.contains(Pair.make(child, node))) {
                        workList.push(Pair.make(child, node));
                    }
                });
                /*} else { //adding also the leaf node, if no match found???
                    checkAndAddAdjacencyList(rootNode, child, adjacencyList);
                    returnNodes.add(child);
                }*/
            }
        }
        return returnNodes;
    }
    /**
     * usage: traverse the points-to graph to prepare an adjacency list for the Field-Sensitive analysis
     * */
    private void addToIndexingGraphForFS(Object rootNode, Map<Integer, Set<Integer>> adjacencyListFS, Map<Object, Set<Object>> fieldSummaryEdges, Set<Pair<Object,Object>> visitedPair) {
        Stack<Pair<Object,Object>> workList = new Stack<>();
        this.getSuccNodes(rootNode).forEachRemaining(node -> {
            workList.push(Pair.make(rootNode, node));
        });
        int fs_summary_count = 0;
        Map<Pair<Object, IFlowLabel>, Set<Object>> visitedFieldNodes = new HashMap<>();//stores the field summary for a child, label pair - multiple summary values for a single key (not under one context, one return)
        while (!workList.isEmpty()) {
            Pair<Object, Object> objectPair = workList.pop();
            Object root = objectPair.fst;
            Object child = objectPair.snd;
            if (visitedPair.contains(objectPair))
                continue;
            visitedPair.add(objectPair);

            //Assumption: root - child => only one label could be of a putField, no a --[f[g--> x
            for (IFlowLabel label: this.getEdgeLabels(root, child)) {
                //this only added edges by checking context-sensitive edges, should not iterate anymore
                if (isReturnBarEdge(label) || isParamBarEdge(label) || isMatchEdge(label))
                    continue; //dont add to adjacency list
                if (isPutFieldEdge(label)) {
                    //find the field summary and add to the adjacency list
                    //if this child is already visited with this field label, retrieve it from the map, else find the field summary edge
                    Pair<Object, IFlowLabel> fieldPair = Pair.make(child, label);
                    if (visitedFieldNodes.containsKey(fieldPair)) {
                        Set<Object> summaryValues = visitedFieldNodes.get(fieldPair);
                        if (summaryValues != null) {
                            for (Object value : summaryValues) {
                                checkAndAddAdjacencyList(root, value, adjacencyListFS);
                                fs_summary_count++;
                                this.getSuccNodes(value).forEachRemaining(node -> {
                                    if (!visitedPair.contains(Pair.make(value, node))) {
                                        workList.push(Pair.make(value, node));
                                    }
                                });
                            }
                        }
                        continue; // visited with match or no match
                    }
                    PutFieldLabel putFieldLabel = (PutFieldLabel)label;
                    GetFieldLabel getFieldLabel = GetFieldLabel.make(putFieldLabel.getField());
                    Set<Object> retNodes = getSummaryFS(root, child, getFieldLabel, adjacencyListFS, visitedPair, visitedFieldNodes);
                    for (Object ret : retNodes) {
                        checkAndAddAdjacencyList(root, ret, adjacencyListFS); //check this
                        this.getSuccNodes(ret).forEachRemaining(node -> {
                            if (!visitedPair.contains(Pair.make(ret, node))) {
                                workList.push(Pair.make(ret, node));
                            }
                        });
                    }
                    //if it's a mismatch, still get the last visited mismatched nodes and traverse further
                    //if no summary, then ignore it
                    //if this has not visited before
                    continue;
                }
                if (isGetFieldEdge(label)) {
                    this.getSuccNodes(child).forEachRemaining(node -> {
                        if (!visitedPair.contains(Pair.make(child, node))) {
                            workList.push(Pair.make(child, node));}
                    });
                    continue; //dont add to adjacency list, but traverse the child
                }
                //for all other edges, add it to the adjacency list and traverse further
                checkAndAddAdjacencyList(root, child, adjacencyListFS);
                this.getSuccNodes(child).forEachRemaining(node -> {
                    if (!visitedPair.contains(Pair.make(child, node))) {
                        workList.push(Pair.make(child, node));}
                });
            }
        }
    }

    /**
     * get the count of all edges, given a root node
     * to compute total edges in a graph
     * @param node - root node of the graph
     * @param graph - points to graph built
     */
    private static Integer getEdgeCount(Object node, PointerFlowGraph graph, int count, Set<Object> visitedNodes) {
        for (Object child : Iterator2Iterable.make(graph.getSuccNodes(node))) {
            //two nodes can have more than one edge
            //reverse edge should be eliminated, so we dont get stuck in loop
            int edgesCount = graph.getEdgeLabels(node, child).size();
            count += edgesCount;
            //System.out.println("child::" + child + " count::" + edgesCount);
            if (graph.getSuccNodeCount(child) > 0 && !visitedNodes.contains(child)) {
                visitedNodes.add(child);
                count = getEdgeCount(child, graph, count, visitedNodes);
            }
        }
        return count;
    }
    /**
     * find the root node or the return node for the allocation
     * o -> foo(),v2 -> Ret-V:foo() -> [main,v18, main,v20]
     * o -match--> main,v18
     * o -match--> main,v20
     * */
    private Set<Object> fetchReturnOrRootNode(Object returnNode, Set<Object> visited, Set<Object> rootNodes, Set<Pair<Object,Object>> visitedPair) {
        Set<Object> returnNodes = new HashSet<>();
        Stack<Pair<Object,Object>> worklist = new Stack<>();
        this.getPredNodes(returnNode).forEachRemaining(node -> worklist.push(Pair.make(node, returnNode)));
        while (!worklist.empty()) {
            Pair<Object, Object> objectPair= worklist.pop();
            Object child = objectPair.fst;
            if (visited.contains(child))
                continue;
            visited.add(child);
            visitedPair.add(objectPair);
            if (rootNodes.contains(child))
                returnNodes.add(child);
            //this.getPredNodes(child).forEachRemaining(node -> {if (!visitedPair.contains(Pair.make(root, child))) {worklist.push(Pair.make(node, child))}});
        }
        return returnNodes;
    }

    private boolean isApplicationInit(CGNode node) {
        IMethod method = node.getMethod();
        return method.isInit() && method.getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application);
    }

    @Override
    protected void addNodesForParameters(CGNode node, IR ir) {}

    //build nodes for parameters and add edges

    @Override
    protected FlowStatementVisitor makeVisitor(CGNode node) {
        return new StatementVisitor(heapModel, this, cha, cg, node, inverseEdges);
    }

    public static PointerFlowGraph makePointerFlowGraph(CallGraph chaCG, HeapModel heapModel, MemoryAccessMap mam, ClassHierarchy cha){
        return new PointerFlowGraph(chaCG, heapModel, mam, cha);
    }

    /**
     * usage: write the adjacency list to the file for Context-Sensitivity and Field-Sensitivity
     * */
    public static void writeAdjacencyListToFile(Map<Integer, Set<Integer>> adjacencyList, String fileName) {
        try {
            /*RandomAccessFile stream = new RandomAccessFile("AdjacencyListInputFile.gra", "rw");
            FileChannel channel = stream.getChannel();
*/
            File file = new File(fileName);
            FileWriter writer = new FileWriter(file);
            String header = "graph_for_greach";
            writer.write(header);
            writer.write("\n");
            int noOfNodes = adjacencyList.size();
            writer.write(""+ noOfNodes);
            writer.write("\n");
            for (int i : adjacencyList.keySet()) {
                String line = i + ": ";
                for (int j : adjacencyList.get(i)) {
                    if (i == j) continue;
                    line += j + " ";
                }
                line += "#";
                writer.write(line);
                writer.write("\n");
            }
            writer.close();

        }catch (IOException exception){
            System.out.println("Exception occurred:"+exception);
        }
    }
    /*
    * This function is to get the method names from the program to run on SPDS
    * */
    private void writeMethodNamesToFile(Set<String> methodNames, String fileName) {
        try {
            File file = new File(fileName);
            FileWriter writer = new FileWriter(file);
            for (String method : methodNames) {
                writer.write(method);
                writer.write("\n");
            }
            writer.close();
        } catch (IOException exception){
            System.out.println("Exception occurred:"+exception);
        }
    }
    /* *
     * create a test file for querying - combination of root nodes with leaf nodes or with query nodes from the input - if only one argument is given in the query
     * */
    private void writeTestFile(Set<Object> rootNodes, String fileName, Set<Integer> pts_to_queries, int reachable) {
        try {
            File file = new File(fileName);
            FileWriter writer = new FileWriter(file);
            for (int i : pts_to_queries) {
                for (Object root : rootNodes) {
                    int rt = this.getNumber(root);
                    String line = rt +" " + i + " " + reachable;
                    writer.write(line);
                    writer.write("\n");
                }
            }
            writer.close();
        } catch (IOException exception){
            System.out.println("Exception occurred:"+exception);
        }
    }

    /* *
     * create a test file for querying when the arguments are passed from the program via an invoke statement
     * eg: pointsToQuery(a, b) or pointsToQuery(a)
     * */
    private static void writeQueryTestFile(String fileName, int reachable) {
        try {
            File file = new File(fileName);
            FileWriter writer = new FileWriter(file);
            System.out.println("pts_queries::"+pts_queries);
            for (int i : pts_queries.keySet()) {
                int rt = pts_queries.get(i);
                String line = rt +" " + i + " " + reachable;
                writer.write(line);
                if (i < pts_queries.size())
                    writer.write("\n");
            }
            writer.close();
        } catch (IOException exception){
            System.out.println("Exception occurred:"+exception);
        }
    }

    /*
    * To generate the query file for Dacapo or any macro-benchmark
    * */
    private void generateQueries(int noOfQueries, String fileName, int reachable) {
        try {
            int max = this.getNumberOfNodes(), min = 0;
            File file = new File(fileName);
            FileWriter writer = new FileWriter(file);
            for (int i = 0; i < noOfQueries; i++) {
                Random random = new Random();
                int src = random.nextInt(max-min) ;
                int trg = random.nextInt(max-min+1);
                String line = src + " " + trg + " " + reachable;
                writer.write(line);
                writer.write("\n");
            }
            writer.close();
            System.out.println("File written");
        } catch (IOException exception){
            System.out.println("Exception occurred:"+exception);
        }
    }

    private boolean isParamEdge(IFlowLabel label) {
        return label.toString().contains("param[") && !label.isBarred();
    }

    private boolean isReturnEdge(IFlowLabel label) {
        return label.toString().contains("return[") && !label.isBarred();
    }

    private boolean isParamBarEdge(IFlowLabel label) {
        return label.toString().contains("paramBar[") && label.isBarred();
    }

    private boolean isReturnBarEdge(IFlowLabel label) {
        return label.toString().contains("returnBar[") && label.isBarred();
    }

    private boolean isGetFieldEdge(IFlowLabel label) {
        return label.toString().contains("getfield[");
    }

    private boolean isPutFieldEdge(IFlowLabel label) {
        return label.toString().contains("putfield[");
    }

    private boolean isAssignEdge(IFlowLabel label) {
        return label.toString().contains("assign");
    }

    private boolean isAssignOnlyEdge(IFlowLabel label) {
        return label.toString().equalsIgnoreCase("assign");
    }

    private boolean isNewEdge(IFlowLabel label) {
        return label.toString().equalsIgnoreCase("new");
    }

    private boolean isMatchEdge(IFlowLabel label) {
        return label.toString().contains("match[");
    }

    private boolean shouldIgnore(CGNode node) {
        IMethod method = node.getMethod();
        return method.isBridge()
                || method.isClinit()
                || method.isNative()
                || method.isSynthetic()
                || method.isWalaSynthetic()
                || method.isInit();
                // && !method.getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application));
    }

    private boolean isApplicationNode(CGNode node) {
        IMethod method = node.getMethod();
        return method.getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application);
    }
    /**
     * A visitor that generates graph nodes and edges for an IR.
     *
     * <p>strategy: when visiting a statement, for each use of that statement, add a graph edge from
     * def to use.
     *
     * <p>Parameter passing is done separately
     */
    public static class StatementVisitor extends SSAInstruction.Visitor
            implements FlowStatementVisitor {

        private final HeapModel heapModel;

        private final IFlowGraph g;

        private final IClassHierarchy cha;

        private final CallGraph cg;

        /**
         * The method node whose statements we are currently traversing
         */
        protected final CGNode node;

        /**
         * The governing IR
         */
        protected final IR ir;

        /**
         * The basic block currently being processed
         */
        private ISSABasicBlock basicBlock;

        /**
         * Governing symbol table
         */
        protected final SymbolTable symbolTable;

        /**
         * Def-use information
         */
        protected final DefUse du;

        //final Map<PointerKey, CGNode> parameters = HashMapFactory.make();
        public Map<PointerKey, Set<PointerKey>> inverseEdges;// = HashMapFactory.make();

        public StatementVisitor(
                HeapModel heapModel, IFlowGraph g, IClassHierarchy cha, CallGraph cg, CGNode node, Map<PointerKey, Set<PointerKey>> inverseEdges) {
            super();
            this.heapModel = heapModel;
            this.g = g;
            this.cha = cha;
            this.cg = cg;
            this.node = node;
            this.ir = node.getIR();
            this.du = node.getDU();
            this.symbolTable = ir.getSymbolTable();
            assert symbolTable != null;
            this.inverseEdges = inverseEdges;
        }

        @Override
        public void visitArrayLoad(SSAArrayLoadInstruction instruction) {
            // skip arrays of primitive type
            if (instruction.typeIsPrimitive()) {
                return;
            }
            PointerKey result = heapModel.getPointerKeyForLocal(node, instruction.getDef());
            PointerKey arrayRef = heapModel.getPointerKeyForLocal(node, instruction.getArrayRef());
            // TODO optimizations for purely local stuff
            g.addNode(result);
            g.addNode(arrayRef);
            //g.addEdge(result, arrayRef, GetFieldLabel.make(ArrayContents.v())); //AS - recheck!!!
            //ArrayContents arrayContents = ArrayContents.v();
            int index = instruction.getIndex();
            g.addEdge(arrayRef, result, GetFieldLabel.make(ArrayContentWithIndex.makeWithIndex(index)));
        }

        /**
         * @see IInstruction.Visitor#visitArrayStore(com.ibm.wala.shrike.shrikeBT.IArrayStoreInstruction)
         */
        @Override
        public void visitArrayStore(SSAArrayStoreInstruction instruction) {
            // Assertions.UNREACHABLE();
            // skip arrays of primitive type
            if (instruction.typeIsPrimitive()) {
                return;
            }
            // make node for used value
            PointerKey value = heapModel.getPointerKeyForLocal(node, instruction.getValue());
            PointerKey arrayRef = heapModel.getPointerKeyForLocal(node, instruction.getArrayRef());
            // TODO purely local optimizations
            g.addNode(value);
            g.addNode(arrayRef);
            //g.addEdge(value, arrayRef, PutFieldLabel.make(ArrayContents.v()));
            int index = instruction.getIndex();
            g.addEdge(value, arrayRef, PutFieldLabel.make(ArrayContentWithIndex.makeWithIndex(index)));
            //g.addEdge(arrayRef, value, PutFieldLabel.make(ArrayContentWithIndex.makeWithIndex(index)));
        }

        /**
         * @see IInstruction.Visitor#visitCheckCast(ITypeTestInstruction)
         */
        @Override
        public void visitCheckCast(SSACheckCastInstruction instruction) {
            Set<IClass> types = HashSetFactory.make();

            for (TypeReference t : instruction.getDeclaredResultTypes()) {
                IClass cls = cha.lookupClass(t);
                if (cls == null) {
                    return;
                } else {
                    types.add(cls);
                }
            }

            FilteredPointerKey.MultipleClassesFilter filter =
                    new FilteredPointerKey.MultipleClassesFilter(types.toArray(new IClass[0]));
            PointerKey result = heapModel.getPointerKeyForLocal(node, instruction.getResult());
            PointerKey value = heapModel.getPointerKeyForLocal(node, instruction.getVal());
            g.addNode(result);
            g.addNode(value);
            //g.addEdge(result, value, AssignLabel.make(filter)); //AS - recheck!!!!
            g.addEdge(value, result, AssignLabel.make(filter));
        }

        /**
         * @see IInstruction.Visitor#visitReturn(ReturnInstruction)
         */
        @Override
        public void visitReturn(SSAReturnInstruction instruction) {

            //System.out.println("Instruction ret::" + instruction);
            // skip returns of primitive type
            if (!instruction.returnsPrimitiveType() && !instruction.returnsVoid()) {
                // make a node for the result
                PointerKey resultNode = heapModel.getPointerKeyForLocal(node, instruction.getResult());
                g.addNode(resultNode);

                //make node for return value
                PointerKey returnValue = heapModel.getPointerKeyForReturnValue(node);
                g.addNode(returnValue);

                g.addEdge(resultNode, returnValue, AssignLabel.noFilter());
                    /*for (CallSiteReference site : Iterator2Iterable.make(node.iterateCallSites())) {
                        final ReturnEdge returnLabel = ReturnEdge.make(new CallerSiteContext(node, site));
                        g.addEdge(returnValue, def, returnLabel);
                    }*/
            }
        }

        /**
         * @see IInstruction.Visitor#visitGet(IGetInstruction)
         */
        @Override
        public void visitGet(SSAGetInstruction instruction) {
            visitGetInternal(
                    instruction.getDef(),
                    instruction.getRef(),
                    instruction.isStatic(),
                    instruction.getDeclaredField());
            instruction.getClass().getDeclaringClass();
            //cg.getClassHierarchy()
        }

        protected void visitGetInternal(int lval, int ref, boolean isStatic, FieldReference field) {

            // skip getfields of primitive type (optimisation) Todo should we??
            if (field.getFieldType().isPrimitiveType()) {
                return;
            }
            IField f = cg.getClassHierarchy().resolveField(field);
            if (f == null) {
                return;
            }
            PointerKey def = heapModel.getPointerKeyForLocal(node, lval);
            assert def != null;

            if (isStatic) {
                PointerKey fKey = heapModel.getPointerKeyForStaticField(f);
                g.addNode(def);
                g.addNode(fKey);
                //g.addEdge(def, fKey, AssignGlobalLabel.v()); //AS - recheck!!!!!!!
                g.addEdge(fKey, def, AssignGlobalLabel.v());
            } else {
                PointerKey refKey = heapModel.getPointerKeyForLocal(node, ref);
                g.addNode(def);
                g.addNode(refKey);
                // TODO purely local optimizations
                //g.addEdge(def, refKey, GetFieldLabel.make(f));
                g.addEdge(refKey, def, GetFieldLabel.make(f));
                //System.out.println("GETFIELD def::"+def);
                //System.out.println("refkey::"+refKey);
            }
        }

        /**
         * @see IInstruction.Visitor#visitPut(IPutInstruction)
         */
        @Override
        public void visitPut(SSAPutInstruction instruction) {
            visitPutInternal(
                    instruction.getVal(),
                    instruction.getRef(),
                    instruction.isStatic(),
                    instruction.getDeclaredField());
        }

        public void visitPutInternal(int rval, int ref, boolean isStatic, FieldReference field) {
            // skip putfields of primitive type (optimisation)
            if (field.getFieldType().isPrimitiveType()) {
                return;
            }
            IField f = cg.getClassHierarchy().resolveField(field);
            if (f == null) {
                return;
            }
            PointerKey use = heapModel.getPointerKeyForLocal(node, rval);
            assert use != null;

            if (isStatic) {
                PointerKey fKey = heapModel.getPointerKeyForStaticField(f);
                g.addNode(use);
                g.addNode(fKey);
                //g.addEdge(fKey, use, AssignGlobalLabel.v());
                g.addEdge(use, fKey, AssignGlobalLabel.v());
            } else {
                PointerKey refKey = heapModel.getPointerKeyForLocal(node, ref);
                g.addNode(use);
                g.addNode(refKey);
                //g.addEdge(refKey, use, PutFieldLabel.make(f));
                g.addEdge(use, refKey, PutFieldLabel.make(f));

                //adding the node to inverse edges, which is used in adding nodes for parameters and returns
                //if this pointerkey is 'this', then an inverse edge will be added
                //inverseEdges.put(refKey, use);
                inverseEdges.computeIfAbsent(refKey, k -> new HashSet<>());
                inverseEdges.get(refKey).add(use);
                //System.out.println("Inverse edge::"+inverseEdges);
            }
        }

        /**
         * @see IInstruction.Visitor#visitInvoke(IInvokeInstruction)
         */
        @Override
        public void visitInvoke(SSAInvokeInstruction instruction) {

            //what to do with special instructions -
            //instruction: invokespecial <Application, LA, <init>()V > v3 @4 exception:v4 - params 3
            //invokespecial < Application, Ljava/lang/Object, <init<()V > 1
            //if init - primitive do nothing else wrapper - do something - takeparam, make connection??

            //v11 = invokestatic<>@26
            //2 invokespecial < Application, LA, <init>()V > v3 @4 exception:v4
            //If static and no parameters
            // System.out.println("instructions:::" + instruction);

            //if init connect with param nodes

           /* if (instruction.isSpecial()) {

                PointerKey use = heapModel.getPointerKeyForLocal(node, instruction.getUse(0));
                g.addNode(use);


            }*/

            /*
            if (instruction.getNumberOfPositionalParameters() == 0) {
                if (instruction.getNumberOfUses() > 0) {
                    for (int i = 0; i < instruction.getNumberOfUses(); i++) {
                        // // just make nodes for parameters; we'll get to them when traversing from the callee
                        //actual parameters
                        PointerKey use = heapModel.getPointerKeyForLocal(node, instruction.getUse(i));
                        g.addNode(use);
                        System.out.println("Use::" + use);
                        *//*for(PointerKey pk : formalParameters.get(node)){
                            ParamBarLabel label = ParamBarLabel.make(new CallerSiteContext(node,instruction.getCallSite()));
                            addEdge(use,pk,label);
                        }*//*
                    }
                } else {
                   *//* System.out.println("target"+instruction.getNumberOfReturnValues());
                    System.out.println("REturn value::"+instruction.getReturnValue(0));
                    PointerKey returnNode = heapModel.getPointerKeyForReturnValue()
                    System.out.println("::"+instruction.);*//*
                }
                */
            //for any def'd values, keep track of the fact that they are def'd by a call
            /*if (instruction.hasDef()) {
                PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());
                g.addNode(def);
                System.out.println("Def::" + def);
                //params.put(def, instruction);
            }
*/
            //Pointer keys for returns
            //PointerKey exc = heapModel.getPointerKeyForLocal(node, instruction.getException());
            // g.addNode(exc);
            //callDefs.put(exc, instruction);
            //}
            /*if(instruction.isSpecial()) {
                System.out.println(instruction.getDef());
                PointerKey local =
            }*/
        }

        /**
         * @see IInstruction.Visitor#visitNew(NewInstruction)
         */
        @Override
        public void visitNew(SSANewInstruction instruction) {

            //NOT CONSIDERING ALLOC EDGES

            InstanceKey iKey = heapModel.getInstanceKeyForAllocation(node, instruction.getNewSite());
            if (iKey == null) {
                // something went wrong. I hope someone raised a warning.
                return;
            }
            PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());
            g.addNode(iKey);
            g.addNode(def);
            g.addEdge(def, iKey, NewLabel.v());

            NewMultiDimInfo multiDimInfo = getInfoForNewMultiDim(instruction, heapModel, node);
            if (multiDimInfo != null) {
                for (Pair<PointerKey, InstanceKey> newInstr : multiDimInfo.newInstrs) {
                    g.addNode(newInstr.fst);
                    g.addNode(newInstr.snd);
                    g.addEdge(newInstr.fst, newInstr.snd, NewLabel.v());
                }
                for (Pair<PointerKey, PointerKey> arrStoreInstr : multiDimInfo.arrStoreInstrs) {
                    g.addNode(arrStoreInstr.fst);
                    g.addNode(arrStoreInstr.snd);
                    g.addEdge(arrStoreInstr.fst, arrStoreInstr.snd, PutFieldLabel.make(ArrayContents.v()));
                }
            }
        }

        /**
         * @see IInstruction.Visitor#visitThrow(ThrowInstruction)
         */
        @Override
        public void visitThrow(SSAThrowInstruction instruction) {
            // don't do anything: we handle exceptional edges
            // in a separate pass
        }

        @Override
        public void visitGetCaughtException(SSAGetCaughtExceptionInstruction instruction) {
            List<ProgramCounter> peis =
                    SSAPropagationCallGraphBuilder.getIncomingPEIs(ir, getBasicBlock());
            PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());

            Set<IClass> types = SSAPropagationCallGraphBuilder.getCaughtExceptionTypes(instruction, ir);
            addExceptionDefConstraints(ir, node, peis, def, types);
        }

        /**
         * Generate constraints which assign exception values into an exception pointer
         *
         * @param node         governing node
         * @param peis         list of PEI instructions
         * @param exceptionVar PointerKey representing a pointer to an exception value
         * @param catchClasses the types "caught" by the exceptionVar
         */
        protected void addExceptionDefConstraints(
                IR ir,
                CGNode node,
                List<ProgramCounter> peis,
                PointerKey exceptionVar,
                Set<IClass> catchClasses) {
            for (ProgramCounter peiLoc : peis) {
                SSAInstruction pei = ir.getPEI(peiLoc);

                if (pei instanceof SSAAbstractInvokeInstruction) {
                    SSAAbstractInvokeInstruction s = (SSAAbstractInvokeInstruction) pei;
                    PointerKey e = heapModel.getPointerKeyForLocal(node, s.getException());
                    g.addNode(exceptionVar);
                    g.addNode(e);
                    g.addEdge(exceptionVar, e, AssignLabel.noFilter());

                } else if (pei instanceof SSAAbstractThrowInstruction) {
                    SSAAbstractThrowInstruction s = (SSAAbstractThrowInstruction) pei;
                    PointerKey e = heapModel.getPointerKeyForLocal(node, s.getException());
                    g.addNode(exceptionVar);
                    g.addNode(e);
                    g.addEdge(exceptionVar, e, AssignLabel.noFilter());
                }

                // Account for those exceptions for which we do not actually have a
                // points-to set for
                // the pei, but just instance keys
                Collection<TypeReference> types = pei.getExceptionTypes();
                if (types != null) {
                    for (TypeReference type : types) {
                        if (type != null) {
                            InstanceKey ik = heapModel.getInstanceKeyForPEI(node, peiLoc, type);
                            if (ik == null) {
                                // probably due to exclusions
                                continue;
                            }
                            assert ik instanceof ConcreteTypeKey
                                    : "uh oh: need to implement getCaughtException constraints for instance " + ik;
                            ConcreteTypeKey ck = (ConcreteTypeKey) ik;
                            IClass klass = ck.getType();
                            if (PropagationCallGraphBuilder.catches(catchClasses, klass, cha)) {
                                g.addNode(exceptionVar);
                                g.addNode(ik);
                                g.addEdge(exceptionVar, ik, NewLabel.v());
                            }
                        }
                    }
                }
            }
        }

        /*
         * (non-Javadoc)
         *
         * @see com.ibm.domo.ssa.SSAInstruction.Visitor#visitPi(com.ibm.domo.ssa.SSAPiInstruction)
         */
        @Override
        public void visitPi(SSAPiInstruction instruction) {
            // for now, ignore condition and just treat it as a copy
            PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());
            PointerKey use = heapModel.getPointerKeyForLocal(node, instruction.getVal());
            g.addNode(def);
            g.addNode(use);
            g.addEdge(def, use, AssignLabel.noFilter());
        }

        public ISSABasicBlock getBasicBlock() {
            return basicBlock;
        }

        /**
         * The calling loop must call this in each iteration!
         */
        @Override
        public void setBasicBlock(ISSABasicBlock block) {
            basicBlock = block;
        }

        @Override
        public void visitLoadMetadata(SSALoadMetadataInstruction instruction) {
            PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());
            assert instruction.getType() == TypeReference.JavaLangClass;
            InstanceKey iKey =
                    heapModel.getInstanceKeyForMetadataObject(instruction.getToken(), instruction.getType());

            g.addNode(iKey);
            g.addNode(def);
            g.addEdge(def, iKey, NewLabel.v());
        }
    }

    public static class NewMultiDimInfo {

        public final Collection<Pair<PointerKey, InstanceKey>> newInstrs;

        // pairs of (base pointer, stored val)
        public final Collection<Pair<PointerKey, PointerKey>> arrStoreInstrs;

        public NewMultiDimInfo(
                Collection<Pair<PointerKey, InstanceKey>> newInstrs,
                Collection<Pair<PointerKey, PointerKey>> arrStoreInstrs) {
            this.newInstrs = newInstrs;
            this.arrStoreInstrs = arrStoreInstrs;
        }

    }

    /**
     * collect information about the new instructions and putfield instructions used to model an
     * allocation of a multi-dimensional array. excludes the new instruction itself (i.e., the
     * allocation of the top-level multi-dim array).
     */
    public static NewMultiDimInfo getInfoForNewMultiDim(
            SSANewInstruction instruction, HeapModel heapModel, CGNode node) {
        if (heapModel == null) {
            throw new IllegalArgumentException("null heapModel");
        }
        Collection<Pair<PointerKey, InstanceKey>> newInstrs = HashSetFactory.make();
        Collection<Pair<PointerKey, PointerKey>> arrStoreInstrs = HashSetFactory.make();
        InstanceKey iKey = heapModel.getInstanceKeyForAllocation(node, instruction.getNewSite());
        if (iKey == null) {
            // something went wrong. I hope someone raised a warning.
            return null;
        }
        IClass klass = iKey.getConcreteType();
        // if not a multi-dim array allocation, return null
        if (!klass.isArrayClass()
                || ((ArrayClass) klass).getElementClass() == null
                || !((ArrayClass) klass).getElementClass().isArrayClass()) {
            return null;
        }
        PointerKey def = heapModel.getPointerKeyForLocal(node, instruction.getDef());

        int dim = 0;
        InstanceKey lastInstance = iKey;
        PointerKey lastVar = def;
        while (klass != null && klass.isArrayClass()) {
            klass = ((ArrayClass) klass).getElementClass();
            // klass == null means it's a primitive
            if (klass != null && klass.isArrayClass()) {
                InstanceKey ik =
                        heapModel.getInstanceKeyForMultiNewArray(node, instruction.getNewSite(), dim);
                PointerKey pk = heapModel.getPointerKeyForArrayContents(lastInstance);
                // if (DEBUG_MULTINEWARRAY) {
                // Trace.println("multinewarray constraint: ");
                // Trace.println(" pk: " + pk);
                // Trace.println(" ik: " + system.findOrCreateIndexForInstanceKey(ik)
                // + " concrete type " + ik.getConcreteType()
                // + " is " + ik);
                // Trace.println(" klass:" + klass);
                // }
                // g.addEdge(pk, ik, NewLabel.v());
                newInstrs.add(Pair.make(pk, ik));
                arrStoreInstrs.add(Pair.make(lastVar, pk));
                lastInstance = ik;
                lastVar = pk;
                dim++;
            }
        }

        return new NewMultiDimInfo(newInstrs, arrStoreInstrs);
    }

    /**
     * Edges which represents flow of parameters in inter-procedural graph
     * also includes the context of the callsite
     * */
    private static final class ParamEdge implements IFlowLabel {

        CallerSiteContext context;

        public ParamEdge(CallerSiteContext context) {
            this.context = context;
        }

        public static ParamEdge make(CallerSiteContext context) {
            return new ParamEdge(context);
        }

        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {
        }

        @Override
        public String toString() {
            return "param[" + context + ']';
        }

        @Override
        public ParamBarEdge bar() {
            return new ParamBarEdge(context);
        }

        @Override
        public boolean isBarred() {
            return false;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final ParamEdge other = (ParamEdge) obj;
            if (context == null) {
                return other.context == null;
            } else return context.equals(other.context);
        }
    }

    /**
     * Edges which represent flow of return values from call to return
     * also includes the context of the callsite
     */
    private static final class ReturnEdge implements IFlowLabel {
        CallerSiteContext context;
        public ReturnEdge(CallerSiteContext context) {
            this.context = context;
        }
        public static ReturnEdge make(CallerSiteContext context) {
            return new ReturnEdge(context);
        }
        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {
        }
        @Override
        public ReturnBarEdge bar() {
            return new ReturnBarEdge(context);
        }
        @Override
        public boolean isBarred() {
            return false;
        }
        @Override
        public String toString() {
            return "return[" + context + ']';
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final ReturnEdge other = (ReturnEdge) obj;
            if (context == null) {
                return other.context == null;
            } else return context.equals(other.context);
        }
    }

    /**
     * Edges which represents flow of parameters in inter-procedural graph
     * also includes the context of the call site
     * */
    private static final class ParamBarEdge implements IFlowLabel {

        CallerSiteContext context;

        public ParamBarEdge(CallerSiteContext context) {
            this.context = context;
        }

        public CallerSiteContext getContext() {
            return this.context;
        }

        public static ParamBarEdge make(CallerSiteContext context) {
            return new ParamBarEdge(context);
        }
        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {

        }

        @Override
        public ParamEdge bar() {
            return ParamEdge.make(context);
        }

        @Override
        public boolean isBarred() {
            return true;
        }

        @Override
        public String toString() {
            return "paramBar[" + context + ']';
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final ParamBarEdge other = (ParamBarEdge) obj;
            if (context == null) {
                return other.context == null;
            } else return context.equals(other.context);
        }
    }

    /**
     * Edges which represent flow of return values from call to return
     * also includes the context of the callsite
     */
    private static final class ReturnBarEdge implements IFlowLabel{

        CallerSiteContext context;

        private ReturnBarEdge(CallerSiteContext context) {
            this.context = context;
        }

        public static ReturnBarEdge make(CallerSiteContext context) {
            return new ReturnBarEdge(context);
        }

        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {
        }

        @Override
        public ReturnEdge bar() {
            return ReturnEdge.make(context);
        }

        @Override
        public boolean isBarred() {
            return true;
        }

        @Override
        public String toString() {
            return "returnBar[" + context + "]";
        }
    }

    /**
     * Edges which represent flow of actual parameters to call site definition
     * also includes the context of the callsite
     */
    private static final class MatchEdge implements IFlowLabel {
        CallerSiteContext context;

        private MatchEdge(CallerSiteContext context) { this.context=context; }

        public static MatchEdge make(CallerSiteContext context) { return new MatchEdge(context); }

        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {
        }

        @Override
        public MatchEdge bar() { return MatchEdge.make(context); }

        @Override
        public boolean isBarred() { return false; }

        @Override
        public String toString() { return "match[" + context + "]"; }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final MatchEdge other = (MatchEdge) obj;
            if (context == null) {
                return other.context == null;
            } else return context.equals(other.context);
        }
    }

    private static final class MatchBarEdge implements IFlowLabel {
        CallerSiteContext context;
        private MatchBarEdge(CallerSiteContext context) { this.context=context; }
        public static MatchBarEdge make(CallerSiteContext context) { return new MatchBarEdge(context); }
        @Override
        public void visit(IFlowLabelVisitor v, Object dst) {
        }
        @Override
        public MatchEdge bar() { return MatchEdge.make(context); }
        @Override
        public boolean isBarred() { return false; }
        @Override
        public String toString() { return "match[" + context + "]"; }
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final MatchBarEdge other = (MatchBarEdge) obj;
            if (context == null) {
                return other.context == null;
            } else return context.equals(other.context);
        }
    }

    private static final class ArrayContentWithIndex implements IField {
        int index;

        private ArrayContentWithIndex(int index) {
            this.index = index;
        }

        public static ArrayContentWithIndex makeWithIndex(int index) {
            return new ArrayContentWithIndex(index);
        }

        @Override
        public String toString() {
            return "arr["+index+"]";
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null) return false;
            if (getClass() != obj.getClass()) return false;
            final ArrayContentWithIndex other = (ArrayContentWithIndex) obj;
            return index == other.index;
        }
        @Override
        public TypeReference getFieldTypeReference() {
            Assertions.UNREACHABLE();
            return null;
        }

        @Override
        public FieldReference getReference() {
            Assertions.UNREACHABLE();
            return null;
        }

        @Override
        public boolean isFinal() {
            Assertions.UNREACHABLE();
            return false;
        }

        @Override
        public boolean isPrivate() {
            Assertions.UNREACHABLE();
            return false;
        }

        @Override
        public boolean isProtected() {
            Assertions.UNREACHABLE();
            return false;
        }

        @Override
        public boolean isPublic() {
            Assertions.UNREACHABLE();
            return false;
        }

        @Override
        public IClass getDeclaringClass() {
            Assertions.UNREACHABLE();
            return null;
        }

        @Override
        public Atom getName() {
            Assertions.UNREACHABLE();
            return null;
        }

        @Override
        public boolean isStatic() {
            Assertions.UNREACHABLE();
            return false;
        }

        @Override
        public Collection<Annotation> getAnnotations() {
            return Collections.emptySet();
        }

        @Override
        public boolean isVolatile() {
            return false;
        }

        @Override
        public IClassHierarchy getClassHierarchy() {
            Assertions.UNREACHABLE();
            return null;
        }
    }

}
