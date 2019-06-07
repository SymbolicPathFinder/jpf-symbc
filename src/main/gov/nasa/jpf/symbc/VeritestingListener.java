package gov.nasa.jpf.symbc;


import gov.nasa.jpf.jvm.bytecode.IfInstruction;
import gov.nasa.jpf.symbc.veritesting.Heuristics.HeuristicManager;
import gov.nasa.jpf.symbc.veritesting.Heuristics.PathStatus;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.PropertyListenerAdapter;
import gov.nasa.jpf.jvm.JVMDirectCallStackFrame;
import gov.nasa.jpf.jvm.bytecode.GOTO;
import gov.nasa.jpf.report.ConsolePublisher;
import gov.nasa.jpf.report.Publisher;
import gov.nasa.jpf.report.PublisherExtension;
import gov.nasa.jpf.symbc.numeric.*;
import gov.nasa.jpf.symbc.veritesting.*;
import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticBranchChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticPCChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.*;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.AstToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.AstToGreen.WalaVarToSPFVarVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicOutputTable;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SlotParamTable;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesPass1Visitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesPass2Visitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfToGreenVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubstituteGetOutput;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.linearization.LinearizationTransformation;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;

import gov.nasa.jpf.symbc.veritesting.ast.transformations.typepropagation.TypePropagationVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import gov.nasa.jpf.vm.*;
import gov.nasa.jpf.vm.Instruction;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.RealConstant;

import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;


import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract.contractDiscoveryOn;
import static gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticBranchChoiceGenerator.*;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingMain.skipRegionStrings;
import static gov.nasa.jpf.symbc.veritesting.VeritestingMain.skipVeriRegions;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.*;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.isSymCond;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.isStackConsumingRegionEnd;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.maybeParseConstraint;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager.*;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SpfCasesInstruction.*;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArrayUtil.doArrayStore;

public class VeritestingListener extends PropertyListenerAdapter implements PublisherExtension {


    // veritestingMode ranges from 1 to 5 which is the same as runMode ranging from VANILLASPF, VERITESTING, HIGHORDER,
    // SPFCASES, EARLYRETURNS
    public static int veritestingMode = 0;
    public static VeritestingMode runMode;

    public static long totalSolverTime = 0, z3Time = 0;
    public static long parseTime = 0, regionSummaryParseTime = 0;
    public static long solverAllocTime = 0;
    public static long cleanupTime = 0;
    public static int solverCount = 0;
    public static int maxStaticExplorationDepth = 1;
    public static boolean initializeTime = true;
    public static int veritestRegionCount = 0;
    private static long staticAnalysisDur;
    public static String key;
    private final long runStartTime = System.nanoTime();
    public static StatisticManager statisticManager = new StatisticManager();
    private static int veritestRegionExpectedCount = -1;
    private static int instantiationLimit = -1;
    public static boolean simplify = true;
    public static boolean jitAnalysis = true;
    // makes timeout reporting happens at least 12 times in the last 2 minutes before a timeout at a gap of 10 seconds
    private static int timeout_mins = -1, timeoutReportingCounter = 12;
    private static long npaths = 0;

    public static StringBuilder regionDigest = new StringBuilder();
    public static boolean printRegionDigest = false;
    private static String regionDigestPrintName;

    private static boolean spfCasesHeuristicsOn = false;

    public enum VeritestingMode {VANILLASPF, VERITESTING, HIGHORDER, SPFCASES, EARLYRETURNS}


    public static boolean performanceMode = false;
    // reads in a exclusionsFile configuration option, set to ${jpf-symbc}/MyJava60RegressionExclusions.txt by default
    public static String exclusionsFile;


    // reads in an array of Strings, each of which is the name of a method whose regions we wish to report metrics for
    public static String[] interestingClassNames;

    public String[] regionKeys = {"replace.amatch([C[CI)I#160",
            "replace.amatch([C[CI)I#77",
            "replace.dodash(C[C[C)V#112",
            "replace.dodash(C[C[C)V#8",
            "replace.esc([C)C#7",
            "replace.getccl([C[C)Z#15",
            "replace.getccl([C[C)Z#84",
            "replace.makepat([C[C)I#305",
            "replace.makepat([C[C)I#458",
            "replace.makepat([C[C)I#474",
            "replace.makepat([C[C)I#491",
            "replace.makepat([C[C)I#507",
            "replace.makepat([C[C)I#521",
            "replace.makesub([C[C)I#111",
            "replace.makesub([C[C)I#124",
            "replace.makesub([C[C)I#23",
            "replace.makesub([C[C)I#34",
            "replace.makesub([C[C)I#64",
            "replace.makesub([C[C)I#7",
            "replace.omatch([C[CI)Z#108",
            "replace.omatch([C[CI)Z#132",
            "replace.omatch([C[CI)Z#241",
            "replace.omatch([C[CI)Z#64",
            "replace.patsize([CI)I#32"};

    public VeritestingListener(Config conf, JPF jpf) {
        if (conf.hasValue("veritestingMode")) {
            veritestingMode = conf.getInt("veritestingMode");
            runMode = veritestingMode == 5 ? VeritestingMode.EARLYRETURNS :
                    (veritestingMode == 4 ? VeritestingMode.SPFCASES :
                            ((veritestingMode == 3 ? VeritestingMode.HIGHORDER :
                                    (veritestingMode == 2 ? VeritestingMode.VERITESTING : VeritestingMode.VANILLASPF))));

            switch (runMode) {
                case VANILLASPF:
                    System.out.println("* Warning: either invalid or no veritestingMode specified.");
                    System.out.println("* Warning: set veritestingMode to 1 to use vanilla SPF with VeritestingListener");
                    System.out.println("* Warning: set veritestingMode to 2 to use veritesting");
                    System.out.println("* Warning: set veritestingMode to 3 to use veritesting with higher order regions");
                    System.out.println("* Warning: set veritestingMode to 4 to use veritesting with higher order regions and SPFCases");
                    System.out.println("* Warning: resetting veritestingMode to 0 (aka use vanilla SPF)");
                    veritestingMode = 0;
                    break;
                case VERITESTING:
                    System.out.println("* running veritesting without SPFCases.");
                    break;
                case SPFCASES:
                    System.out.println("* running veritesting with SPFCases.");
                    break;
                case EARLYRETURNS:
                    System.out.println("* running veritesting with SPFCases and Early Returns.");
                    break;
            }

            if (conf.hasValue("performanceMode"))
                performanceMode = conf.getBoolean("performanceMode");
            if (conf.hasValue("jpf-symbc")) {
                exclusionsFile = conf.getString("jpf-symbc") + "/MyJava60RegressionExclusions.txt";
            }
            if (conf.hasValue("jitAnalysis")) {
                jitAnalysis = conf.getBoolean("jitAnalysis");
            }
            if (conf.hasValue("exclusionsFile")) {
                exclusionsFile = conf.getString("exclusionsFile");
                if (jitAnalysis) {
                    System.out.println("**** warning: exclusionsFile is ignored when jitAnalysis is turned on");
                    System.out.println("use jitAnalysis = false in your JPF configuration file to use the exclusionsFile property");
                }
            }
            if (conf.hasValue("interestingClassNames")) {
                interestingClassNames = conf.getStringArray("interestingClassNames", new char[]{','});
            }

            if (conf.hasValue("veritestRegionExpectedCount"))
                veritestRegionExpectedCount = conf.getInt("veritestRegionExpectedCount");

            if (conf.hasValue("instantiationLimit"))
                instantiationLimit = conf.getInt("instantiationLimit");

            if (conf.hasValue("simplify"))
                simplify = conf.getBoolean("simplify");

            if (conf.hasValue("SPFCasesHeuristics") && (veritestingMode >= 4))
                spfCasesHeuristicsOn = conf.getBoolean("SPFCasesHeuristics");


            if (conf.hasValue("printRegionDigest")) {
                printRegionDigest = conf.getBoolean("printRegionDigest");
                if (conf.hasValue("regionDigestPrintName"))
                    regionDigestPrintName = conf.getString("regionDigestPrintName");
                else
                    regionDigestPrintName = "UnspecifiedDigestName";
                if (printRegionDigest) regionDigest.append("\n").append(regionDigestPrintName).append("\n");
            }
            if (conf.hasValue("maxStaticExplorationDepth"))
                maxStaticExplorationDepth = conf.getInt("maxStaticExplorationDepth");

            if (conf.hasValue("contractDiscoveryOn"))
                contractDiscoveryOn = conf.getBoolean("contractDiscoveryOn");

            StatisticManager.veritestingRunning = true;
            jpf.addPublisherExtension(ConsolePublisher.class, this);
            if (System.getenv("TIMEOUT_MINS") != null) {
                timeout_mins = Integer.parseInt(System.getenv("TIMEOUT_MINS"));
            }

            if (contractDiscoveryOn)
                if (conf.hasValue("contractMethodName"))
                    DiscoverContract.contractMethodName = conf.getString("contractMethodName");
        }
    }

    public SymbolicInteger makeSymbolicInteger(String name) {
        //return new SymbolicInteger(name, MinMax.getVarMinInt(name), MinMax.getVarMaxInt(name));
        return new SymbolicInteger(name, Integer.MIN_VALUE, Integer.MAX_VALUE);
    }

    /**
     * Listener's main method that checks every instruction for being a potential veritesting region.
     *
     * @param vm                   Virtual Machine.
     * @param ti                   Current running Thread.
     * @param instructionToExecute instruction to be executed.
     */
    public void executeInstruction(VM vm, ThreadInfo ti, Instruction instructionToExecute) {
        if (timeout_mins != -1) {
            long runningTimeNsecs = System.nanoTime() - runStartTime;
            if (TimeUnit.NANOSECONDS.toSeconds(runningTimeNsecs) > ((timeout_mins * 60) - (10 * timeoutReportingCounter))) {
                System.out.println("Metrics Vector:");
                System.out.println(getMetricsVector(runningTimeNsecs));
                timeoutReportingCounter--;
            }
        }
        StackFrame curr = ti.getTopFrame();

        boolean isIfInstruction = instructionToExecute instanceof IfInstruction;
        boolean isEmptyRegionHeuristic = HeuristicManager.getRegionHeuristicSize() == 0;
        boolean isActiveLastRegion = (isEmptyRegionHeuristic) ? false :
                HeuristicManager.getRegionHeuristic().getRegionStatus();

        String lastRegionKey = (isEmptyRegionHeuristic) ? null : HeuristicManager.getLastRegionKey();

//        runAdapterSynth(ti, curr);
        if (runMode == VeritestingMode.VANILLASPF)
            return;
        else if (isEmptyRegionHeuristic && !isIfInstruction)
            return;
        else if (!isEmptyRegionHeuristic && !isActiveLastRegion && !isIfInstruction)
            return;
        else if (spfCasesHeuristicsOn
                && StaticBranchChoiceGenerator.heuristicsCountingMode
                && isIfInstruction
                && !keyFromInstructionToExc(instructionToExecute).equals(lastRegionKey)) //if we are in another
            // if-statement inside the heuristic counting mode, then just return and let spf handle it.
            return;
        else if (spfCasesHeuristicsOn && StaticBranchChoiceGenerator.heuristicsCountingMode) { //if we are
            // in heuristic
            // mode then count
            // paths, if we are at the end of the region of interest then return
            PathStatus pathStatus = HeuristicManager.incrementRegionExactHeuristicCount(instructionToExecute);
            switch (pathStatus) {
                case ENDREACHED:
                    ti.getVM().getSystemState().setIgnored(true);
                    return;
                case INHEURISTIC:
                case OUTHEURISTIC:
                    break; // continue veritesting.
            }
        }


        if (!performanceMode) {
            if (instantiationLimit > 0 && statisticManager.getSuccInstantiations() > instantiationLimit) return;
            boolean noVeritestingFlag = false;
            noVeritestingFlag = isNoVeritesting(curr, noVeritestingFlag);
            if (noVeritestingFlag)
                return;
            // End equivalence checking code
        }

        String key = keyFromInstructionToExc(instructionToExecute);


        StatisticManager.instructionToExec = key;
        try {
            if (jitAnalysis) {
                StaticRegion staticRegion;
                if (!skipVeriRegions.contains(key) && isAllowedRegion(key)) {
                    if (isSymCond(ti, instructionToExecute)) {
                        thisHighOrdCount = 0;
                        staticRegion = JITAnalysis.discoverRegions(ti, instructionToExecute, key); // Just-In-Time static analysis to discover regions
                        if (staticRegion != null) {
                            if (printRegionDigest) regionDigest.append("\n").append(staticRegion.staticStmt.toString());
                            runVeritestingWrapper(ti, vm, staticRegion, instructionToExecute);
                        }
                    } /*else
                        statisticManager.updateConcreteHitStatForRegion(key);*/
                }
            } else { //not jitAnalysis
                if (initializeTime) {
                    discoverRegions(ti); // static analysis to discover regions
                    initializeTime = false;
                } else {
                    HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;
                    StaticRegion staticRegion = regionsMap.get(key);
                    if ((staticRegion != null) && !(staticRegion.isMethodRegion) && !skipVeriRegions.contains(key) &&
                            isAllowedRegion(key)) {
                        thisHighOrdCount = 0;
                        //if (SpfUtil.isSymCond(staticRegion.staticStmt)) {
                        if (SpfUtil.isSymCond(ti, staticRegion.staticStmt, (SlotParamTable) staticRegion.slotParamTable, instructionToExecute)) {
                            if (printRegionDigest) regionDigest.append("\n").append(staticRegion.staticStmt.toString());
                            runVeritestingWrapper(ti, vm, staticRegion, instructionToExecute);
                        } else
                            statisticManager.updateConcreteHitStatForRegion(key);
                    }
                }
            }
        } catch (IllegalArgumentException e) {
            statisticManager.updateSPFHitForRegion(key, e.getMessage());
            System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
            updateSkipRegions(e.getMessage(), key);
            writeRegionDigest();
            return;
        } catch (StaticRegionException sre) {
            statisticManager.updateSPFHitForRegion(key, sre.getMessage());
            System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + sre.getMessage() + "\n");
            updateSkipRegions(sre.getMessage(), key);
            writeRegionDigest();
            return;
        } catch (VisitorException greenEx) {
            statisticManager.updateSPFHitForRegion(key, greenEx.getMessage());
            System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + greenEx.getMessage() + "\n");
            updateSkipRegions(greenEx.getMessage(), key);
            writeRegionDigest();
            return;
        } catch (CloneNotSupportedException e) {
            System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
            e.printStackTrace();
            updateSkipRegions(e.getMessage(), key);
            writeRegionDigest();
            return;
        } catch (Exception e) {
            System.out.println("!!!!!!!! Aborting Veritesting !!!!!!!!!!!! " + "\n" + e.getMessage() + "\n");
            e.printStackTrace();
            updateSkipRegions(e.getMessage(), key);
            writeRegionDigest();
        }
    }


    private void runVeritestingWrapper(ThreadInfo ti, VM vm, StaticRegion staticRegion, Instruction instructionToExecute) throws Exception {
        if ((runMode != VeritestingMode.SPFCASES) && (runMode != VeritestingMode.EARLYRETURNS)) {
            isRegionEndOk(staticRegion, instructionToExecute);

            DynamicRegion dynRegion = runVeritesting(ti, instructionToExecute, staticRegion, key);
            Instruction nextInstruction = setupSPF(ti, instructionToExecute, dynRegion, null);
            ++veritestRegionCount;
            ti.setNextPC(nextInstruction);
            statisticManager.updateVeriSuccForRegion(key);

            System.out.println("------------- Region was successfully veritested --------------- ");
        } else {
            isRegionEndOk(staticRegion, instructionToExecute);
            runVeritestingWithSPF(ti, vm, instructionToExecute, staticRegion, key);
        }
    }

    private void isRegionEndOk(StaticRegion staticRegion, Instruction instructionToExecute) throws StaticRegionException {
        boolean isEndingInsnStackConsuming = isStackConsumingRegionEnd(staticRegion, instructionToExecute);
        // If region ends on a stack operand consuming instruction then the region should have a stack output
        if (isEndingInsnStackConsuming && staticRegion.stackOutput == null) {
            String ex = "Region ends on a stack-consuming instruction";
            skipRegionStrings.add(ex);
            throwException(new StaticRegionException(ex), INSTANTIATION);
        }
        if (!isEndingInsnStackConsuming && staticRegion.stackOutput != null) {
            String ex = "Region with stack output ends on a non-stack-consuming instruction";
            skipRegionStrings.add(ex);
            throwException(new StaticRegionException(ex), INSTANTIATION);
        }
    }

    private String keyFromInstructionToExc(Instruction instructionToExecute) {
        MethodInfo methodInfo = instructionToExecute.getMethodInfo();
        String className = methodInfo.getClassName();
        String methodName = methodInfo.getName();
        String methodSignature = methodInfo.getSignature();
        int offset = instructionToExecute.getPosition();
        key = CreateStaticRegions.constructRegionIdentifier(className + "." + methodName + methodSignature, offset);
        return key;
    }


    private void discoverRegions(ThreadInfo ti) {
        Config conf = ti.getVM().getConfig();
        String[] allClassPaths = conf.getStringArray("classpath");
        ArrayList<String> classPath = new ArrayList<>();
        for (String s : allClassPaths) {
            classPath.add(s);
            // These classpaths are (1) classpath in .jpf file, (2) SPF class paths, (3) JPF-core class paths, so we
            // want to run static analysis only on class paths in the .jpf file
//            if (!s.contains("jpf-symbc")) classPath.add(s);
//            else break;
        }
        String className = conf.getString("target");
        VeritestingMain veritestingMain = new VeritestingMain(ti);
        long startTime = System.nanoTime();
        veritestingMain.analyzeForVeritesting(classPath, className);
        long endTime = System.nanoTime();
        staticAnalysisDur = endTime - startTime;
        statisticManager.collectStaticAnalysisMetrics(VeritestingMain.veriRegions);
        StaticRegionException.staticAnalysisComplete();
    }

    private boolean isNoVeritesting(StackFrame curr, boolean noVeritestingFlag) {
        String[] allowedFunctions = new String[]{"adapt", "f1", "f2"};
        for (String s : allowedFunctions)
            if (curr.getMethodInfo().getName().equals(s)) return false;
        while (!JVMDirectCallStackFrame.class.isInstance(curr)) {
            if (curr.getMethodInfo().getName().contains("NoVeritest")) {
                noVeritestingFlag = true;
                break;
            } else curr = curr.getPrevious();
        }
        return noVeritestingFlag;
    }

    private boolean isAllowedRegion(String key) {
        return true;
        /*int allowed_regions_bv = Integer.parseInt(System.getenv("REGION_BV"));
        for (int i = 0; i < regionKeys.length; i++) {
            if ((allowed_regions_bv & (1 << i)) != 0) {
                if (key.equals(regionKeys[i]))
                    return true;
            }
        }
        return false;*/
    }

    private void updateSkipRegions(String message, String key) {
        for (String skipString : skipRegionStrings) {
            if (message.toLowerCase().contains(skipString.toLowerCase()))
                skipVeriRegions.add(key);
        }
    }

    private void runVeritestingWithSPF(ThreadInfo ti, VM vm, Instruction instructionToExecute, StaticRegion staticRegion,
                                       String key) throws Exception {

        if (!ti.isFirstStepInsn() && !StaticBranchChoiceGenerator.heuristicsCountingMode) { // first time around
            StaticPCChoiceGenerator newCG;
            DynamicRegion dynRegion = runVeritesting(ti, instructionToExecute, staticRegion, key);
            if (dynRegion.totalNumPaths > 0 && dynRegion.totalNumPaths <= (getNumSatChoices(dynRegion))) {
                String ex = "region instantiation is not beneficial (" +
                        dynRegion.totalNumPaths + "," + getNumSatChoices(dynRegion) + ")";
                skipRegionStrings.add(ex);
                throwException(new StaticRegionException(ex), INSTANTIATION);
            }
            if (spfCasesHeuristicsOn)
                newCG = new StaticBranchChoiceGenerator(dynRegion, instructionToExecute, true);
            else
                newCG = new StaticBranchChoiceGenerator(dynRegion, instructionToExecute);

            newCG.makeVeritestingCG(ti, instructionToExecute, key);

            SystemState systemState = vm.getSystemState();
            systemState.setNextChoiceGenerator(newCG);
            ti.setNextPC(instructionToExecute);
            hgOrdRegionInstance += thisHighOrdCount;
            statisticManager.updateVeriSuccForRegion(key);
            ++VeritestingListener.veritestRegionCount;
        } else {
            ChoiceGenerator<?> cg = ti.getVM().getSystemState().getChoiceGenerator();
            if (cg instanceof StaticPCChoiceGenerator) {
                StaticPCChoiceGenerator vcg = (StaticPCChoiceGenerator) cg;
                int choice = (Integer) cg.getNextChoice();
                Instruction nextInstruction = null;
                try {
                    nextInstruction = vcg.execute(ti, instructionToExecute, choice);
                } catch (StaticRegionException sre) {
                    System.out.println(sre.toString());
                    return;
                }

                ti.setNextPC(nextInstruction);
            }
        }
    }

    @Override
    public void threadTerminated(VM vm, ThreadInfo terminatedThread) {
        System.out.println("threadTerminated");
        npaths++;
        super.threadTerminated(vm, terminatedThread);
    }

    @Override
    public void choiceGeneratorRegistered(VM vm, ChoiceGenerator<?> nextCG, ThreadInfo currentThread, Instruction executedInstruction) {
        System.out.println("choiceGeneratorRegistered(" + nextCG.getClass() + ") at " + executedInstruction.getMethodInfo() + "#" + executedInstruction.getPosition());
    }

    @Override
    public void choiceGeneratorProcessed(VM vm, ChoiceGenerator<?> processedCG) {
        System.out.println("choiceGeneratorProcessed: at " + processedCG.getInsn().getMethodInfo() + "#" + processedCG.getInsn().getPosition());
    }

    private DynamicRegion runVeritesting(ThreadInfo ti, Instruction instructionToExecute, StaticRegion staticRegion,
                                         String key) throws Exception {
        Exception transformationException = null;
        System.out.println("\n---------- STARTING Transformations for conditional region: " + key +
                "\n" + PrettyPrintVisitor.print(staticRegion.staticStmt) + "\n");
        staticRegion.slotParamTable.print();
        staticRegion.inputTable.print();
        staticRegion.outputTable.print();
        staticRegion.varTypeTable.print();

        /*-------------- EARLY RETURN TRANSFORMATION ---------------*/
        if (runMode == VeritestingMode.EARLYRETURNS) {
            staticRegion = RemoveEarlyReturns.removeEarlyReturns(staticRegion);
        }

        /*-------------- UNIQUENESS TRANSFORMATION ---------------*/
        DynamicRegion dynRegion = UniqueRegion.execute(staticRegion);

        boolean somethingChanged = true;
        FixedPointWrapper.resetWrapper();
        do {
            while (somethingChanged) {

                /*-------------- SUBSTITUTION & HIGH ORDER TRANSFORMATION ---------------*/
                /*--------------  FIELD TRANSFORMATION ---------------*/
                /*-------------- ARRAY TRANSFORMATION TRANSFORMATION ---------------*/
                dynRegion = FixedPointWrapper.executeFixedPointTransformations(ti, dynRegion);
                somethingChanged = FixedPointWrapper.isChangedFlag();

                if (!performanceMode)
                    assert (FixedPointWrapper.isChangedFlag() == !FixedPointWrapper.isEqualRegion());
            }
            /*-------------- HIGH ORDER TRANSFORMATION ---------------*/
            dynRegion = FixedPointWrapper.executeFixedPointHighOrder(ti, dynRegion);
            somethingChanged = FixedPointWrapper.isChangedFlag();
            transformationException = FixedPointWrapper.getFirstException();
            assert (FixedPointWrapper.isChangedFlag() == !FixedPointWrapper.isEqualRegion());
        }
        while (somethingChanged);


        if (transformationException != null) throw transformationException;

        TypePropagationVisitor.propagateTypes(dynRegion);

        dynRegion = UniqueRegion.execute(dynRegion);

        if (simplify) {
            Iterator<Map.Entry<Variable, Expression>> itr = dynRegion.constantsTable.table.entrySet().iterator();
        /*
        ArrayRefVarExpr, FieldRefVarExpr, WalaVarExpr should be unique at this point because UniqueRegion should have
        handled it
         */
            while (itr.hasNext()) {
                Map.Entry<Variable, Expression> entry = itr.next();
                if (entry.getKey() instanceof FieldRefVarExpr)
                    assert ((FieldRefVarExpr) entry.getKey()).uniqueNum != -1;
                if (entry.getKey() instanceof WalaVarExpr) assert ((WalaVarExpr) entry.getKey()).getUniqueNum() != -1;
                if (entry.getKey() instanceof ArrayRefVarExpr)
                    assert ((ArrayRefVarExpr) entry.getKey()).uniqueNum != -1;
            }
        }
        RegionMetricsVisitor.execute(dynRegion);

        if ((runMode.ordinal()) >= (VeritestingMode.SPFCASES.ordinal())) {

            /*-------------- SPFCases TRANSFORMATION 1ST PASS ---------------*/
            dynRegion = SpfCasesPass1Visitor.execute(ti, dynRegion,
                    runMode.ordinal() < VeritestingMode.EARLYRETURNS.ordinal() ?
                            new ArrayList(Arrays.asList(THROWINSTRUCTION, NEWINSTRUCTION, ARRAYINSTRUCTION, INVOKE)) : null);

            /*-------------- SPFCases TRANSFORMATION 1ST PASS ---------------*/
            dynRegion = SpfCasesPass2Visitor.execute(dynRegion);
        }
        /*--------------- LINEARIZATION TRANSFORMATION ---------------*/
        LinearizationTransformation linearTrans = new LinearizationTransformation();
        dynRegion = linearTrans.execute(dynRegion);

        /*--------------- Discover Lustre Translation ---------------*/
        if(contractDiscoveryOn)
            DiscoverContract.discoverLusterContract(dynRegion);

        /*--------------- TO GREEN TRANSFORMATION ---------------*/
        dynRegion = AstToGreenVisitor.execute(dynRegion);

        if ((runMode.ordinal()) >= (VeritestingMode.SPFCASES.ordinal())) {
            SpfToGreenVisitor visitor = new SpfToGreenVisitor();
            dynRegion = visitor.execute(dynRegion);
        }
        return dynRegion;
    }

    /**
     * This populates the Output of the summarized region to SPF.
     *
     * @param ti        Currently running thread.
     * @param ins       Branch instruction that indicates beginning of the region.
     * @param dynRegion Dynamic region that has been summarized.
     * @throws StaticRegionException Exception to indicate a problem while setting SPF.
     */

    public static Instruction setupSPF(ThreadInfo ti, Instruction ins, DynamicRegion dynRegion, Integer choice) throws StaticRegionException {
        if (canSetPC(ti, dynRegion, choice)) {
            populateFieldOutputs(ti, dynRegion);
            populateArrayOutputs(ti, dynRegion);
            populateSlots(ti, dynRegion);
            clearStack(ti.getTopFrame(), ins);

            if (choice != null && choice == RETURN_CHOICE && VeritestingListener.runMode == VeritestingMode.EARLYRETURNS) {//we are setting up an early return choice.
                pushReturnOnStack(ti.getTopFrame(), dynRegion);
            }
            if (dynRegion.stackOutput != null) {
//                dynRegion.stackOutput = (WalaVarExpr) (new ExprVisitorAdapter(new WalaVarToSPFVarVisitor(dynRegion.varTypeTable))).accept(dynRegion.stackOutput);
                pushExpOnStack(dynRegion, ti.getTopFrame(), (String) dynRegion.varTypeTable.lookup(dynRegion.stackOutput),
                        dynRegion.stackOutput);
            }
            return advanceSpf(ins, dynRegion, choice != null && choice == RETURN_CHOICE);

        }
        assert ti.getVM().getSystemState().isIgnored();
        return ins.getNext();
    }

    private static void pushReturnOnStack(StackFrame sf, DynamicRegion dynRegion) throws StaticRegionException {
        String returnType = dynRegion.earlyReturnResult.retPosAndType.getSecond();
        Expression returnVar = dynRegion.earlyReturnResult.retVar;
        pushExpOnStack(dynRegion, sf, returnType, returnVar);
    }

    private static void pushExpOnStack(DynamicRegion dynRegion, StackFrame sf, String returnType, Expression var)
            throws StaticRegionException {
        if (simplify && dynRegion.constantsTable != null) { //only handling the case of ints
            if (isConstant(dynRegion.constantsTable.lookup((Variable) var))) {
                var = dynRegion.constantsTable.lookup((Variable) var);
                returnType = getConstantType(var);
            }
        }
        boolean isConst = isConstant(var);
        if (returnType != null) {
            switch (returnType) {
                case "double":
                    if (isConst) sf.pushDouble(((RealConstant) var).getValue());
                    else sf.pushDouble(0);
                    break;
                case "float":
                    if (isConst) sf.pushFloat((float) ((RealConstant) var).getValue());
                    else sf.pushFloat(0);
                    break;
                case "long":
                    if (isConst) sf.pushLong(((IntConstant) var).getValue());
                    else sf.pushLong(0);
                    break;
                case "int":
                case "short":
                case "boolean":
                default: //assume int for now
                    if (isConst) sf.push(((IntConstant) var).getValue());
                    else sf.push(0);
                    break;
            }
            if (!isConst) {
                if (var instanceof WalaVarExpr) {
                    WalaVarToSPFVarVisitor walaVarVisitor = new WalaVarToSPFVarVisitor(dynRegion.varTypeTable);
                    ExprVisitorAdapter eva1 = new ExprVisitorAdapter(walaVarVisitor);
                    var = (Expression) eva1.accept(var);
                }
                sf.setOperandAttr(greenToSPFExpression(var));
            }
        } else {
            throw new StaticRegionException("Unknown type of expression to be pushed on the stack");
        }
    }

    /**
     * This method checks that the current PathCondition and after appending the summarized region is satisfiable.
     *
     * @param ti            Currently running thread.
     * @param dynRegion Finaly summary of the region, after all transformations has been successfully completed.
     * @return PathCondition is still satisfiable or not.
     * @throws StaticRegionException Exception to indicate a problem while checking SAT of the updated PathCondition.
     */
    private static boolean canSetPC(ThreadInfo ti, DynamicRegion dynRegion, Integer choice) throws StaticRegionException {
        PathCondition pc;
        PCChoiceGenerator currCG;

        if (ti.getVM().getSystemState().getChoiceGenerator() instanceof PCChoiceGenerator) {
            currCG = (PCChoiceGenerator) ti.getVM().getSystemState().getChoiceGenerator();
        } else {
            currCG = ti.getVM().getLastChoiceGeneratorOfType(PCChoiceGenerator.class);
        }
        if (currCG == null) throw new StaticRegionException("Cannot find latest PCChoiceGenerator");
        pc = currCG.getCurrentPC();
        if (runMode.ordinal() < VeritestingMode.SPFCASES.ordinal()) //only add region summary in non spfcases mode.
            pc._addDet(new GreenConstraint(dynRegion.regionSummary));

        // if we're trying to run fast, then assume that the region summary is satisfiable in any non-SPFCASES mode or
        // if the static choice is the only feasible choice.
        boolean cond1 =performanceMode && (runMode == VeritestingMode.VERITESTING ||
                runMode == VeritestingMode.HIGHORDER ||
                (choice != null && choice == STATIC_CHOICE && isOnlyStaticChoiceSat(dynRegion)));
        if ( cond1 || isPCSat(pc)) {
            currCG.setCurrentPC(pc);
            long t1 = System.nanoTime();
            // if we're running in incremental solving mode, then we need to ask this region summary to be
            // communicated to the solver right away instead of waiting for it to happen in
            // the PathCondition.simplify() control flow.
            maybeParseConstraint(pc);
            regionSummaryParseTime += (System.nanoTime() - t1);
            return true;
        } else {
            if (runMode.ordinal() >= VeritestingMode.SPFCASES.ordinal()) // this is where we ignore populating the output of the static choice
                ti.getVM().getSystemState().setIgnored(true); //to ignore counting of the current choice generator.
            return false;
        }
    }


    /**
     * This pop up operands of the if instruction that begins the region.
     *
     * @param sf  Current StackFrame.
     * @param ins Current executing instruction
     * @throws StaticRegionException Exception to indicate a problem while clearning the stack.
     */

    private static void clearStack(StackFrame sf, Instruction ins) throws StaticRegionException {
        int numOperands = SpfUtil.getOperandNumber(ins.getMnemonic());
        while (numOperands > 0) {
            sf.pop();
            numOperands--;
        }
    }


    //TODO: I need to use the wala name not number here.

    /**
     * Populates SPF stack slot with the output of the veritesting region.
     *
     * @param ti        Current executing thread.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    private static void populateSlots(ThreadInfo ti, DynamicRegion dynRegion) {
        StackFrame sf = ti.getModifiableTopFrame();
        DynamicOutputTable dynOutputTable = dynRegion.outputTable;
        List<Integer> slots = dynOutputTable.getKeys();

        Iterator slotItr = slots.iterator();

        while (slotItr.hasNext()) {
            Integer slot = (Integer) slotItr.next();
            Variable var = dynOutputTable.lookup(slot);
            assert (var instanceof WalaVarExpr);
            Expression symVar;
            if (simplify && dynRegion.constantsTable.lookup(var) != null) {
                symVar = dynRegion.constantsTable.lookup(var);
                if (symVar instanceof CloneableVariable)
                    symVar = createGreenVar((String) dynRegion.varTypeTable.lookup(var), symVar.toString()); // assumes toString() would return the same string as getSymName()
            } else
                symVar = createGreenVar((String) dynRegion.varTypeTable.lookup(var), ((WalaVarExpr) var).getSymName());
            //TODO: Dont write a local output as a symbolic expression attribute if it is a constant
            sf.setSlotAttr(slot, greenToSPFExpression(symVar));
        }
    }

    private static void populateFieldOutputs(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
        Iterator itr = dynRegion.psm.getUniqueFieldAccess().iterator();
        while (itr.hasNext()) {
            FieldRefVarExpr expr = (FieldRefVarExpr) itr.next();
            String type = dynRegion.fieldRefTypeTable.lookup(expr);
            Expression symVar;
            if (dynRegion.constantsTable != null && dynRegion.constantsTable.lookup(expr) != null) {
                symVar = dynRegion.constantsTable.lookup(expr);
                if (symVar instanceof CloneableVariable)
                    symVar = createGreenVar(type, symVar.toString()); // assumes toString() would return the same string as getSymName()
            } else symVar = createGreenVar(type, expr.getSymName());
            new SubstituteGetOutput(ti, expr.fieldRef, false, greenToSPFExpression(symVar)).invoke();
        }
    }

    private static void populateArrayOutputs(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {
//        Iterator itr = dynRegion.arrayPSM.getUniqueArrayAccess().iterator();
//        while (itr.hasNext()) {
//            ArrayRefVarExpr expr = (ArrayRefVarExpr) itr.next();
//            Expression symVar = createGreenVar(dynRegion.fieldRefTypeTable.lookup(expr), expr.getSymName());
//            doArrayStore(ti, expr, symVar, dynRegion.fieldRefTypeTable.lookup(expr));
//        }
        doArrayStore(ti, dynRegion.arrayOutputs, dynRegion.constantsTable);
    }

    /**
     * Steps SPF to the end of the region.
     *
     * @param ins       Insturction to be executed.
     * @param dynRegion Dynamic region that has been successfully transformed and summarized.
     */
    public static Instruction advanceSpf(Instruction ins, DynamicRegion dynRegion, boolean earlyReturnSetup) {
        int endIns;
        if (!earlyReturnSetup) // going to first instruction after the region
            endIns = dynRegion.endIns;
        else //going to a return instruction
            endIns = dynRegion.earlyReturnResult.retPosAndType.getFirst();
        while (ins.getPosition() != endIns) {
            if (ins instanceof GOTO && (((GOTO) ins).getTarget().getPosition() <= endIns))
                ins = ((GOTO) ins).getTarget();
            else ins = ins.getNext();
        }
        // this hack used to go along with a corresponding hack in SpfUtil.isStackConsumingRegionEnd that would advance
        // SPF beyond a store at the end of the region. These hacks aren't needed anymore but I am keeping this code
        // around until a month or two has gone by after we've stopped seeing these issues (March 13, 2019)
//        if (ins.getMnemonic().contains("store")) {
//            ins = ins.getNext();
//            System.out.println("advancing beyond a store at end of region");
//            assert false; //too late to throw a StaticRegionException, region's outputs have already been written
//        }
        //ti.setNextPC(ins);
        return ins;
    }


    public void publishFinished(Publisher publisher) {
        long runEndTime = System.nanoTime();
        PrintWriter pw = publisher.getOut();
        publisher.publishTopicStart("VeritestingListener report:");
        long dynRunTime = (runEndTime - runStartTime) - (jitAnalysis ? JITAnalysis.staticAnalysisDur : staticAnalysisDur);

        writeRegionDigest();


        //pw.println(statisticManager.printAllRegionStatistics());
//        pw.println(statisticManager.printStaticAnalysisStatistics());
        pw.println(statisticManager.printAllExceptionStatistics());

        pw.println("\n/************************ Printing Time Decomposition Statistics *****************");
        pw.println("static analysis time = " + TimeUnit.NANOSECONDS.toMillis(jitAnalysis ? JITAnalysis.staticAnalysisDur : staticAnalysisDur) + " msec");
        pw.println("Veritesting Dyn Time = " + TimeUnit.NANOSECONDS.toMillis(dynRunTime) + " msec");
        pw.println("Veritesting fix-pint Time = " + TimeUnit.NANOSECONDS.toMillis(FixedPointWrapper.fixedPointTime) + " msec");

        pw.println("\n/************************ Printing Solver Statistics *****************");
        pw.println("Total Solver Queries Count = " + solverCount);
        pw.println("Total Solver Time = " + TimeUnit.NANOSECONDS.toMillis(totalSolverTime) + " msec");
        pw.println("Total Solver Parse Time = " + TimeUnit.NANOSECONDS.toMillis(parseTime) + " msec");
        pw.println("Region Summary Parse Time = " + TimeUnit.NANOSECONDS.toMillis(regionSummaryParseTime) + " msec");
        pw.println("Total Solver Clean up Time = " + TimeUnit.NANOSECONDS.toMillis(cleanupTime) + " msec");
        pw.println("PCSatSolverCount = " + StatisticManager.PCSatSolverCount);
        pw.println("PCSatSolverTime = " + TimeUnit.NANOSECONDS.toMillis(StatisticManager.PCSatSolverTime) + " msec");
        pw.println("Constant Propagation Time for PC sat. checks = " + TimeUnit.NANOSECONDS.toMillis(StatisticManager.constPropTime));
        pw.println("Array SPF Case count = " + StatisticManager.ArraySPFCaseCount);
        pw.println("If-removed count = " + StatisticManager.ifRemovedCount);

        pw.println(statisticManager.printAccumulativeStatistics());
        pw.println(statisticManager.printInstantiationStatistics());

        //SH: turning this off because it is not an interesting number to know, because it includes those regions that were concrete.
        //      pw.println("Total number of Distinct regions = " + statisticManager.regionCount());

        pw.println("Number of Veritested Regions Instances = " + veritestRegionCount);

        /* Begin added for equivalence checking */
        if (veritestRegionExpectedCount != -1) {
            pw.println("Expected Number of Veritested Regions Instances = " + veritestRegionExpectedCount);
            assert (veritestRegionCount >= veritestRegionExpectedCount);
        }
        pw.println(statisticManager.getDistinctVeriRegionKeys());
        /* End added for equivalence checking */


        assert veritestRegionCount == statisticManager.getSuccInstantiations();
        pw.println("Metrics Vector:");
        pw.println(getMetricsVector(dynRunTime));

        if (spfCasesHeuristicsOn)
            statisticManager.printHeuristicStatistics();
    }

    private void writeRegionDigest() {
        if (!performanceMode)
            if (printRegionDigest) {
                try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                        new FileOutputStream("../logs/regionDigest_" + regionDigestPrintName), "utf-8"))) {
                    writer.write(regionDigest.toString());
                } catch (Exception e) {
                    System.out.println("problem writing regionDigest out.");
                }
                if (jitAnalysis) {
                    System.out.println("printing methods attempted for jitAnalysis\n");
                    System.out.println(JITAnalysis.getAttemptedMethods());
                } else {
                    System.out.println("printing methods attempted for Static Analysis\n");
                    System.out.println(VeritestingMain.getAttemptedMethods());
                }
            }
    }

    private String getMetricsVector(long dynRunTime) {
        return (TimeUnit.NANOSECONDS.toMillis((jitAnalysis ? JITAnalysis.staticAnalysisDur : staticAnalysisDur)) + TimeUnit.NANOSECONDS.toMillis(dynRunTime)) + "," +
                TimeUnit.NANOSECONDS.toMillis(jitAnalysis ? JITAnalysis.staticAnalysisDur : staticAnalysisDur) + "," +
                TimeUnit.NANOSECONDS.toMillis(dynRunTime) + "," +
                npaths + "," +
                solverCount + "," +
                TimeUnit.NANOSECONDS.toMillis(totalSolverTime) + "," +
                TimeUnit.NANOSECONDS.toMillis(parseTime) + "," +
                TimeUnit.NANOSECONDS.toMillis(cleanupTime) + "," +
                statisticManager.getDistinctVeriRegionNum() + "," +
                statisticManager.getDistinctSpfRegionNum() + "," +
                statisticManager.getConcreteRegionNum() + "," +
                statisticManager.getFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION) + "," +
                statisticManager.getFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION) + "," +
                statisticManager.getFailNum(FailEntry.FailReason.MISSINGMETHODSUMMARY) + "," +
                statisticManager.getFailNum(FailEntry.FailReason.OTHER) + "," +
                hgOrdRegionInstance + "," +
                statisticManager.regionCount() + "," +
//                veritestRegionCount + "," + // this number also reports the total number of successful instantiations
                // instantiation metrics
                statisticManager.getSuccInstantiations() + "," + statisticManager.getFailedInstantiations() + "," +
                statisticManager.getConcreteInstNum() + "," +
                statisticManager.getInstFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION) + "," +
                statisticManager.getInstFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION) + "," +
                statisticManager.getInstFailNum(FailEntry.FailReason.MISSINGMETHODSUMMARY) + "," +
                statisticManager.getInstFailNum(FailEntry.FailReason.OTHER) + "," +
                // static analysis metrics
                interestingRegionCount + "," + numMethodSummaries + "," + maxBranchDepth + "," + maxExecPathCount + "," + avgExecPathCount + "," +
                // exception metrics
                staticPhaseEx + "," + instPhaseEx + "," + unknownPhaseEx;
    }
}
