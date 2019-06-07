package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingMain;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;
import gov.nasa.jpf.vm.ThreadInfo;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import static gov.nasa.jpf.symbc.VeritestingListener.statisticManager;


public class JITAnalysis {
    /**
     * keeps track of all classes we have seen for recovering of the IR
     */
    private static HashSet<String> attemptedClasses = new HashSet<>();

    /**
     * keeps track of all the methods we have seen for recovering the IR
     */
    private static HashSet<String> attemptedMehods = new HashSet<>();


    public static long staticAnalysisDur;
    private static boolean firstTime = true;
    private static ThreadInfo ti;
    private static Instruction instruction;
    private static VeritestingMain veritestingMain;


    /**
     * This is tries to discover statically all potential regions that could be used as veritesting regions.
     *
     * @param ti  Current running thread.
     * @param key
     */
    public static StaticRegion discoverRegions(ThreadInfo ti, Instruction instruction, String key) throws StaticRegionException {

        JITAnalysis.ti = ti;
        JITAnalysis.instruction = instruction;

        MethodInfo methodInfo = instruction.getMethodInfo();
        String className = methodInfo.getClassName();
        String jvmMethodName = methodInfo.getFullName();

        StaticRegion staticRegion = discoverAllClassAndGetRegion(className, jvmMethodName, key);

        statisticManager.collectStaticAnalysisMetrics(VeritestingMain.veriRegions);
        StaticRegionException.staticAnalysisComplete();
        return staticRegion;
    }

    public static StaticRegion discoverAllClassAndGetRegion(String className, String jvmMethodName, String key) throws StaticRegionException {

        long startTime = System.nanoTime();

        if (firstTime) { //create veritestingMain only once.
            System.out.println("^_^ running jitAnalysis ^_^");
            JITAnalysis.veritestingMain = new VeritestingMain(ti);
            firstTime = false;
        }
        ArrayList<String> classPath = new ArrayList<>();

        if (!attemptedClasses.contains(className) || (!attemptedMehods.contains(jvmMethodName))) { // need to run static analysis first
            attemptedClasses.add(className);
            attemptedMehods.add(jvmMethodName);
            //String className = conf.getString("target");
            classPath = getClassPaths();
            /*try {
                veritestingMain.jitAnalyzeForVeritesting(classPath, className, jvmMethodName, false);
            } catch (StaticRegionException sre) { // if failed while summarizing the method, try to summarize regions inside it.
                    System.out.println(sre);
            }*/
            try {
                veritestingMain.jitAnalyzeForVeritesting(classPath, className, jvmMethodName, false);
            } catch (StaticRegionException sre1) { // if failed while summarizing the method, try to summarize regions inside it.
                try {
                    veritestingMain.jitAnalyzeForVeritesting(classPath, className, jvmMethodName, true);
                } catch (StaticRegionException sre2) {
                    System.out.println(sre2);
                }
            }
        }

        HashMap<String, StaticRegion> regionsMap = VeritestingMain.veriRegions;
        StaticRegion staticRegion = regionsMap.get(key);

        long endTime = System.nanoTime();
        staticAnalysisDur += endTime - startTime;

        if (staticRegion == null) {
            //throw new StaticRegionException("Region " + key + " has no recovered static region");
            System.out.println("Region " + key + " has no recovered static region");
            return null;
        } else
            return staticRegion;
    }

    private static ArrayList<String> getClassPaths() {
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
        return classPath;
    }

    public static HashSet<String> getAttemptedMethods() {
        return attemptedMehods;
    }
}
