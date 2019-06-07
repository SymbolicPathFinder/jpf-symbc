package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.symbc.veritesting.Heuristics.HeuristicManager;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingMain;
import gov.nasa.jpf.symbc.veritesting.ast.def.Instruction;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;

import java.lang.management.ThreadInfo;
import java.util.*;

import static gov.nasa.jpf.symbc.VeritestingListener.interestingClassNames;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionMap;

public class StatisticManager {
    public static HashMap<String, RegionStatistics> regionsStatisticsMap = new HashMap<>();
    public static String instructionToExec;
    public static boolean veritestingRunning = false;
    public static int solverQueriesUnique = 0;
    public static boolean inializeQueriesFile = true;
    public static int hgOrdRegionInstance = 0;
    public static int PCSatSolverCount = 0;
    public static long PCSatSolverTime = 0;
    public static long constPropTime = 0;
    public static int ArraySPFCaseCount = 0;
    public static int ifRemovedCount = 0;
    public static int maxBranchDepth = -1;
    public static long maxExecPathCount = -1;
    public static double avgExecPathCount = 0.0;
    public static int numMethodSummaries = 0;
    public static int interestingRegionCount = 0;
    public static int staticPhaseEx = 0, instPhaseEx = 0, unknownPhaseEx = 0;
    public static int thisHighOrdCount = 0;


    public void printHeuristicStatistics() {
        System.out.println("\nPrinting Heuristic Statistics:\n");
        HeuristicManager.printStatistics();
    }

    public void updateVeriSuccForRegion(String key) {
        hgOrdRegionInstance += thisHighOrdCount;
        if (regionsStatisticsMap.get(key) != null) {
            RegionStatistics regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.veriHitNumber++;
        } else {
            RegionStatistics regionStatistics = new RegionStatistics(key, null, 1, 0, 0);
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }

    //updates the number of times we couldn't veritest a region and we left it for SPF to deal with it.
    public void updateSPFHitForRegion(String key, String failError) {
        RegionStatistics regionStatistics;
        if (regionsStatisticsMap.get(key) != null) {
            regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.spfHitNumber++;
        } else {
            regionStatistics = new RegionStatistics(key, null, 0, 1, 0);
            regionsStatisticsMap.put(key, regionStatistics);
        }

        if (failError.contains("FieldSSAVisitor")) {
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION, failError));
        } else if (failError.contains("not summarize invoke")) {
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.MISSINGMETHODSUMMARY, failError));
        } else if (failError.contains("new") || (failError.contains("throw")) || (failError.contains("arrayload")) || (failError.contains("arraystore"))) {
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.SPFCASEINSTRUCTION, failError));
        } else {
            regionStatistics.failReasonList.add(new FailEntry(FailEntry.FailReason.OTHER, failError));
        }
    }


    public void updateConcreteHitStatForRegion(String key) {
        RegionStatistics regionStatistics;
        if (regionsStatisticsMap.get(key) != null) {
            regionStatistics = regionsStatisticsMap.get(key);
            regionStatistics.concreteNumber++;
        } else {
            regionStatistics = new RegionStatistics(key, null, 0, 0, 1);
            regionsStatisticsMap.put(key, regionStatistics);
        }
    }


    public String printAllRegionStatistics() {
        StringBuilder out = new StringBuilder("\n/************************ Printing Regions Statistics *****************\n" +
                "veriHitNumber: number of times a region was successfully veritested\n" +
                "spfHitNumber: number of times we were not able to veritest a region and we left it to SPF (this is counting failures due to statements in the region we couldn't summaries.)\n" +
                "concreteHit: number of times a region was not veritested because of the condition\n");

        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            out.append(regionsStatisticsMap.get(keysItr.next()).print());
        out.append("\n").append(getDistinctVeriRegionKeys());
        return out.toString();
    }

    public String printAllExceptionStatistics() {
        String first = "\n/************************ Printing Exception Statistics *****************\n";

        Set<String> keys = ExceptionMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        String out = new String();
        while (keysItr.hasNext()) {
            String message = keysItr.next();
            Pair<Integer, StaticRegionException.ExceptionPhase> p = ExceptionMap.get(message);
            out += message + ": (" + p.getFirst() + ", " + p.getSecond() + ")" + "\n";
            switch (p.getSecond()) {
                case STATIC:
                    staticPhaseEx += p.getFirst();
                    break;
                case INSTANTIATION:
                    instPhaseEx += p.getFirst();
                    break;
                case DONTKNOW:
                    unknownPhaseEx += p.getFirst();
                    break;
                default:
                    throw new IllegalArgumentException("cannot have exceptions that aren't static or instantiation-time");
            }
        }
        String ret = first + "Static Analysis exceptions count = " + staticPhaseEx +
                "\nInstantiation Time exceptions count = " + instPhaseEx +
                "\nUnknown phases exception count = " + unknownPhaseEx + "\n" + out;
        return ret;
    }

    public String printAccumulativeStatistics() {
        String out = "\n/************************ Printing Region Statistics *****************\n" +
                "Number of Distinct Veritested Regions = " + getDistinctVeriRegionNum() + "\nNumber of Distinct Un-Veritested Symbolic Regions = " + getDistinctSpfRegionNum()
                //  + "\nNumber of Distinct Un-Veritested Concrete Regions = "+ getConcreteRegionNum()
                + "\nNumber of Distinct Failed Regions for Field Reference = " + getFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for SPFCases = " + getFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION)
                + "\nNumber of Distinct Failed Regions for missing method summaries = " + getFailNum(FailEntry.FailReason.MISSINGMETHODSUMMARY)
                + "\nNumber of Distinct Failed Regions for Other Reasons = " + getFailNum(FailEntry.FailReason.OTHER)
                + "\nNumber of High Order Regions Used = " + hgOrdRegionInstance;
        return out;
    }

    public String printInstantiationStatistics() {
        String out = "\n/************************ Printing Instantiation Statistics *****************\n" +
                "Number of successful instantiations = " + getSuccInstantiations() +
                "\nTotal Number of unsuccessful instantiations = " + getFailedInstantiations()
                //+ "\nNumber of failed instantiations due to concrete condition = "+ getConcreteInstNum()
                + "\nNumber of failed instantiations due to Field Reference = " + getInstFailNum(FailEntry.FailReason.FIELDREFERNCEINSTRUCTION)
                + "\nNumber of failed instantiations due to SPFCases = " + getInstFailNum(FailEntry.FailReason.SPFCASEINSTRUCTION)
                + "\nNumber of failed instantiations due to missing method summaries = " + getInstFailNum(FailEntry.FailReason.MISSINGMETHODSUMMARY)
                + "\nNumber of failed instantiations due to Other Reasons = " + getInstFailNum(FailEntry.FailReason.OTHER) + "\n\n";
        return out;
    }

    public String printStaticAnalysisStatistics() {
        ArrayList<String> out = new ArrayList<>();
        StringBuilder ret = new StringBuilder();
        Iterator<Map.Entry<String, StaticRegion>> itr = VeritestingMain.veriRegions.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, StaticRegion> entry = itr.next();
            String key = entry.getKey();
//            if (!isInterestingRegion(key)) continue;
            StaticRegion region = entry.getValue();
            out.add(key + ": maxDepth = " + region.maxDepth + ", execution path count = " + region.totalNumPaths + "\n");
        }
        Collections.sort(out);
        String first = "\n/************************ Printing Static Analysis statistics *****************\n" +
                "Total Number of summarized regions = " + VeritestingMain.veriRegions.size()
                + "\nNumber of interesting regions = " + interestingRegionCount + " (uses interestingClassNames JPF config. option)"
                + "\nNumber of summarized interesting methods = " + numMethodSummaries
                + "\nOverall maximum branch depth for interesting regions = " + maxBranchDepth
                + "\nMaximum execution path count for interesting regions = " + maxExecPathCount
                + "\nAvg. execution path count for interesting regions = " + avgExecPathCount + "\n";
        out.add(0, first);
        for (String s : out) {
            ret.append(s);
        }
        return ret.toString();
    }

    public int getDistinctVeriRegionNum() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).veriHitNumber != 0)
                ++count;
        return count;
    }

    public String getDistinctVeriRegionKeys() {
        String ret = "";
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();
        ArrayList<String> out = new ArrayList<>();

        while (keysItr.hasNext()) {
            String key = keysItr.next();
            if (regionsStatisticsMap.get(key).veriHitNumber != 0)
                out.add(regionsStatisticsMap.get(key).regionKey + "\n");
        }
        Collections.sort(out);
        out.add(0, "Printing keys of regions that were instantiated at least once\n");
        out.add(out.size(), "Finished printing keys of regions that were instantiated at least once\n");
        for (String s : out) {
            ret += s;
        }
        return ret;
    }

    public int getSuccInstantiations() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            count += regionsStatisticsMap.get(keysItr.next()).veriHitNumber;
        return count;
    }

    public int getDistinctSpfRegionNum() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).spfHitNumber != 0)
                ++count;
        return count;
    }

    public int getFailedInstantiations() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            count += regionsStatisticsMap.get(keysItr.next()).spfHitNumber;
        return count;
    }

    public int getConcreteRegionNum() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            if (regionsStatisticsMap.get(keysItr.next()).concreteNumber != 0)
                ++count;
        return count;
    }

    public int getConcreteInstNum() {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        while (keysItr.hasNext())
            count += regionsStatisticsMap.get(keysItr.next()).concreteNumber;
        return count;
    }

    public int getFailNum(FailEntry.FailReason failReason) {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        ArrayList<FailEntry> failReasonList;
        while (keysItr.hasNext()) {
            failReasonList = regionsStatisticsMap.get(keysItr.next()).failReasonList;
            Iterator<FailEntry> failItr = failReasonList.iterator();
            Boolean failNotFound = true;
            while (failItr.hasNext() && failNotFound) {
                FailEntry entry = failItr.next();
                if (entry.failReason == failReason) {
                    ++count;
                    failNotFound = false;
                }
            }
        }
        return count;
    }

    public int getInstFailNum(FailEntry.FailReason failReason) {
        int count = 0;
        Set<String> keys = regionsStatisticsMap.keySet();
        Iterator<String> keysItr = keys.iterator();

        ArrayList<FailEntry> failReasonList;
        while (keysItr.hasNext()) {
            failReasonList = regionsStatisticsMap.get(keysItr.next()).failReasonList;
            Iterator<FailEntry> failItr = failReasonList.iterator();
            while (failItr.hasNext()) {
                FailEntry entry = failItr.next();
                if (entry.failReason == failReason) {
                    ++count;
                }
            }
        }
        return count;
    }


    public int regionCount() {
        return regionsStatisticsMap.size();
    }

    public void collectStaticAnalysisMetrics(HashMap<String, StaticRegion> veriRegions) {
        Iterator<Map.Entry<String, StaticRegion>> itr = veriRegions.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, StaticRegion> entry = itr.next();
            String key = entry.getKey();
            if (!isInterestingRegion(key)) continue;
            interestingRegionCount++;
            StaticRegion region = entry.getValue();
            if (region.maxDepth > this.maxBranchDepth)
                maxBranchDepth = region.maxDepth;
            if (region.totalNumPaths > maxExecPathCount)
                maxExecPathCount = region.totalNumPaths;
            avgExecPathCount += region.totalNumPaths;
            numMethodSummaries += (region.isMethodRegion ? 1 : 0);
        }
        avgExecPathCount /= veriRegions.size();
    }

    private boolean isInterestingRegion(String key) {
        if (interestingClassNames == null) return true;
        for (String className : interestingClassNames)
            if (key.toLowerCase().contains(className.toLowerCase())) return true;
        return false;
    }
}
