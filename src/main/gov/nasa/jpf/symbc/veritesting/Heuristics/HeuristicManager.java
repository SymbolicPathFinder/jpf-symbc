package gov.nasa.jpf.symbc.veritesting.Heuristics;

import gov.nasa.jpf.symbc.veritesting.ChoiceGenerator.StaticBranchChoiceGenerator;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.RegionHitExactHeuristic;
import gov.nasa.jpf.vm.bytecode.ReturnInstruction;

import java.util.ArrayList;
import java.util.Formatter;

import static gov.nasa.jpf.symbc.VeritestingListener.performanceMode;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.RegionHitExactHeuristic.formatString;


public class HeuristicManager {


    /**
     * used to collect all regions that we hit along with the number of paths that SPF had to explore through it.
     * An invariant here is that the last added element is the element that we wish to count its paths, if we are still
     * in the heuristic choices.
     */
    private static ArrayList<RegionHitExactHeuristic> regionHitExactHeuristicArray = new ArrayList<>();


    public static boolean addRegionExactHeuristic(RegionHitExactHeuristic newRegionHitExactHeuristic) {
       /* for (RegionHitExactHeuristic regionHitExactHeuristic : regionHitExactHeuristicArray) {
            if (regionHitExactHeuristic.getRegionKey().equals(newRegionHitExactHeuristic.getRegionKey()))
                return false; //do not recreate heursitics for regions we already created.
        }*/
       if (performanceMode) regionHitExactHeuristicArray.clear();
       regionHitExactHeuristicArray.add(newRegionHitExactHeuristic);
       return true;
    }

    public static PathStatus incrementRegionExactHeuristicCount(gov.nasa.jpf.vm.Instruction instructionToExecute) {
        RegionHitExactHeuristic regionHeuristic = HeuristicManager.getRegionHeuristic();
        if (regionHeuristic.getRegionStatus()) {
            assert (StaticBranchChoiceGenerator.heuristicsCountingMode);
            if (instructionToExecute.toString().equals(regionHeuristic.getTargetInstruction().toString())
                    || (instructionToExecute instanceof ReturnInstruction && instructionToExecute.getMethodInfo()
                    .equals(regionHeuristic.getMethodInfo())))
            {// do the
                // check
                // for the return
                // instructions that lay only inside the region, not for example a return from another hight order
                // region
                regionHeuristic.incrementPathCount();
                return PathStatus.ENDREACHED; //returns true if we are trying to count paths, whether we hit end
                // instruction or return instruction
            }
            return PathStatus.INHEURISTIC;
        }
        return PathStatus.OUTHEURISTIC;
    }

    public static void regionHeuristicFinished(String key) {
        RegionHitExactHeuristic regionHeuristic = regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
        if (!key.equals(regionHeuristic.getRegionKey())) {
            System.out.println("unexpected region for heuristics.");
            assert false;
        }

        if (!regionHeuristic.getRegionStatus()) {
            System.out.println("expecting region heuristic in 'active status'!");
            assert false;
        }
        regionHeuristic.setActiveState(false);
    }

    public static boolean getRegionHeuristicStatus(String key) {
        RegionHitExactHeuristic regionHeuristic = regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
        if (!key.equals(regionHeuristic.getRegionKey())) {
            System.out.println("unexpected region for heuristics.");
            assert false;
        }
        return regionHeuristic.getRegionStatus();
    }

    public static String getLastRegionKey() {
        RegionHitExactHeuristic regionHeuristic = regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
        return regionHeuristic.getRegionKey();
    }


    public static RegionHitExactHeuristic getRegionHeuristic() {
        assert (regionHitExactHeuristicArray.size() != 0);
        return regionHitExactHeuristicArray.get(regionHitExactHeuristicArray.size() - 1);
    }

    public static void printStatistics() {
//        System.out.println("RegionKey" + heurTabStr + heurTabStr + "TargetInstruction" + heurTabStr + "ActiveStatus" + heurTabStr + "PathCount");
        Formatter f = new Formatter();
        f.format(formatString,"RegionKey" , "TargetInstruction" , "ActiveStatus" , "PathCount" , "EstimatedPathCount");
        System.out.println(f.toString());
        for (RegionHitExactHeuristic regionHeuristic : regionHitExactHeuristicArray) {
            System.out.println(regionHeuristic.toString());
        }
    }

    public static int getRegionHeuristicSize() {
        return regionHitExactHeuristicArray.size();
    }
}
