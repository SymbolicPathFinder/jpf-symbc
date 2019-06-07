package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import gov.nasa.jpf.vm.Instruction;
import gov.nasa.jpf.vm.MethodInfo;

import java.util.Formatter;


public class RegionHitExactHeuristic{
    String regionKey;
    Instruction targetInstruction;

    public MethodInfo getMethodInfo() {
        return methodInfo;
    }

    MethodInfo methodInfo;
    boolean active;

    public int getPathCount() {
        return pathCount;
    }

    int pathCount = 0;
    long estimatedPathCount = 0;

    public RegionHitExactHeuristic(String regionKey, Instruction targetInstruction, MethodInfo methodInfo, int
            pathCount) {
        this.regionKey = regionKey;
        this.targetInstruction = targetInstruction;
        this.methodInfo = methodInfo;
        this.pathCount = pathCount;
        active = true;
    }

    public boolean getRegionStatus() {
        return active;
    }

    public String getRegionKey() {
        return regionKey;
    }

    public Instruction getTargetInstruction() {
        return targetInstruction;
    }

    public void incrementPathCount() {
        ++pathCount;
    }

    public void setEstimatedPathCount(long c) { estimatedPathCount = c; }

    public boolean equal(RegionHitExactHeuristic regionHitExactHeuristic) {
        if (this.regionKey.equals(regionHitExactHeuristic.regionKey))
            return true;
        else
            return false;
    }

    public static final String formatString = "%-50s %-16.16s %-10.10s %-20.20s %-20.20s";
    public String toString(){
        Formatter f = new Formatter();
        f.format(formatString,regionKey , targetInstruction , active , pathCount , estimatedPathCount);
        return f.toString();
    }

    public String print(){
        return "regionKey = " + regionKey + ", targetInstruction = " + targetInstruction + ", active = " + active +
                ", pathcount = " + pathCount + ", estimatedPathCount = " + estimatedPathCount;
    }

    public void setActiveState(boolean state) {
        active = state;
    }
}


