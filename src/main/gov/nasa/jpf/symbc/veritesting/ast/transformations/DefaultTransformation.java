package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;

import java.util.Set;

/**
 * Abstract class that defines transformation execution and then checking its invariants.
 */
public abstract class DefaultTransformation implements Transformation {

    @Override
    public TransformationData execute(TransformationData data) throws StaticRegionException {
        data.checkInvariants();
        DynamicRegion r = execute(data.region);
        Set<Invariant> i = updateInvariants(data.invariants);
        return new TransformationData(r, i, data.runInvariants);
    }

    public abstract DynamicRegion execute(DynamicRegion region);

    // default behavior is to leave invariants unchanged.
    public Set<Invariant> updateInvariants(Set<Invariant> invariants) {
        return invariants;
    }

    @Override
    public String getName() {
        return null;
    }
}
