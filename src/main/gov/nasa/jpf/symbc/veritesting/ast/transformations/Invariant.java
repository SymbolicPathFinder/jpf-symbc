package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;

/**
 * An interface for checking invariants of every transformation.
 */
public interface Invariant {
    public void checkInvariant(Region region) throws StaticRegionException;
    public String getName();
}
