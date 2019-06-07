package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.Region;

import java.util.Set;


/*
    A Transformation describes a transformation and the set of invariants that
    are expected to hold prior to and after its occurrence.

    Because some passes define invariants that hold thereafter, we "carry" a set of
    invariants forward unless they are explicitly removed by another pass.  The
    execute function allows such manipulation of the set of invariants for future passes.

    The getName() function exists so that it is possible to log information about
    the execution of the system.

    Given this common interface, it is possible to batch up transformations into
    composite transformations, easily perform fixpointing computations (if the
    AST has appropriate definitions for equality - this is TODO!!!!).

    This is a slightly richer interface than would be ideal, but transformation
    writers can choose to ignore the invariant check parts.
 */

/**
 * A Transformation describes a transformation and the set of invariants that are expected to hold prior to and after its occurrence.
 */
public interface Transformation {
    public TransformationData execute(TransformationData data) throws StaticRegionException;
    public String getName();
}
