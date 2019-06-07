package gov.nasa.jpf.symbc.veritesting.ast.transformations;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.List;

/**
 * Used to iterate over all transformations, executes them and check their invariants after transformations.
 */
public class TransformationList implements Transformation {

    public final List<Transformation> transformations;
    public final String name;

    public TransformationList(List<Transformation> transformations, String name) {
        this.transformations = transformations;
        this.name = name;
    }

    public TransformationData execute(TransformationData data) throws StaticRegionException {
        for (Transformation t : transformations) {
            data = t.execute(data);
        }
        data.checkInvariants();
        return data;
    }

    @Override
    public String getName() {
        return name;
    }

}
