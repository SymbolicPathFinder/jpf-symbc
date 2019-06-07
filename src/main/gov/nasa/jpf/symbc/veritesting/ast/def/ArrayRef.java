package gov.nasa.jpf.symbc.veritesting.ast.def;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import za.ac.sun.cs.green.expr.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

public class ArrayRef {
    public final int ref;
    public final Expression index;

    public ArrayRef(int ref, Expression index) {
        this.ref = ref;
        this.index = index;
    }

    public static ArrayRef makeArrayRef(ArrayLoadInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throwException(new IllegalArgumentException("cannot make ArrayRef for symbolic array reference"), INSTANTIATION);
        int ref = ((IntConstant)getIns.arrayref).getValue();
        Expression indexName = getIns.index;
        return new ArrayRef(ref, indexName);
    }

    public static ArrayRef makeArrayRef(ArrayStoreInstruction getIns) {
        if (!(getIns.arrayref instanceof IntConstant))
            throwException(new IllegalArgumentException("cannot make ArrayRef for symbolic array reference"), INSTANTIATION);
        int ref = ((IntConstant)getIns.arrayref).getValue();
        Expression indexName = getIns.index;
        return new ArrayRef(ref, indexName);
    }

    public Expression getIndex() {
        return index;
    }

    public int getRef() {
        return ref;
    }

    @Override
    public String toString() {
        return ref+",  "+index;
    }

    @Override
    public boolean equals(Object obj) {
        if (ArrayRef.class.isInstance(obj)) {
            ArrayRef f = (ArrayRef) obj;
            return ref == f.ref && index.equals(f.index);
        }
        else return false;
    }

    @Override
    protected ArrayRef clone() {
        if (index instanceof IntVariable) {
            IntVariable i = (IntVariable) index;
            return new ArrayRef(ref, new IntVariable(i.getName(), i.getLowerBound(), i.getUpperBound()));
        }
        else if (index instanceof IntConstant) {
            return new ArrayRef(ref, new IntConstant(((IntConstant) index).getValue()));
        } else if (index instanceof WalaVarExpr) {
            return new ArrayRef(ref, ((WalaVarExpr)index).clone());
        }  else {
//            throwException(new IllegalArgumentException("Unsupported index type found when cloning ArrayRef"), INSTANTIATION);
//            return null;
            return new ArrayRef(ref, index);
        }
    }

    public static boolean looseArrayRefEquals(ArrayRef arrayRef, ArrayRef key) {
        if (arrayRef.ref == key.ref) {
            boolean bothIntConst = arrayRef.index instanceof IntConstant && key.index instanceof IntConstant;
            if (!bothIntConst || ((IntConstant) arrayRef.index).getValue() == ((IntConstant) key.index).getValue()) {
                return true;
            }
        }
        return false;
    }

}
