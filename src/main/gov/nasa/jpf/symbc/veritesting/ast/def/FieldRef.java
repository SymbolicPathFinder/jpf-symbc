package gov.nasa.jpf.symbc.veritesting.ast.def;

import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.types.TypeName;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.vm.ThreadInfo;
import org.apache.bcel.classfile.Utility;
import za.ac.sun.cs.green.expr.IntConstant;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils.getType;

/**
 * This class is used to represent field-reference pair that is used in RangerIR to provide SSA for fields.
 */

public class FieldRef {
    public final int ref;
    public final String field;
    public final boolean isStatic;
    public final String className;


    public FieldRef(int ref, String className, String field, boolean isStatic) {
        this.ref = ref;
        this.field = field;
        this.isStatic = isStatic;
        this.className = className;
    }

    public static FieldRef makeGetFieldRef(ThreadInfo ti, GetInstruction getIns) throws StaticRegionException {
        if (!(getIns.ref instanceof IntConstant) && !getIns.getOriginal().isStatic())
            throwException(new IllegalArgumentException("cannot make FieldRef for symbolic object reference"), INSTANTIATION);
        // getIns.ref contains object reference whereas putIns.def contains object reference
        int ref = getIns.getOriginal().isStatic() ? -1 : ((IntConstant)getIns.ref).getValue();
        if (ref == 0) throwException(new StaticRegionException("Cannot get any information from null objects"), INSTANTIATION);
        String fieldName = getIns.field.getName().toString();
        String className = getIns.getOriginal().isStatic() ?
                getIns.field.getDeclaringClass().getName().getClassName().toString():
                ti.getClassInfo(ref).getName();
        TypeName typeName = getIns.field.getDeclaringClass().getName();
        if (typeName.isPrimitiveType()) throwException(new IllegalArgumentException("cannot make FieldRef for primitive object type in FieldRef.makeGetFieldRef"), INSTANTIATION);
        else {
            className = getType(typeName);
        }
        return new FieldRef(ref, className, fieldName, getIns.getOriginal().isStatic());
    }

    public static FieldRef makePutFieldRef(ThreadInfo ti, PutInstruction putIns) throws StaticRegionException {
        if (!(putIns.def instanceof IntConstant)&& !putIns.getOriginal().isStatic())
            throwException(new IllegalArgumentException("cannot make FieldRef for symbolic object reference"), INSTANTIATION);
        int ref = putIns.getOriginal().isStatic() ? -1 : ((IntConstant)putIns.def).getValue();
        if (ref == 0) throwException(new StaticRegionException("Cannot get any information from null objects"), INSTANTIATION);
        String fieldName = putIns.field.getName().toString();
        String className = putIns.getOriginal().isStatic() ?
                putIns.field.getDeclaringClass().getName().getClassName().toString():
                ti.getClassInfo(ref).getName();
        TypeName typeName = putIns.field.getDeclaringClass().getName();
        if (typeName.isPrimitiveType()) throwException(new IllegalArgumentException("cannot make FieldRef for primitive object type in FieldRef.makePutFieldRef"), INSTANTIATION);
        else {
            className = getType(typeName);
        }
        return new FieldRef(ref, className, fieldName, putIns.getOriginal().isStatic());
    }

    public String getField() {
        return field;
    }

    public int getRef() {
        return ref;
    }

    @Override
    public String toString() {
        return ref+",  "+field;
    }

    @Override
    public boolean equals(Object obj) {
        if (FieldRef.class.isInstance(obj)) {
            FieldRef f = (FieldRef) obj;
            return ref == f.ref && field.equals(f.field);
        }
        else return false;
    }

    @Override
    protected FieldRef clone() {
        return new FieldRef(ref, className, field, isStatic);
    }
}
