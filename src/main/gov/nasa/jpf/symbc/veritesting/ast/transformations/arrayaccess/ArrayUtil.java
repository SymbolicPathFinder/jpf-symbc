package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.GammaVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.*;

import java.util.Iterator;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.createGreenVar;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.greenToSPFExpression;
import static za.ac.sun.cs.green.expr.Operation.Operator.EQ;

public class ArrayUtil {
    public static Pair<Expression, String> getExpression(ThreadInfo ti, ArrayRef c, Pair<Expression[], String> valuesTypePair) {
        Pair<Expression, String> rhs;
        int len=getArrayLength(ti, c.ref); // assumed concrete
        assert len == valuesTypePair.getFirst().length;
        if (c.index instanceof IntConstant) {
            int index = ((IntConstant)c.index).getValue();
            if (index >= len) //TODO make this a SPF case in the future
                throwException(new IllegalArgumentException("Array index greater than or equal to array length"), INSTANTIATION);
            return new Pair<>(valuesTypePair.getFirst()[index], valuesTypePair.getSecond());
        } else { // the index is symbolic
            rhs = constructArrayITE(c.index, 0, valuesTypePair);
        }
        return rhs;
    }


    public static Pair<Expression, String> constructArrayITE(Expression indexExpression, int index,
                                         Pair<Expression[], String> valuesTypePair) {
        Expression[] values = valuesTypePair.getFirst();
        int len = values.length;
        String type = valuesTypePair.getSecond();
        if (index == len-1) return new Pair<>(values[index], type);
        else {
            Expression cond = new Operation(EQ, indexExpression, new IntConstant(index));
            Expression ite = constructArrayITE(indexExpression, index+1, valuesTypePair).getFirst();
            return new Pair<>(new GammaVarExpr(cond, values[index], ite), type);
        }
    }

    public static Pair<Expression, String> getArrayElement(ElementInfo ei, int index) {
        // copied from Soha's implementation of FillArrayLoadHoles in the previous veritesting implementation
        if(ei.getArrayType().equals("B")){
            return new Pair(getArrayElementInner(ei, index, "byte"), "byte"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("I")){
            return new Pair(getArrayElementInner(ei, index, "int"), "int"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("F")){
            return new Pair(getArrayElementInner(ei, index, "float"), "float"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("D")){
            return new Pair(getArrayElementInner(ei, index, "double"), "double"); //elements of the array are concrete
        } else if (ei.getArrayType().equals("C")) {
            return new Pair(getArrayElementInner(ei, index, "char"), "char"); //elements of the array are concrete
        } else if (ei.getClassInfo().isReferenceArray()) {
            return new Pair(getArrayElementInner(ei, index, "reference"), "int"); // elements of the array are concrete
        } else if (ei.getArrayType().equals("Z")) {
            return new Pair(getArrayElementInner(ei, index, "boolean"), "boolean"); // elements of the array are concrete
        } else {
            throwException(new IllegalArgumentException("Unsupported element type in array"), INSTANTIATION);
            return null;
        }
    }

    private static Expression getArrayElementInner(ElementInfo ei, int index, String type) {
        if (ei.getElementAttr(index) != null)
            return SPFToGreenExpr((gov.nasa.jpf.symbc.numeric.Expression)ei.getElementAttr(index));
        else
            return type.equals("float") ? new RealConstant(ei.getFloatElement(index)) :
                    type.equals("double") ? new RealConstant(ei.getDoubleElement(index)) :
                            type.equals("byte") ? new IntConstant(ei.getByteElement(index)) :
                                    type.equals("char") ? new IntConstant(ei.getCharElement(index)) :
                                            type.equals("int") ? new IntConstant(ei.getIntElement(index)) :
                                                    type.equals("boolean") ? new IntConstant(ei.getBooleanElement(index) ? 1 : 0) :
                                                    new IntConstant(ei.getReferenceElement(index));
    }

    public static int getArrayLength(ThreadInfo ti, int ref) {
        ElementInfo eiArray = ti.getElementInfo(ref);
        int len=(eiArray.getArrayFields()).arrayLength(); // assumed concrete
        return len;
    }

    public static Pair<Expression[], String> getInitialArrayValues(ThreadInfo ti, int ref) {
        int len = getArrayLength(ti, ref);
        Expression ret[] = new Expression[len];
        String type = null;
        ElementInfo eiArray = ti.getElementInfo(ref);
        for (int i=0; i < len; i++) {
            Pair<Expression, String> p = getArrayElement(eiArray, i);
            ret[i] = p.getFirst();
            type = p.getSecond();
        }
        return new Pair(ret, type);
    }

    public static void doArrayStore(ThreadInfo ti, ArrayExpressions arrayExpressions,
                                    DynamicTable<Expression> constantsTable) throws StaticRegionException {
        Iterator itr = arrayExpressions.table.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<Integer, Expression[]> entry = (Map.Entry) itr.next();
            int ref = entry.getKey();
            Expression[] exps = entry.getValue();
            ElementInfo eiArray = ti.getModifiableElementInfo(ref);
            int len = exps.length;
            String type = arrayExpressions.arrayTypesTable.get(ref);
            for (int i = 0; i < len; i++) {
                Expression newExpr = exps[i];
                eiArray.checkArrayBounds(i);
                if (newExpr instanceof Variable && constantsTable != null &&
                        constantsTable.lookup((Variable) newExpr) != null)
                    newExpr = constantsTable.lookup((Variable) newExpr);
                //TODO: Dont write an array output as a symbolic expression attribute if it is a constant
                //TODO: support "reference" as an array element type in the future
                if (eiArray.getClassInfo().isReferenceArray()) {
                    if (newExpr instanceof IntConstant) {
                        eiArray.setReferenceElement(i, ((IntConstant) newExpr).getValue());
                    } else throwException(new StaticRegionException("non-constant element-type given to reference array in ArraySSAVisitor.doArrayStore"), INSTANTIATION);
                }
                else if (type.equals("int")) eiArray.setIntElement(i, 0);
                else if (type.equals("char")) eiArray.setCharElement(i, (char) 0);
                else if (type.equals("float")) eiArray.setFloatElement(i, 0);
                else if (type.equals("double")) eiArray.setDoubleElement(i, 0);
                else if (type.equals("byte")) eiArray.setByteElement(i, (byte) 0);
                else if (type.equals("boolean")) eiArray.setBooleanElement(i, false);
                else
                    throwException(new StaticRegionException("unknown array type given to ArraySSAVisitor.doArrayStore"), INSTANTIATION);
                if (newExpr instanceof CloneableVariable)
                    newExpr = createGreenVar(type, newExpr.toString());
                eiArray.setElementAttr(i, greenToSPFExpression(newExpr));
                assert(greenToSPFExpression(newExpr) != null);
            }
        }
    }

}
