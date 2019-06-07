package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRefVarExpr;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.SubscriptPair;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef.looseArrayRefEquals;

public class ArraySubscriptMap {
    public final HashMap<ArrayRef, SubscriptPair> table;
    protected final String tableName = "Path Subscript Map";
    protected final String label1 = "ArrayRef";
    protected final String label2 = "subscript";
    private int uniqueNum = -1;

    public ArraySubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    public SubscriptPair lookup(ArrayRef key) {
        SubscriptPair ret = null;
        if (key != null) {
            for (ArrayRef arrayRef: table.keySet()) {
                if (looseArrayRefEquals(arrayRef, key)) {
                    ret = table.get(arrayRef);
                }
            }
        }
        else {
            throwException(new IllegalArgumentException("Cannot lookup the value of a null " + label1 + "."), INSTANTIATION);
        }
        return ret;
    }

    // returns -1 if the key isn't found
    // Because we do a loose lookup, its possible that both ArrayRefs write to the same array without being exactly the same
    // This can happen if the reference value in both ArrayRefs is the same but one or both use a non-IntConstant for the index
    public ArrayRef lookupKey(ArrayRef key) {
        ArrayRef ret = null;
        if (key != null) {
            for (ArrayRef arrayRef: table.keySet()) {
                if (looseArrayRefEquals(arrayRef, key)) {
                    ret = arrayRef;
                }
            }
        }
        else {
            throwException(new IllegalArgumentException("Cannot lookup the value of a null " + label1 + "."), INSTANTIATION);
        }
        return ret;
    }

    public void add(ArrayRef v1, SubscriptPair v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(ArrayRef key) {
        if (lookup(key) != null)
            for (ArrayRef arrayRef: table.keySet()) {
//                if (arrayRef.ref == key.ref && arrayRef.index.equals(key.index))
//                    table.remove(arrayRef);
                if (looseArrayRefEquals(arrayRef, key))
                    table.remove(arrayRef);
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public void updateKeys(ArrayRef oldKey, ArrayRef newKey){
        for(ArrayRef key: table.keySet()) {
            SubscriptPair value = table.get(key);
            if (looseArrayRefEquals(oldKey, newKey)) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }

    public Set<ArrayRef> getKeys(){
        return table.keySet();
    }

    @Override
    protected ArraySubscriptMap clone() {
        ArraySubscriptMap map = new ArraySubscriptMap();
        this.table.forEach((key, value) -> {
            map.add(key, value);
        });
        return map;
    }

    public void updateValue(ArrayRef arrayRef, SubscriptPair p) {
        for(ArrayRef key: table.keySet()) {
            if(looseArrayRefEquals(arrayRef, key)) {
                table.put(key, p);
            }
        }
    }

    public void setUniqueNum(int uniqueNum) {
        this.uniqueNum = uniqueNum;
    }

    public ArrayList<ArrayRefVarExpr> getUniqueArrayAccess() throws StaticRegionException {
        ArrayList<ArrayRefVarExpr> retList = new ArrayList();
        if (uniqueNum == -1) throwException( new StaticRegionException("uniqueNum not set before getting unique array accesses"), INSTANTIATION);
        Iterator itr = this.table.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry pair = (Map.Entry) itr.next();
            ArrayRef arrayRef = (ArrayRef) pair.getKey();
            SubscriptPair subscriptPair = (SubscriptPair) pair.getValue();
            ArrayRefVarExpr expr = new ArrayRefVarExpr(arrayRef, subscriptPair);
            expr = expr.makeUnique(uniqueNum);
            retList.add(expr);
        }
        return retList;
    }
}

