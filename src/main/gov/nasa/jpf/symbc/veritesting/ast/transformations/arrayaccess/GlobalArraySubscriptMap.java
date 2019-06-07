package gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess;

import gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef;
import za.ac.sun.cs.green.expr.IntConstant;

import java.util.HashMap;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.def.ArrayRef.looseArrayRefEquals;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.arrayaccess.ArraySSAVisitor.ARRAY_SUBSCRIPT_BASE;

public class GlobalArraySubscriptMap {
    public final HashMap<Integer, Integer> table;
    protected final String tableName = "Global Subscript Map";
    protected final String label1 = "ArrayRef";
    protected final String label2 = "subscript";

    public GlobalArraySubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    /*public int lookup(ArrayRef key) {
        int ret = -1;
        if (key != null) {
            for (ArrayRef array: table.keySet()) {
                if (array.ref == key.ref && array.index.equals(key.index))
                    ret = table.get(array);
            }
        }
        else {
            throwException(new IllegalArgumentException("Cannot lookup the value of a null " + label1 + "."), INSTANTIATION);
        }
        return ret;
    }*/

    // returns -1 if the key isn't found
    public int lookup(Integer key) {
        int ret = -1;
        if (key != null) {
            for (Integer ref: table.keySet()) {
                if (ref.equals(key))
                    ret = table.get(ref);
            }
        }
        else {
            throwException(new IllegalArgumentException("Cannot lookup the value of a null " + label1 + "."), INSTANTIATION);
        }
        return ret;
    }

    public void add(Integer v1, Integer v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(Integer key) {
        if (lookup(key) != -1)
            for (Integer ref: table.keySet()) {
//                if (arrayRef.ref == key.ref && arrayRef.index.equals(key.index))
//                    table.remove(arrayRef);
                if (ref.equals(key))
                    table.remove(ref);
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public Set<Integer> getKeys(){
        return table.keySet();
    }

    @Override
    protected GlobalArraySubscriptMap clone() {
        GlobalArraySubscriptMap map = new GlobalArraySubscriptMap();
        this.table.forEach(map::add);
        return map;
    }

    public void updateValue(Integer ref, Integer p) {
        for(Integer key: table.keySet()) {
            if(ref.equals(key)) {
                table.put(key, p);
            }
        }
    }

    public Integer createSubscript(Integer ref) {
        if (lookup(ref) != -1) {
            int ret = lookup(ref);
            updateValue(ref, ret+1);
            return ret+1;
        }
        else {
            add(ref, ARRAY_SUBSCRIPT_BASE + 1);
            return ARRAY_SUBSCRIPT_BASE + 1;
        }
    }
}


