package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRef;

import java.util.HashMap;
import java.util.Set;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess.FieldSSAVisitor.FIELD_SUBSCRIPT_BASE;

public class GlobalSubscriptMap {
    public final HashMap<FieldRef, Integer> table;
    protected final String tableName = "Global Subscript Map";
    protected final String label1 = "FieldRef";
    protected final String label2 = "subscript";

    public GlobalSubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    public int lookup(FieldRef key) {
        int ret = -1;
        if (key != null) {
            for (FieldRef field: table.keySet()) {
                if (field.ref == key.ref && field.field.equals(key.field))
                    ret = table.get(field);
            }
        }
        else {
            throwException(new IllegalArgumentException("Cannot lookup the value of a null " + label1 + "."), INSTANTIATION);
        }
        return ret;
    }

    public void add(FieldRef v1, Integer v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(FieldRef key) {
        if (lookup(key) != -1)
            for (FieldRef field: table.keySet()) {
                if (field.ref == key.ref && field.field.equals(key.field))
                    table.remove(field);
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public Set<FieldRef> getKeys(){
        return table.keySet();
    }

    @Override
    protected GlobalSubscriptMap clone() {
        GlobalSubscriptMap map = new GlobalSubscriptMap();
        this.table.forEach(map::add);
        return map;
    }

    public void updateValue(FieldRef fieldRef, Integer p) {
        for(FieldRef key: table.keySet()) {
            if(key.equals(fieldRef)) {
                table.put(key, p);
            }
        }
    }

    public Integer createSubscript(FieldRef fieldRef) {
        if (lookup(fieldRef) != -1) {
            int ret = lookup(fieldRef);
            updateValue(fieldRef, ret+1);
            return ret+1;
        }
        else {
            add(fieldRef, FIELD_SUBSCRIPT_BASE + 1);
            return FIELD_SUBSCRIPT_BASE + 1;
        }
    }
}

