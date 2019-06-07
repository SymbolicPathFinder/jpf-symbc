package gov.nasa.jpf.symbc.veritesting.ast.transformations.fieldaccess;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRef;
import gov.nasa.jpf.symbc.veritesting.ast.def.FieldRefVarExpr;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.INSTANTIATION;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

public final class FieldSubscriptMap {
    public final HashMap<FieldRef, SubscriptPair> table;
    protected final String tableName = "Path Subscript Map";
    protected final String label1 = "FieldRef";
    protected final String label2 = "subscript";
    private int uniqueNum = -1;

    public FieldSubscriptMap(){
        this.table = new HashMap<>();
    }

    // returns -1 if the key isn't found
    public SubscriptPair lookup(FieldRef key) {
        SubscriptPair ret = null;
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

    public void add(FieldRef v1, SubscriptPair v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    public void remove(FieldRef key) {
        if (lookup(key) != null)
            for (Iterator<Map.Entry<FieldRef, SubscriptPair>> fieldRefItr = table.entrySet().iterator();
                 ((Iterator) fieldRefItr).hasNext(); ) {
                Map.Entry<FieldRef, SubscriptPair> entry = fieldRefItr.next();
                FieldRef field = entry.getKey();
                if (field.ref == key.ref && field.field.equals(key.field))
                    fieldRefItr.remove();
            }
    }

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println("!w"+v1 + " --------- " + v2));
    }

    public void updateKeys(FieldRef oldKey, FieldRef newKey){
        for(FieldRef key: table.keySet()) {
            SubscriptPair value = table.get(key);
            if(key.equals(oldKey)) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }

    public Set<FieldRef> getKeys(){
        return table.keySet();
    }

    @Override
    protected FieldSubscriptMap clone() {
        FieldSubscriptMap map = new FieldSubscriptMap();
        this.table.forEach((key, value) -> {
            map.add(key, value);
        });
        return map;
    }

    public void updateValue(FieldRef fieldRef, SubscriptPair p) {
        for(FieldRef key: table.keySet()) {
            if(key.equals(fieldRef)) {
                table.put(key, p);
            }
        }
    }

    public void setUniqueNum(int uniqueNum) {
        this.uniqueNum = uniqueNum;
    }

    public ArrayList<FieldRefVarExpr> getUniqueFieldAccess() throws StaticRegionException {
        ArrayList<FieldRefVarExpr> retList = new ArrayList();
        if (uniqueNum == -1) throwException(new StaticRegionException("uniqueNum not set before getting unique field accesses"), INSTANTIATION);
        Iterator itr = this.table.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry pair = (Map.Entry) itr.next();
            FieldRef fieldRef = (FieldRef) pair.getKey();
            SubscriptPair subscriptPair = (SubscriptPair) pair.getValue();
            FieldRefVarExpr expr = new FieldRefVarExpr(fieldRef, subscriptPair);
            expr = expr.makeUnique(uniqueNum);
            retList.add(expr);
        }
        return retList;
    }
}
