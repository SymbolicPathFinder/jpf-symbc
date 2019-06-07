package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.DONTKNOW;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;


/**
 * Base class for all environment tables that use a Expression object as the key.
 */


public class CloneableVarTable<T> {
    public final HashMap<CloneableVariable, T> table;
    protected String tableName;
    protected String label1;
    protected String label2;

    protected CloneableVarTable(){
        this.table = new HashMap<>();
    }

    public CloneableVarTable(String tableName, String label1, String label2){
        this.table = new HashMap<>();
        this.tableName = tableName;
        this.label1 = label1;
        this.label2 = label2;
    }

    /**
     * Basic lookup inside the table.
     * */
    public T lookup(CloneableVariable v) {
        if (v != null)
            return table.get(v);
        else
            try {
                throwException(new StaticRegionException("Cannot lookup the value of a null " + label1 + "."), DONTKNOW);
            } catch (StaticRegionException e) {
                System.out.println(e.getMessage());
            }
        return null;
    }

    /**
     * Basic add row inside the table.
     * */

    public void add(CloneableVariable v1, T v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    /**
     * Basic remove element/row inside the table.
     * */

    public void remove(CloneableVariable v1) {
        table.remove(v1);
    }

    /**
     * Basic print of the table. inside the table.
     * */

    public void print() {
        System.out.println("\nprinting " + tableName+" ("+ label1 + "->" + label2 +")");
        table.forEach((v1, v2) -> System.out.println(v1 + " --------- " + v2));
    }

    /**
     * Updates a key of the table for a specific entry.
     * */

    public void updateKeys(CloneableVariable oldKey, CloneableVariable newKey){
        Object[] keys = table.keySet().toArray();
        for (Object key : keys) {
            T value = table.get(key);
            if (key == oldKey) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }

    /**
     * Returns all keys of the table.
     * */

    public Set<CloneableVariable> getKeys(){
        return table.keySet();
    }

    /**
     * Appends a postfix to each key in the table.
     * @param unique A unique postfix.
     */

    public void makeUniqueKey(int unique) throws CloneNotSupportedException, StaticRegionException {
        List keys = new ArrayList(table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while(itr.hasNext()){
            CloneableVariable oldKey = (CloneableVariable) itr.next();
            CloneableVariable newKey = oldKey.clone();
            newKey = newKey.makeUnique(unique);
            table.put(newKey, table.get(oldKey));
            table.remove(oldKey);
        }
    }

    /**
     * Merge the table with the entries of another table.
     * */

    public void mergeExpressionTable(CloneableVarTable<T> t){
        this.table.putAll(t.table);
    }

}
