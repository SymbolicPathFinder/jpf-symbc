package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import java.util.Set;

/**
 * Base class for all environment tables.
 */


public class StaticTable<V> extends Table<Integer, V>{

    public StaticTable(String region_input_table, String var, String s) {
        super(region_input_table, var, s);
    }



    /**
     * Updates a key of the table for a specific entry.
     */

    public void updateKey(Integer oldKey, Integer newKey) {
        Object[] keys = table.keySet().toArray();
        for (int i = 0; i < keys.length; i++) {
            V value = table.get(keys[i]);
            if (keys[i] == oldKey) {
                table.put(newKey, value);
                table.remove(oldKey);
            }
        }
    }


    /**
     * Merge the table with the eateries of another table.
     */

    public void mergeTable(StaticTable<V> t) {
        this.table.putAll(t.table);
    }


    public Set<Integer> getKeys() {
        return table.keySet();

    }
}
