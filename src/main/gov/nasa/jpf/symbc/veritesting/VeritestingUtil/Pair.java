package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

/**
 * Base class that this used to pair any two types.
 * @param <T>
 * @param <V>
 */
public class Pair <T,V> {
    private T first;
    private V second;

    public Pair(T first, V second){
        this.first = first;
        this.second = second;
    }
    public T getFirst(){
        return first;
    }

    public V getSecond(){
        return second;
    }
}
