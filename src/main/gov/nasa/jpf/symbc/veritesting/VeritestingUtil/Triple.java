package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

/**
 * Base class that this used to pair any three types.
 * @param <T>
 * @param <V>
 */
public class Triple <T,V,K> {
    private T first;
    private V second;
    private K third;

    public Triple(T first, V second, K third){
        this.first = first;
        this.second = second;
        this.third = third;
    }
    public T getFirst(){
        return first;
    }

    public V getSecond(){
        return second;
    }

    public K getThird(){ return third; }
}
