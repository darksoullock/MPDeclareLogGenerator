package core.interfaces;

public interface Function3<T, U, V, R>  {
    R invoke(T t, U u, V v) throws Exception;
}