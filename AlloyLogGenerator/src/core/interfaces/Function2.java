package core.interfaces;

public interface Function2<T, U, R>  {
    R invoke(T t, U u) throws Exception;
}