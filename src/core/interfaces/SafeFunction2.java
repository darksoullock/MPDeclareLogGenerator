package core.interfaces;

public interface SafeFunction2<T, U, R>  {
    R invoke(T t, U u);
}