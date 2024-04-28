class Context {
    Object id(Object p) {
        Object x = p;
        return x;
    }

    Object ide(Object p) {
        return id(p);
    }

    Object idi(Object p) {
        return ide(p);
    }
    public static void main(String args[])
    {
        Context m = new Context();
        Object x = new Object();
        Object y = new Object();

        Object a = m.idi(x); //x -> idi-p -> ide-p -> id-p -> Obj x -> ret x -> a, m -> a
        Object b = m.idi(y);

        Context m1 = new Context();
        Object c = m1.idi(x);
        Object d = m1.idi(y);

        queryFor(m1);
    }
    private static void queryFor(Object queryVariable) {}
}
