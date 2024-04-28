public class TwoSrcTwoSinkFieldMatch {
    Object f;
    TwoSrcTwoSinkFieldMatch() {}
    void set(Object p) {
        this.f = p;
    }
    Object get() {
        return this.f;
    }
    public static void main(String[] args) {
        Object a = new Object();
        Object c = new Object();
        TwoSrcTwoSinkFieldMatch e = new TwoSrcTwoSinkFieldMatch();
        TwoSrcTwoSinkFieldMatch g = new TwoSrcTwoSinkFieldMatch();
        e.set(a);
        g.set(c);
        Object b = e.get();
        Object d = g.get();
    }
}
