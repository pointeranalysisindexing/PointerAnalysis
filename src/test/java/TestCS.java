public class TestCS {

    Object f;

    void set(Object t) {
        this.f = t;
    }

    Object get() {
        return this.f;
    }

    static TestCS foo() {
        return new TestCS();
    }

    public static void main(String[] args) {
        TestCS x = new TestCS();
        TestCS y = new TestCS();
        Object a = new Object();
        Object b = new Object();
        x.set(a); //prime edge
        y.set(b);
        Object c = x.get(); //summary edge
        Object d = y.get();
        Object e = foo(); // return prime edge
        Object f = foo();// return prime edge
        pointsTo(a,c);
    }
    static void pointsTo(Object p1, Object p2) {}
}
