public class TestParamPrime {

    Object f;

    void set(Object t) {
        this.f = t;
    }

    public static void main(String[] args) {
        TestParamPrime x = new TestParamPrime();
        TestParamPrime y = new TestParamPrime();
        Object a = new Object();
        Object b = new Object();
        x.set(a);
        y.set(b);
    }
}
