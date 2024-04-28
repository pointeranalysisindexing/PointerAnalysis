public class TestClassA {
    TestClassA() {

    }
    static TestClassA foo() {
        return new TestClassA();
    }
    public static void main(String[] args) {
        TestClassA x = foo(); //test with field inits too
        TestClassA y = foo();
    }
}
