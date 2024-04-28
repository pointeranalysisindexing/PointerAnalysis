public class TwoFieldsOneObject {
    Object f;
    Object g;
    Object getF() {
        return this.f;
    }
    Object getG() {
        return this.g;
    }
    void setF(Object p) {
        this.f = p;
    }
    void setG(Object p) {
        this.g = p;
    }
    public static void main(String[] args) {
        Object a = new Object();
        Object c = new Object();
        TwoFieldsOneObject e = new TwoFieldsOneObject();
        TwoFieldsOneObject g = new TwoFieldsOneObject();
        e.setF(a);
        g.f = e.f;
        g.g = e.f;
    }
}
