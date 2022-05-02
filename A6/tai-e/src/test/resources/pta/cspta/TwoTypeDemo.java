class TwoTypeDemo {
    public static void main(String[] args) {
        List l1 = new List();
        l1.add(new Object());
    }
}

class List {
    Object element;
    void add(Object e) {
        this.element = e;
    }
}