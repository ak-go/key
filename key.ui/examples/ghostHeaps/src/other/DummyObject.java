public class DummyObject {
    public int a = 0;
    //@ public ghost int ga = 0;

    public DummyObject next = new DummyObject();

    //@ ghost public DummyObject gnext = new DummyObject();

    public boolean equals(DummyObject other){
        return a == other.a && next == other.next; // kann return abhängig von ga sein?
    }
}