package other;
public class DummyObject {
    public int a = 0;
    //@ public ghost int ga = 0;

    public DummyObject next;

    //@ ghost public DummyObject gnext = new DummyObject();

    //@ ghost public boolean[] ghostBools = {true, true, false, false};

    public boolean equals(DummyObject other){
        return a == other.a && next == other.next; // kann return abhängig von ga sein?
    }
}