package other;
public class DummyObject {
    public int a = 0;
    //@ public ghost int ga = 0;

    public DummyObject otherDummy = new DummyObject();

    //@ ghost public DummyObject gnext = new DummyObject();

}