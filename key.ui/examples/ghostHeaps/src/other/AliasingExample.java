package other;
public class AliasingExample{
    // non-ghost object
    public DummyObject o = new DummyObject();

    // ghost object
    //@ ghost public DummyObject go = o;
    //@ ghost public DummyObject d = new DummyObject();

    /* public normal_behavior
        requires true;
        ensures \result == 0;
     */
    /*public int foo(){
        DummyObject dum = new DummyObject();
        o = dum;
        o.a = 1;
        //@ set d = dum;
        //@ set d.a = 1;

        return o.a;
    }*/

    /*@ public normal_behavior
        requires true;
        assignable o.a;
        ensures o.a == \old(o.a) + 1;

        also

        public normal_behavior
        requires go == o;
        assignable go.a;
        ensures go.a == \old(go.a) + 1;
     */
    public void changeFieldThroughObject() {
        o.a = o.a + 1;
    }

    /*@ public normal_behavior
        requires true;
        assignable go.ga;
        ensures go.ga == \old(go.ga) + 1;

        also

        public normal_behavior
        requires go == o;
        assignable o.ga;
        ensures o.ga == \old(o.ga) + 1;
     */
    public void changeGhostFieldThroughGhostObject() {
        //@ set go.ga = go.ga + 1;
    }

    /*@ public normal_behavior
        requires o == go;
        assignable \everything;
        ensures \result == true;
     */
    public boolean outputBasedOnGhostVariable() {
        DummyObject help = o;                   // hier wird nur eine Referenz auf o erstellt, wie kann ich eine Kopie inklusive der ghost Variablen erstellen?
        // set go.gnext = new DummyObject();     // does not work becaus new is not allowed in set statement
        //@ set go.gnext = newDummyObject();
        //@ set go.ga = go.ga + 1;              // beim Vergleich mit "==" werden die Werte von ghost Variablen ignoriert

        return help == o;                       // wie kann man den return value von ghost code abhängig machen? dirket darauf zugreiffen geht ja nicht, oder doch?
    }


    public DummyObject newDummyObject() {
        return new DummyObject();
    }

    // ---- verification does not work, Parser already recognises the ghost assignment of a non-ghost field ----
    /*@ public normal_behavior
        requires true;
        assignable go.a;
        ensures go.a == \old(go.a) + 1;
     */
    public void changeFieldThroughGhostObject() {
        // set go.a = go.a + 1;
    }

    /*@ public normal_behavior
        requires true;
        assignable o.ga;
        ensures o.ga == o.ga +1;
     */
    public void changeGhostFieldThroughObject() {
        // o.ga = o.ga + 1;
    }
}