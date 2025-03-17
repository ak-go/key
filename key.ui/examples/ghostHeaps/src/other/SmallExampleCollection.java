package other;
public class SmallExampleCollection {
    DummyObject d1 = new DummyObject();
    DummyObject d2 = new DummyObject();
    DummyObject d3 = new DummyObject();
    //@ ghost DummyObject[] dummyArr;

    //@ ghost DummyObject gd1 = new DummyObject();
    //@ ghost DummyObject gd2 = new DummyObject();
    //@ ghost DummyObject gd3 = new DummyObject();

    /*@ public normal_behavior
    @   assignable d1.otherDummy, d2.otherDummy, dummyArr;
    @   ensures \result == dummyArr[0] && \result.otherDummy == dummyArr[1]
    @   && \result.otherDummy.otherDummy == dummyArr[2]
    @   && \result.otherDummy.otherDummy == dummyArr[3];
    @*/
    public DummyObject connectDummyObjects(){
        DummyObject[] arr = {d1, d2, d3};
        //@ set dummyArr = arr;
        d1.otherDummy = d2;
        d2.otherDummy = d3;
        d3.otherDummy = d1;
        return d1;
    }

    /*@ public normal_behavior
    @   requires d1 != d2 && d2 != d3 && d3 != d1;
    @   assignable d1.otherDummy, d1.a, d2.a, d3.otherDummy, d3.a;
    @   ensures d1.otherDummy == d3 && d1.a == 12
    @       && d2.a == 3 && d3.otherDummy == d2 && d3.a == 12;
    @*/
    public void opOnJavaFields(){
        d1.otherDummy = d3;
        d1.a = 12;
        d2.a = 3;
        d1.otherDummy.a = d1.a;
        d1.otherDummy.otherDummy = d2;
    }

    /*@ public normal_behavior
    @   requires d1 != d2 && d2 != d3 && d3 != d1;
    @   assignable d1.otherDummy, d1.a, d2.a, d3.otherDummy, d3.a,
    @       gd1.gOtherDummy, gd1.gOtherDummy.ga;
    @   ensures d1.otherDummy == d3 && d1.a == 12
    @       && d2.a == 3 && d3.otherDummy == d2 && d3.a == 12;
    @   ensures gd1.gOtherDummy == d1 && gd1.gOtherDummy.ga == d2.a;
    @*/
    public void opOnJavaFields2(){
        d1.otherDummy = d3;
        d1.a = 12;
        //@ set gd1.gOtherDummy = d1;
        d2.a = 3;
        //@ set d1.ga = d2.a;
        d1.otherDummy.a = d1.a;
        d1.otherDummy.otherDummy = d2;
    }

    /*@ public normal_behavior
    @   requires gd1 != gd2 && gd2 != gd3 && gd3 != gd1;
    @   assignable gd1.gOtherDummy, gd1.ga, gd2.gOtherDummy, gd2.ga,
    @       gd3.gOtherDummy, gd3.ga;
    @   ensures gd1.gOtherDummy == gd3 && gd3 == gd2.gOtherDummy
    @       && gd3.ga == 42 && 42 == gd2.ga
    @       && gd3.gOtherDummy == gd1 && gd1.ga == 21;
    @*/
    public void opOnGhostFields(){
        //@ set gd1.gOtherDummy = gd3;
        //@ set gd3.ga = 42;
        //@ set gd2.ga = gd1.gOtherDummy.ga;
        //@ set gd2.gOtherDummy = gd1.gOtherDummy;
        //@ set gd2.gOtherDummy.gOtherDummy = gd1;
        //@ set gd1.ga = 21;
    }

    /*@ public normal_behavior
    @   requires gd1 != gd2 && gd2 != d3 && d3 != gd1 && d3 != d3;
    @   assignable gd1.gOtherDummy, gd1.ga, gd2.gOtherDummy, gd2.ga,
    @       d3.gOtherDummy, d3.ga, d1.a;
    @   ensures gd1.gOtherDummy == d3 && d3 == gd2.gOtherDummy
    @       && d3.ga == 42 && 42 == gd2.ga && d1.a == d3.a
    @       && d3.gOtherDummy == gd1 && gd1.ga == 21;
    @*/
    public void opOnGhostFields2(){
        d1.a = d3.a;
        //@ set gd1.gOtherDummy = d3;
        //@ set d3.ga = 42;
        //@ set gd2.ga = gd1.gOtherDummy.ga;
        //@ set gd2.gOtherDummy = gd1.gOtherDummy;
        //@ set gd2.gOtherDummy.gOtherDummy = gd1;
        //@ set gd1.ga = 21;
    }
}