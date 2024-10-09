public class SmallExample {

    public int i = 0;
    //@ public ghost int j = 0;


    /*@ public normal_behavior
        assignable i, j;
        ensures i == \old(i)+2 && j == \old(j)+3;
     */
    public void m() {
        i = i + 2;
        //@ set j = j + 3;
    }


    /*@ public normal_behavior
        requires 0 < i <= 126;
        assignable i, j;
        ensures i == \old(i)+2 && j == \old(j)+3;
     */
    public void callM() {
        if(0 < i && i <= 126) {
            m();
        }
    }


    //@ public ghost int h;
    /*@ public normal_behavior
        accessible i, j;
        assignable h;
        ensures \result == i+3 && h == i+j;
     */
    public int m2() {
        //@ set h = j + i;
        return i + 3;
    }


    /*@ public normal_behavior
        accessible j;
        assignable i, h;
        ensures h == j + \old(i);
        ensures i == \old(i) + 3;
     */
    public void callM2() {
        i = m2();
    }


    /*@ public normal_behavior
        accessible j;
        assignable i, h;
        ensures h == j + i - 3;
        ensures i == \old(i) + (3 * 10);
     */
    public void callM2WithLoop() {
        int a=0;
        /*@ loop_invariant
            0 <= a <= 10 && i == \old(i) + 3*a
            && (a==0 ? h == \old(h) : h == (j + \old(i)+(3*(a-1))));
            decreases 10-a;
            assignable i, h;
            //accessible j;
         */
        while(a<10) {
            i = m2();
            a++;
        }
    }
}