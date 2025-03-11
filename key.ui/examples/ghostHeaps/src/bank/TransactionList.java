package bank;

public interface TransactionList {

    //@ ghost Transaction[] array = new Transaction[10];
    //@ ghost int size = 0;

    // private represents footprint = array, array[*], size;

    /*@ private invariant array != null;
      @ private invariant 0 <= size && size <= array.length;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] != null);
      @ private invariant \typeof(array) == \type(Transaction[]);
      @*/




    /*@ public normal_behavior
        requires 0 <= index < array.length;
        assignable \nothing;
        ensures \result == array[index];
     */
    public Transaction get(int index);


    /*@ public normal_behavior
        ensures \result == (\exists int i; 0 <= i < array.length; array[i] == t);
     */
    public /*@ pure @*/ boolean contains(Transaction t);


    /*@ public normal_behavior
        requires size < array.length;
        assignable array[size];
        ensures array[size] == t;
        ensures size == \old(size)+1;

        also

        public normal_behavior
        requires size == array.length;
        assignable \strictly_nothing;
     */
    public void add(Transaction t);


    /*@ public normal_behavior
        requires contains(t);
        assignable array[0..size];
        ensures !contains(t);
        ensures (\forall int i; 0 <= i < size; (((i < size-1) && \old(array[i]) == t) ==> array == \old(array[i+1])) &&
            (i == size-1 ==> array[i] == null));

        also

        public normal_behavior
        requires !contains(t);
        assignable \strictly_nothing;
     */
    public void remove(Transaction t);
}