package bank;

public class Transaction {
    //@ ghost public boolean success = true;

    private /*@ spec_public @*/ int amount;

    /*@ public normal_behavior
    @   ensures this.amount == amount;
    @*/
    public /*@ pure @*/ Transaction(int amount){
        this.amount = amount;
    }

    /*@ public normal_behavior
    @   ensures \result == this.amount;
    @*/
    public /*@ strictly_pure */ int getAmount(){
        return this.amount;
    }

}