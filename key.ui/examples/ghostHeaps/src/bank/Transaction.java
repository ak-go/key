package bank;

public class Transaction {
    //@ ghost public boolean active = false;
    //@ ghost public boolean success;

    private /*@ spec_public @*/ int amount;

    /*@ public normal_behavior
    @   ensures this.active == false;
    @   ensures this.amount == amount;
    @*/
    public /*@ pure @*/ Transaction(){
        this.amount = 0;
    }

    /*@ public normal_behavior
    @   assignable active, amount;
    @   ensures active == true;
    @   ensures this.amount == \old(this.amount) + amount;
    @*/
    public void addAmount(int amount){
        //@ set active = true;
        this.amount = this.amount + amount;
    }

    /*@ public normal_behavior
    @   ensures \result == this.amount;
    @*/
    public /*@ strictly_pure */ int getAmount(){
        return this.amount;
    }

    /*@ public normal_behavior
        assignable active, amount;
        ensures this.active == false && this.amount == 0;
     */
    public void resetAmount() {
        //@ set active = false;
        this.amount = 0;
    }
}