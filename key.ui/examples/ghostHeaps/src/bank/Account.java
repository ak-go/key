package bank;

public class Account {
    //@ private ghost Transaction lastTransaction;
    //@ public ghost int transactionCount = 0;

    //@ public invariant 0 <= unsuccessfulWithdraws <= 2;
    public int unsuccessfulWithdraws = 0;
    private int balance;
    private boolean locked;

    /* public normal_behavior
    @   assignable balance;
    @   ensures balance == \old(balance) + trans.amount;
    @*/
    /*public void makeTransactions(Transaction[] trans) {
        for (int i = 0; i < trans.length; i++) {
            balance = balance + trans[i].getAmount();
        }
        //@ set transNo = transNo + 1;
    }*/

    /*@ public normal_behavior
    @   requires amount > 0;
    @   assignable balance;
    @   ensures balance == \old(balance) + amount;
    @*/
    public void deposit(int amount) {
        if (amount > 0) {
            balance = balance + amount;
        }
    }

    /* also
    public normal_behavior
    @   requires t.amount > 0 && balance >= t.amount && !locked;
    @   assignable balance;
    @   ensures \result == true && balance == \old(balance) - t.amount;

    @
    @   also
    @   public normal_behavior
    @   assignable \nothing;
    @   ensures !(t.amount > 0 && !locked) ==> \result == false;
     */

    /*@ public normal_behavior
    @   requires t.amount > 0 && !locked && balance < t.amount;
    @   assignable lastTransaction, t.success;
    @   ensures \old(lastTransaction) != null && !\old(lastTransaction).success ==>
    @       locked;
    @   ensures lastTransaction == t && t.success == false && \result == false;
    @*/
    public boolean withdraw(Transaction t) {
        if(t.getAmount() > 0 && !locked) {
            if (balance >= t.getAmount()) {
                balance = balance - t.getAmount();
                return true;
            }
            unsuccessfulWithdraws = unsuccessfulWithdraws + 1;
            if (unsuccessfulWithdraws == 2) {
                locked = true;
            }
            //@ set lastTransaction = t;
            //@ set t.success = false;
        }
        return false;
    }

    /*@ public normal_behavior
    @   assignable locked, unsuccessfulWithdraws;
    @   ensures \result == locked && locked == false && unsuccessfulWithdraws == 0;
    @*/
    public boolean unlock(){
        locked = false;
        unsuccessfulWithdraws = 0;
        return locked;
    }

    public int getBalance(){
        return balance;
    }
}