package bank;

public class Account {
    //@ public ghost non_null Transaction lastTransaction = new Transaction(0);
    //@ public ghost int transactionCount = 0;

    //@ public invariant 0 <= unsuccessfulWithdraws <= 2;
    public int unsuccessfulWithdraws = 0;
    private int balance;
    private boolean locked;

    /*@ public normal_behavior
    @   requires t.amount > 0;
    @   assignable balance;
    @   ensures balance == \old(balance) + t.amount;
    @*/
    public void deposit(Transaction t) {
        if (t.getAmount() > 0) balance = balance + t.getAmount();
        //@ set lastTransaction = t;
    }

    /*@ public normal_behavior
    @   requires t.amount > 0 && balance >= t.amount && !locked;
    @   assignable balance, unsuccessfulWithdraws, transactionCount;
    @   ensures \result == true && balance == \old(balance)-t.amount
    @       && unsuccessfulWithdraws == 0;
    @   ensures transactionCount == \old(transactionCount) + 1
    @       && lastTransaction == t;
    @   also
    @   public normal_behavior
    @   requires t.amount > 0 && !locked && balance < t.amount;
    @   assignable lastTransaction, t.success;
    @   ensures \old(lastTransaction) != null
    @       && !\old(lastTransaction).success ==> locked;
    @   ensures lastTransaction == t && t.success == false;
    @   ensures \result == false;
    @   also
    @   public normal_behavior
    @   ensures !(t.amount > 0 && !locked) ==> \result == false;
    @*/
    public boolean withdraw(Transaction t) {
        if(t.getAmount() > 0 && !locked) {
            if (balance >= t.getAmount()) {
                balance = balance - t.getAmount();
                unsuccessfulWithdraws = 0;
                //@ set transactionCount = transactionCount + 1;
                //@ set lastTransaction = t;
                //@ set t.success = true;
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
    @   requires locked;
    @   assignable locked, unsuccessfulWithdraws, lastTransaction;
    @   ensures locked == false && unsuccessfulWithdraws == 0;
    @   ensures lastTransaction != null && lastTransaction.success == true;
    @   also
    @   public normal_behavior
    @   requires !locked;
    @   assignable \strictly_nothing;
    @*/
    public void unlock(){
        if(locked) {
            unsuccessfulWithdraws = 0;
            locked = false;
            //@ set lastTransaction = newTransaction();
        }
    }

    public /*@ pure */ Transaction newTransaction(){
        return new Transaction(0);
    }

    /*@ public normal_behavior
    @   ensures amount > 0 && \old(this.balance) >= amount && !locked
    @       ==> balance == \old(balance) - amount;
    @*/
    public void sendAmount(Account otherAcc, int amount){
        Transaction t = new Transaction(amount);
        boolean success = this.withdraw(t);
        if(success) otherAcc.deposit(t);
    }
}