//package customer;

//import org.junit.runner.RunWith;

//RunWith(Customer.class)
//Cucumber.Options(
//format = {"pretty", "json:target/"},
//features = {"src/customer/"})


//Given("^customer is a bank account holder$")
public class Customer {
    private /*@ spec_public @*/ String name;

    /*@ public invariant credits >= 0;
      @*/
    

//Given ("^customer asks bank staff if he/she can change to VIP account")

    private /*@ spec_public @*/ int credits;

    /*@ public invariant credits < 10000000 ==> !vip &&
      @                  credits >= 10000000 ==> vip;
      @*/
    private /*@ spec_public @*/ boolean vip;

    /*@ requires c >= 0;
      @ ensures credits == \old(credits) + c;
      @ assignable credits, vip;
      @*/
    

//When("^customer account's total credit is not less than (\\d+)$")

    public void addCredits(int c) {
        updateCredits(c);
        if (credits >= 10000000) {
            changeToVIP();
        }
    }

    /*@ requires c >= 0;
      @ ensures credits == \old(credits) + c;
      @ assignable credits;
      @*/
    private void updateCredits(int c) {
    	credits += c;
    }

    /*@ requires credits >= 10000000;
      @ ensures vip;
      @ assignable vip;
      @*/
    

//Then("^customer status change to VIP$")

    private void changeToVIP() {
        vip = true;
    }

    /*@ ensures this.name == name;
      @ assignable this.name;
      @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ ensures \result == name;
      @*/
    public /*@ pure @*/ String getName() {
        return name;
    }
}
