forprime(p=3,500, if(ispseudoprime((p^p-1)/(p-1)), print1("m",p," ")); if(ispseudoprime((p^p+1)/(p+1)), print1("p",p," "))); print();
quit
