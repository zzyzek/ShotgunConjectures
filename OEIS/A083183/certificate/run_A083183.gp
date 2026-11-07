default(parisizemax, 1000000000);
read("witness.gp");
setrand(1);
run(5, 100, [2,3,5,7], [3,7], [3,5,7], 1);
run(101, 1000, [2,3,5,7], [3,7], [3,5,7], 0);
