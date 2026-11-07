E=ellinit([0,4,0,-16,16]);
r=ellrank(E); print("ellrank ", r);
print("tors ", elltors(E));
print("minimal model ", ellminimalmodel(E)[1..5]);
print("L(E,1) ", lfun(E,1));
quit
