# Maximal irreducible character degree of GL(2, Z/nZ), via GAP's character table.
MaxDeg := function(n)
  local G;
  if IsPrimeInt(n) then G := GL(2, n);
  else G := GL(2, Integers mod n); fi;
  G := Image(IsomorphismPermGroup(G));
  return Maximum(CharacterDegrees(G)[1]{[1]}[1]) ;
end;
MaxDeg2 := function(n)
  local G, d;
  if IsPrimeInt(n) then G := GL(2, n);
  else G := GL(2, Integers mod n); fi;
  G := Image(IsomorphismPermGroup(G));
  d := CharacterDegrees(G);
  return [Size(G), Maximum(List(d, x -> x[1])), d];
end;
