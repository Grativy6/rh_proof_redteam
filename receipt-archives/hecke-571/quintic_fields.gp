\\ Run from the directory containing hunter-3.txt and hunter-5.txt.
check(e,n) = {
  my(v=readvec(Str("hunter-",e,".txt")), fields=Set([]), D=5^e*571^2);
  if(#v!=n,error("wrong candidate count"));
  for(i=1,n,
    my(f=x^5+sum(j=1,5,v[i][j]*x^(5-j)));
    if(!polisirreducible(f) || polsturm(f)!=5 || polgalois(f)[1]!=20,
       error("unexpected quintic"));
    if(nfdisc(f)==D, fields=setunion(fields,[polredabs(f)])));
  if(#fields!=1,error("expected a single reduced field"));
  print(e, " : ",n," polynomials of Galois-closure order 20; representative ",fields[1]);
};
iferr(check(3,11); check(5,58), E, print(E); quit(1));
quit(0)
