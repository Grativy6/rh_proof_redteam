\\ PARI/GP 2.15.4. Run "gp -fq check_odd_class_fields.gp".
check_quartic(q, expected) = {
  my(F=x^4-5*q*x^2+5*q^2, B=bnfinit(F,1), action=x^3/q-3*x, g);
  if(bnfcertify(B)!=1 || B.cyc!=[5] || B.sign!=[4,0] || B.disc!=5^3*q^2,
     error("quartic field or class group mismatch"));
  g=bnfisprincipal(B,nfgaloisapply(B,action,B.gen[1]),0)[1];
  if(g!=expected,error("wrong cyclotomic action on the class group"));
  print("q=",q,", class group C5, chosen generator acts by ",g);
};
check_forms() = {
  my(S=mfinit([7,3,-7],0), f, D=3997, value);
  if(mfdim(S)!=1,error("unexpected weight-three dimension"));
  f=mfeigenbasis(S)[1];
  if(mfcoef(f,5)!=0 || mfcoef(f,11)!=-6,error("wrong Hecke eigenvalues"));
  value=sum(a=1,D,kronecker(D,a)*a^2)/D;
  if(value!=22416,error("wrong generalized Bernoulli number"));
  print("Level 7 character -7, dimension 1, a5=0, a11=-6. B_2(3997)=",value);
};
iferr(check_quartic(571,3); check_quartic(347,2); check_forms(), E, print(E); quit(1));
quit(0)
