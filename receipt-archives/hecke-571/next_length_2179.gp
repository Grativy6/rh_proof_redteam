quick()={
 my(q=2179,F=x^4-5*q*x^2+5*q^2,B=bnfinit(F,1),g=x^3/q-3*x);
 if(bnfcertify(B)!=1,error("class group certificate"));
 print([q,B.disc,B.sign,B.cyc]);
 for(i=1,#B.gen,print(bnfisprincipal(B,nfgaloisapply(B,g,B.gen[i]),0)));
 my(D=7*q);print("B2 ",sum(a=1,D,kronecker(D,a)*a^2)/D);
};
iferr(quick(),E,print(E);quit(1));quit(0)
