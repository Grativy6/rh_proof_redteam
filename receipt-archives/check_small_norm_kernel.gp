\\ Independent small-field calculation for q=3, d=23. Run: gp -fq check_small_norm_kernel.gp
verify() = {
  my(K0, F, B, alpha, fac, J, principal, unit, exponents, count);
  K0 = polcompositum(x^2+1, x^2+3, 1)[1];
  F = polcompositum(K0[1], x^2+23, 1)[1];
  alpha = 2 + F[3];
  B = bnfinit(F[1], 1);
  if(bnfcertify(B) != 1, error("full class group and unit certification failed"));
  if(poldegree(F[1]) != 8 || B.disc != 256*69^4 || B.cyc != [6], error("field mismatch"));
  if(B.tu[1] != 12 || #B.fu != 3 || nfeltnorm(B,alpha) != 27^4, error("unit or norm mismatch"));
  fac = idealfactor(B,alpha);
  if(fac[,2] != [6]~, error("unexpected valuations"));
  fac[,2] = fac[,2]/2;
  J = idealfactorback(B,fac);
  if(idealpow(B,J,2) != idealhnf(B,alpha), error("half divisor mismatch"));
  principal = bnfisprincipal(B,J,1);
  if(principal[1] != [0]~, error("unexpected half-divisor class"));
  unit = alpha / nfbasistoalg(B,principal[2])^2;
  exponents = bnfisunit(B,unit);
  if(#exponents != 4 || !sum(i=1,3,exponents[i]%2), error("free-unit class missing"));
  count = 4^(#B.fu) * prod(i=1,#B.cyc,gcd(4,B.cyc[i]));
  if(count != 128, error("unexpected W size"));
  print("bnfcertify=1, class group C6, half divisor principal, free-unit component nonsquare, W size ",count);
};
verify_log(d, expected, split_expected) = {
  my(F0=polcompositum(x^2+1,x^2+3,1)[1], F=polcompositum(F0[1],x^2+d,1)[1], B=bnfinit(F[1],1), logged);
  if(bnfcertify(B)!=1, error("class group certification failed"));
  logged=bnflog(B,2);
  if(logged[1]!=expected || logged[3]!=split_expected, error("logarithmic or split class mismatch"));
  print("d=",d,", degree-zero logarithmic class group ",logged[1],", dyadically split ideal class group ",logged[3]);
};
iferr(verify(); verify_log(23,[2,2],[2]); verify_log(167,[4,2],[4]), E, print(E); quit(1));
quit(0)
