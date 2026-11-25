\\ PARI/GP 2.15 or later. Run gp -fq check_auxiliary_prime_residue.gp
\\ Finite certificates for the examples at 11 and 701.
\\ The arbitrary-w rank bound and global survival are proved in the paper.

default(parisizemax, 1000000000);

check(ok, label) = {
  if(!ok, print("FAILED: ", label); quit(1));
};

quintic(T) = T^5 - 2*T^4 + 17*T^3 - 9*T^2 + 26*T + 23;
real11(T) = T^5 + T^4 - 4*T^3 - 3*T^2 + 3*T + 1;

check_dihedral() = {
  my(F = quintic(y), t = Mod(y,F));
  my(A = [-(t^4+12*t^2+15*t+16)/10, (t^4+12*t^2+25*t-4)/10]);
  my(R = [(-t^4+2*t^3-8*t^2-3*t+38)/70, (-2*t^4+5*t^3-36*t^2+40*t-49)/70]);
  my(basis, lattice, charpoly_u, disc);
  check(16*quintic(x) == (x-t)*prod(i=1,2,(2*x+A[i])^2+35*R[i]^2), "four roots in the quadratic extension");
  check(R[1] != 0 && R[2] != 0, "both root differences recover sqrt(-35)");
  basis = [1, t, (t^4+12*t^2+15*t+6)/10, (t^4-5*t^3+12*t^2-45*t-39)/20, (-2*t^4+5*t^3-34*t^2+30*t-37)/10];
  for(i=1,5,
    charpoly_u = charpoly(Mod(lift(basis[i]),F));
    check(denominator(charpoly_u)==1, "each lattice element is integral")
  );
  lattice = matrix(5,5,i,j,polcoef(lift(basis[j]),i-1,y));
  disc = poldisc(F)*matdet(lattice)^2;
  check(disc == 5^2*7^2*11^4, "integral lattice discriminant");
  check(polcyclo(11,x) == x^5*real11(x+1/x), "real cyclotomic polynomial");
};

check_local_eleven() = {
  my(a=quintic(x-4), b=real11(x+2));
  my(a_unit=-polcoef(a,0)/11, b_unit=-polcoef(b,0)/11, res);
  for(i=0,4,check(polcoef(a,i)%11==0 && polcoef(b,i)%11==0,"shifted coefficients"));
  check(valuation(polcoef(a,0),11)==1 && valuation(polcoef(b,0),11)==1, "Eisenstein constants");
  res = Mod(a_unit/b_unit,11);
  check(res == Mod(5,11) && znorder(res)==5, "ratio has non-fifth-power residue");
  check(polisirreducible(Mod(1,11)*(x^5-5)), "degree-five residue extension");
  print("At 11: leading unit residues ",[lift(Mod(a_unit,11)),lift(Mod(b_unit,11))],", fifth power of ratio ",lift(res));
};

check_ray(w, trace_a, radical_a, expected_log, expected_r) = {
  my(K=bnfinit(y^2-y+9,1), R=bnrinit(K,w,1), primitive=Mod(2,w), digits=5^expected_r);
  my(five_parts=select(a->a>1,apply(a->5^valuation(a,5),R.cyc)));
  check(isprime(w) && valuation(w-1,5)==expected_r && kronecker(-35,w)==1, "split ray prime");
  check(K.no==2 && bnfcertify(K)==1, "certified quadratic class group");
  check(five_parts==[digits,digits], "two full local factors");
  check(trace_a^2+35*radical_a^2==4*w, "norm of principal prime generator");
  check(znorder(primitive)==w-1 && primitive^expected_log==Mod(trace_a,w), "discrete logarithm");
  print("Ray at ",w,": 5-primary factors ",five_parts,", normalized uniformizer ",2*expected_log%digits," mod ",digits);
};

check_class_group() = {
  my(P=polcompositum(real11(x),x^2+35)[1], B=bnfinit(polredbest(P),1));
  my(V=polcompositum(real11(x),quintic(x))[1], dec);
  check(poldegree(P)==10 && B.cyc==[110] && bnfcertify(B)==1, "certified class group over the tame layer");
  dec=idealprimedec(nfinit([V,[11]]),11);
  check(poldegree(V)==25 && #dec==1 && dec[1].e==5 && dec[1].f==5, "local degree in the quintic compositum");
  print("Cl(K C_11) = C110; compositum of the quintics at 11 has e=5, f=5.");
};

check_detector(p, expected_v) = {
  my(F=quintic(x)*Mod(1,p), X=Mod(x,F));
  check(isprime(p) && kronecker(-35,p)==1 && p^2%11==1, "both base fields split");
  check(X^(p^5)==X && poldegree(gcd(lift(X^p-X),F))==0, "irreducible quintic via Frobenius");
  check(valuation(p^4-1,5)==expected_v, "exact cyclotomic depth");
  print("Prime ",p,": degree 5; first layer losing its Frobenius = ",expected_v);
};

check_dihedral();
check_local_eleven();
check_ray(11,3,1,8,1);
check_ray(701,33,7,152,2);
check_class_group();
check_detector(2663,1);
check_detector(307,3);
print("All exact finite checks passed.");
quit(0);
