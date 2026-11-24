\\ Run in the directory containing independent-norm.txt from jacobi_norm.cpp.
default(parisizemax,1800000000);
default(nbthreads,1);
check()={
 my(q=2179,r=5447501,m=125,M=625,c=polcyclo(125),z=Mod(Mod(1,M)*x,c),W=readvec("independent-norm.txt")[1]);
 if(#W!=2 || #W[1]!=125 || #W[2]!=125,error("wrong norm record"));
 my(P=Polrev(W[1]),Q=Polrev(W[2]),unit=Mod(r,M)^1089,b=1);
 if(subst(P,x,z)*subst(Q,x,z^(m-1))!=unit,error("Jacobi norm and conjugate mismatch"));
 for(a=1,m-1,if(a%5,my(k=lift(Mod(a,m)^(-2)),S=P);
   if(k>62,k=m-k;S=Q);
   b*= (subst(S,x,z^a)*subst(S,x,z^(m-a))/unit)^k));
 my(V=vector(100,i,lift(polcoef(lift(b),i-1))));
 my(cs=vector(100));cs[1]=2;cs[2]=2-x;
 for(i=3,100,cs[i]=(2-x)*cs[i-1]-cs[i-2]);
 my(pol=cs[51]+cs[26]+1, realb=liftall(lift(Mod(1,M)/2*Mod(sum(i=1,100,V[i]*cs[i]),pol))));
 my(B=nfinit(pol),p=idealprimedec(B,5)[1]);
 if(p.e!=50 || p.f!=1,error("wrong completion"));
 my(zv=vector(3,i,nfislocalpower(B,p,realb,5^i)));
 if(zv!=[1,1,0],error("local power discrepancy"));
 print("Independent real cyclotomic local tests for fifth, 25th and 125th powers: ",zv);
};
iferr(check(),E,print(E);quit(1));quit(0)
