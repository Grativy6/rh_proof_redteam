\\ Read the three exact orbit coefficient rows supplied by the FLINT norm.
default(parisizemax,1800000000);
default(nbthreads,1);
check()={
 my(q=106619,m=125,M=625,r=12*m*q+1,z=Mod(Mod(1,M)*x,polcyclo(m)),tab=readvec("independent-three.json")[1]);
 if(#tab!=3 || #tab[1]!=m,error("coefficient table"));
 my(sq=select(a->(a^2+q)%M==0,[0..M-1])[1],t=Mod(sq-1,M)/2);
 my(P=Polrev(tab[1]+t*tab[2]-(1+t)*tab[3]),Q=Polrev(tab[1]+t*tab[3]-(1+t)*tab[2]),sc=Mod(r,M)^((q-1)/2),b=1);
 if(subst(P,x,z)*subst(Q,x,z^(m-1))!=sc,error("Jacobi norm"));
 for(a=1,m-1,if(a%5,my(k=lift(Mod(a,m)^(-82)),S=P);if(k>62,k=m-k;S=Q);b*=(subst(S,x,z^a)*subst(S,x,z^(m-a))/sc)^k));
 my(V=vector(100,i,lift(polcoef(lift(b),i-1))),cs=vector(100));cs[1]=2;cs[2]=2-x;
 for(i=3,100,cs[i]=(2-x)*cs[i-1]-cs[i-2]);
 my(pol=cs[51]+cs[26]+1,v=liftall(lift(Mod(1,M)/2*Mod(sum(i=1,100,V[i]*cs[i]),pol))));
 my(B=nfinit(pol),P5=idealprimedec(B,5)[1],res=vector(3,i,nfislocalpower(B,P5,v,5^i)));
 if(P5.e!=50 || P5.f!=1 || res!=[1,1,0],error("local power test"));
 print("q=106619, twist 81, fifth, 25th and 125th powers: ", res);
};
iferr(check(),E,print(E);quit(1));quit(0)
