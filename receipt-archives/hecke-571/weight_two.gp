default(parisizemax,4000000000);
default(nbthreads,2);
default(threadsize,64000000);
default(threadsizemax,512000000);
test()={
 my(S=mfinit([3997,2,3997],0),n=mfdim(S),H=Mod(1,5)*matid(n),ps=[2,11,23,29],T,den,a,k,C);
 print("space dimension ",n);
 for(i=1,#ps,
   my(p=ps[i],t=getabstime());
   T=mfheckemat(S,p);den=denominator(T);
   if(den%5==0,error("denominator not invertible at 5"));
   T=Mod(1,5)*T; a=(1+p*kronecker(-571,p))%5;
   C=T*(T*H)-(a^2)*H;
   k=matker(C);H=H*k;
   print([p,den,a^2%5,matsize(H)[2],getabstime()-t]);
   if(matsize(H)[2]==0,break);
 );
 if(n!=378 || matsize(H)[2]!=0,error("cuspidal filter did not exhaust competitors"));
};
iferr(test(),E,print(E);quit(1));quit(0)
