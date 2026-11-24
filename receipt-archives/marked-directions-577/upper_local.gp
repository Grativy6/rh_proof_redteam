\\ Direct Eulerian-polynomial computation in F_(577^12).
default(parisizemax,400000000);
l=577;
dig(a,Y)={
 my(C=if(abs(a)==1,256,128),D=7*C,n=lift(Mod(1-296*a,576)),psi=vector(C),et=[1,1,-1,1,-1,-1,0],t=Mod(510,l)^a);
 for(j=0,C/4-1,my(i=lift(Mod(5,C)^j));psi[i]=t^j;psi[C-i]=t^j);
 my(E=Mod(1,l)*x);
 for(j=0,n-2,E=x*((1-x)*deriv(E)+(j+1)*E));
 my(tot=0,ga=0,z=Y^(1792/D),v=1,nf=Mod(n!,l));
 for(i=1,D-1,v*=z;if(gcd(i,D)==1,
   my(ch=et[(i-1)%7+1]*psi[(i-1)%C+1]);ga+=ch*v;
   tot-=ch*subst(E,x,v)/((1-v)^n*nf)));
 if(ga==0,error("zero Gauss sum"));
 my(ans=if(a==1,211,if(a==2,241,if(a==-1,229,160))));if(tot!=ans*ga,error("digit mismatch"));
 print("a=",a," degree=",n," coefficient/Gauss sum=",ans);
};
run()={my(y=ffgen(l^12,'t),Y=ffprimroot(y)^((l^12-1)/1792));if(fforder(Y)!=1792,error("tame root"));foreach([1,2,-1,-2],a,dig(a,Y));};
iferr(run(),E,print(E);quit(1));quit(0)