\\ PARI/GP 2.15+. Run gp -fq check_frobenius_centralizer_cost.gp
\\ x is the uniformizer. All matrix entries start in F_p[x].
\\ Pivot valuations are computed in its discrete valuation ring at x.

check(ok, label) = { if(!ok, print("FAILED: ",label); quit(1)); };

coordinates(n,a,g) = {
  my(entries=List());
  for(i=1,n,for(j=1,n,
    if((i<=a)==(j<=a),listput(entries,[0,i,j]),
      for(h=1,g,listput(entries,[h,i,j])))
  ));
  Vec(entries)
};

commutator(P,odd,coords) = {
  my(size=#coords);
  matrix(size,size,i,j,
    my(row=coords[i],col=coords[j],M);
    if(row[1]==col[1],M=P,
      if(row[1]==0 && col[1]!=0,M=odd[col[1]],M=0));
    if(type(M)!="t_MAT",0,
      (row[3]==col[3])*M[row[2],col[2]]-(row[2]==col[2])*M[col[3],row[3]])
  )
};

power_input(P,odd,h) = {
  my(n=matsize(P)[1], Z=matrix(n,n), out=vector(#odd));
  for(i=1,#odd,
    my(T=matconcat([P,odd[i];Z,P])^h);
    out[i]=vecextract(T,vector(n,j,j),vector(n,j,n+j))
  );
  [P^h,out]
};

\\ At each step a least-valuation pivot divides the active block in F_p[[x]].
exponents(M) = {
  my(L=M,n=matsize(M)[1],v=vector(n,j,-1));
  for(k=1,n,
    my(ri=0,cj=0,best=0);
    for(i=k,n,for(j=k,n,if(L[i,j]!=0,
      my(w=valuation(L[i,j],x));
      if(!ri || w<best,ri=i;cj=j;best=w)
    )));
    if(!ri,break);
    if(ri!=k,for(j=k,n,my(s=L[k,j]);L[k,j]=L[ri,j];L[ri,j]=s));
    if(cj!=k,for(i=k,n,my(s=L[i,k]);L[i,k]=L[i,cj];L[i,cj]=s));
    v[k]=best;
    for(i=k+1,n,for(j=k+1,n,L[i,j]-=L[i,k]*L[k,j]/L[k,k]))
  );
  v
};
cost(v) = sum(i=1,#v,if(v[i]<0,0,v[i]));
log_count(v,m) = sum(i=1,#v,if(v[i]<0,m,min(m,v[i])));

direct_log_count(L,m,p) = {
  my(n=matsize(L)[1], entries=n*m);
  my(A=matrix(entries,entries,i,j,
    my(source=(j-1)%m,target=(i-1)%m);
    if(target<source,0,polcoef(L[1+(i-1)\m,1+(j-1)\m],target-source,x))
  ));
  entries-matrank(Mod(1,p)*A)
};

run_case(label,P,odd,a,p,delta,base_cost) = {
  my(n=matsize(P)[1],coords=coordinates(n,a,#odd),L=commutator(P,odd,coords));
  my(base=exponents(L));
  check(#select(z->z==-1,base)==n && cost(base)==base_cost,label);
  forstep(k=1,p,p-1,
    my(data=power_input(P,odd,k),Lpow=commutator(data[1],data[2],coords),v=exponents(Lpow));
    check(Lpow==L^k,Str(label," Frobenius commutator identity"));
    check(cost(v)==base_cost+(k-1)*delta,Str(label," exact cost at power ",k));
    for(m=1,13,check(log_count(v,m)==direct_log_count(Lpow,m,p),Str(label," finite kernel ",m)));
    print(label,", power ",k,", excess ",cost(v),", nonzero Smith valuations ",vecsort(select(z->z>=0,v)))
  )
};

{
  my(p=5,r=2,h=x^r,one=Mod(1,p));
  my(P=one*matdiagonal([1,1+h]),Xm=one*[0,1;0,0],Xs=one*[0,h;0,0]);
  run_case("1+1, unit extension",P,[Xm],1,p,2*r,r);
  run_case("1+1, divisible extension",P,[Xs],1,p,2*r,2*r);
  my(diag=one*matdiagonal([1,1+h,1+2*h]),tri=diag,Z=one*matrix(3,3));
  tri[1,2]=one;
  run_case("2+1, diagonal block",diag,[Z],2,p,6*r,6*r);
  run_case("2+1, triangular block",tri,[Z],2,p,6*r,4*r);
  run_case("2+1, triangular block without odd copies",tri,[],2,p,2*r,0);
  my(mixed=[one*[0,0,1;0,0,x;2,0,0],one*[0,0,0;0,0,1;0,1,0]]);
  run_case("2+1, two mixed extension coordinates",tri,mixed,2,p,10*r,12);
}
print("All finite checks passed.");
quit(0);
