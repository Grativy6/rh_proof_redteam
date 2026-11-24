\\ Arithmetic controls for the witness-dependent class-rank floor.
l=577;D=1792;
test()={
 my(samples=[12407809,20284698113,5507892146177,1191770163128833],bounds=[36863,21270527,12273094655,7081575616511]);
 for(s=1,#samples,my(q=samples[s],R=36864*l^(s-1)-1);
 if(!isprime(q) || (q-1)%(D*l^s) || valuation(q-1,l)!=s || R!=bounds[s],error("rank control"));
 print("w=",q,"  v577(w-1)=",s,"  C0 at least ",R));
};
iferr(test(),E,print(E);quit(1));quit(0)
