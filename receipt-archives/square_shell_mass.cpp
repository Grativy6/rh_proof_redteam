// Count the unsigned weight in any integer interval in two independent ways.
// Arguments: largest allowed head, then "rows" or "labels". Input: lower upper cutoff.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int=std::int64_t;
Int root(Int n) {
    Int r=static_cast<Int>(std::sqrt(static_cast<long double>(n)));
    while (r+1<=n/(r+1)) ++r;
    while (r>0 && r>n/r) --r;
    return r;
}
Int rough(Int n) {return n-n/2-n/3+n/6;}

struct Result {
    Int weight=0,occupied=0,largest=0,large_weight=0,large_count=0,signed_mass=0;
    void note(Int v,Int count,Int cut) {
        if (!count) return;
        occupied+=count;weight+=count*v;largest=std::max(largest,v);
        if (v>cut) {large_count+=count;large_weight+=v*count;}
    }
};

// Full consecutive square slabs, using direct physical coefficients.
int square_prefix(int max_root) {
    if (max_root<1 || max_root>12000) return 2;
    const int nmax=(max_root+1)*(max_root+1)-1;
    std::vector<std::int8_t> mu(nmax+1,1);
    std::vector<bool> composite(nmax+1);
    for (int p=2;p<=nmax;++p) if (!composite[p]) {
        for (int k=p;k<=nmax;k+=p) mu[k]=-mu[k];
        if (p>nmax/p) continue;
        for (int k=p*p;k<=nmax;k+=p) composite[k]=true;
        for (int k=p*p;k<=nmax;k+=p*p) mu[k]=0;
    }
    std::vector<int> marks;
    std::cout<<"root size peak abs_peak_without_largest largest endpoint_difference contact square_mass\n";
    Int mass=0;
    for (int j=1;j<=max_root;++j) {
        marks.clear();
        for (int n=j*j;n<(j+1)*(j+1);++n) {
            int r=n,v=1;
            while (r%4==0) {r/=4;v*=2;}
            while (r%9==0) {r/=9;v*=3;}
            marks.push_back((r%2 && r%3) ? v*mu[r] : 0);
        }
        mass+=marks[0];
        const Int start=mass;
        auto biggest=std::max_element(marks.begin()+1,marks.end(),
            [](int a,int b){return std::abs(a)<std::abs(b);});
        Int net=0,rest=0,peak=0,rest_peak=0,contact=start;
        for (auto it=marks.begin()+1;it!=marks.end();++it) {
            net+=*it;
            if (it!=biggest) rest+=*it;
            peak=std::max(peak,std::abs(net));rest_peak=std::max(rest_peak,std::abs(rest));
            contact=std::min(contact,start+net);
        }
        mass+=net;
        std::cout<<j<<' '<<marks.size()<<' '<<peak<<' '<<rest_peak<<' '<<*biggest
                 <<' '<<net<<' '<<contact<<' '<<start<<'\n';
    }
    return 0;
}

int main(int argc,char** argv) {
    if (argc==3 && std::string(argv[1])=="squares") return square_prefix(std::stoi(argv[2]));
    if (argc!=3) return 2;
    Int cap=std::stoll(argv[1]);
    const std::string mode=argv[2];
    if (cap<1 || cap>100000000000000LL || (mode!="rows" && mode!="labels")) return 2;
    const Int stop=root(cap);
    std::vector<bool> prime(stop+1,true);
    std::vector<std::int8_t> mu(stop+1,1);
    std::vector<int> primes;
    for (Int p=2;p<=stop;++p) if (prime[p]) {
        primes.push_back(static_cast<int>(p));
        for (Int k=p;k<=stop;k+=p) mu[k]=-mu[k];
        if (p>stop/p) continue;
        for (Int k=p*p;k<=stop;k+=p) prime[k]=false;
        for (Int k=p*p;k<=stop;k+=p*p) mu[k]=0;
    }
    Int a,b,cut;
    while (std::cin>>a>>b>>cut) {
        if (a<0 || a>=b || b>cap || cut<0) throw std::invalid_argument("bad interval");
        Result s;
        if (mode=="rows") {
            for (Int two=1;two<=b/two;two*=2) {
                for (Int v=two;v<=b/v;v*=3) {
                    const Int lo=a/(v*v),hi=b/(v*v);
                    if (lo==hi) continue;
                    Int count=0;
                    for (Int k=1;k<=hi/k;k+=2) {
                        if (k%3 && mu[k])
                            count+=mu[k]*(rough(hi/(k*k))-rough(lo/(k*k)));
                    }
                    s.note(v,count,cut);
                }
            }
        } else {
            for (Int lo=a+1;lo<=b;lo+=300000) {
                const Int n=std::min<Int>(300000,b-lo+1),hi=lo+n-1;
                std::vector<Int> rest(n);
                std::vector<int> weight(n,1);
                for (Int i=0;i<n;++i) {
                    Int z=lo+i;
                    for (int p:{2,3}) {
                        while (z%(p*p)==0) {z/=p*p;weight[i]*=p;}
                        if (z%p==0) {weight[i]=0;break;}
                    }
                    rest[i]=z;
                }
                for (int p:primes) {
                    if (p<5) continue;
                    if (Int(p)*p>hi) break;
                    for (Int i=(p-lo%p)%p;i<n;i+=p) if (weight[i]) {
                        rest[i]/=p;
                        weight[i]=(rest[i]%p==0 ? 0 : -weight[i]);
                    }
                }
                for (Int i=0;i<n;++i) if (weight[i]) {
                    s.note(std::abs(weight[i]),1,cut);
                    s.signed_mass+=rest[i]>1 ? -weight[i] : weight[i];
                }
            }
        }
        std::cout<<a<<' '<<b<<' '<<cut<<' '<<s.weight<<' '<<s.occupied<<' '
                 <<s.largest<<' '<<s.large_count<<' '<<s.large_weight<<' '<<s.signed_mass<<'\n';
    }
}
