// An integer-only quotient grid for the physical summatory mass.
// g++ -O3 -std=c++17 physical_mass_grid.cpp -o physical_mass_grid
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Int=std::int64_t;
using Wide=__int128_t;

int main(int argc,char**argv) {
    if(argc!=5 && argc!=6) {std::cerr<<"Usage: physical_mass_grid TOP direct_limit first_divisor last_divisor [--rough]\n";return 2;}
    const Int T=std::stoll(argv[1]), D=std::stoll(argv[2]), first=std::stoll(argv[3]), last=std::stoll(argv[4]);
    if(D<1 || D>100000000 || T<=D || T>35000000000000LL || D<T/(D+1)
        || first<1 || first>last || last>T) throw std::invalid_argument("unsupported quotient range");
    const bool rough=argc==6;
    if(rough && std::string(argv[5])!="--rough") throw std::invalid_argument("unknown grid mode");
    std::vector<std::int8_t> mu(D+1,1);
    std::vector<bool> prime(D+1,true);
    for(Int p=2;p<=D;++p) if(prime[p]){
        for(Int n=p;n<=D;n+=p) mu[n]=-mu[n];
        if(p*p<=D){
            for(Int n=p*p;n<=D;n+=p) prime[n]=false;
            for(Int n=p*p;n<=D;n+=p*p) mu[n]=0;
        }
    }
    std::vector<Int> low(D+1);
    for(Int n=1;n<=D;++n) {
        Int u=n,v=1;
        while(u%4==0){u/=4;v*=2;}
        while(u%9==0){u/=9;v*=3;}
        low[n]=low[n-1]+(rough ? (n%2 && n%3 ? mu[n] : 0) : (u%2 && u%3 ? v*mu[u] : 0));
    }
    std::vector<std::pair<Int,Int>> source;
    for(Int two=1,i=0;two<=T;two*=2,++i) {
        Int power3=1;
        for(Int q=two,j=0;q<=T;q*=3,++j) {
            const Int weight=((Int(1)<<(i/2+1))-1)*((3*power3-1)/2);
            source.emplace_back(q,weight);
            if(j%2) power3*=3;
        }
    }
    std::sort(source.begin(),source.end());
    std::vector<Int> keys, prefix{0};
    for(auto [q,weight]:source){keys.push_back(q);prefix.push_back(prefix.back()+weight);}
    std::vector<Int> smooth_roots;
    for(auto [q,weight]:source) if(q<=T/q) smooth_roots.push_back(q);
    const auto allowed=[&](Int n){return rough ? n-n/2-n/3+n/6 : n;};
    const Int high=T/(D+1);
    std::vector<Int> up(high+1);
    for(Int i=high;i>0;--i) {
        const Int n=T/i;
        Wide answer=rough ? 1 : prefix[std::upper_bound(keys.begin(),keys.end(),n)-keys.begin()];
        Int k=2;
        for(;k<=n/k;++k) {
            if(rough && (k%2==0 || k%3==0)) continue;
            const Int q=n/k;
            answer-=q<=D ? low[q] : up[i*k];
        }
        Int previous=allowed(k-1);
        for(Int q=n/k;q>0;--q) {
            const Int end=allowed(n/q);
            answer-=Wide(end-previous)*low[q];
            previous=end;
        }
        if(answer>3*Wide(n) || answer< -3*Wide(n)) throw std::logic_error("mass outside absolute bound");
        up[i]=static_cast<Int>(answer);
    }
    for(Int i=first;i<=last;++i) {
        const Int n=T/i;
        Int result=n<=D ? low[n] : up[i];
        if(rough){
            result=0;
            for(Int v:smooth_roots){
                if(v>n/v)break;
                const Int q=i*v*v;
                result+=v*(T/q<=D ? low[T/q] : up[q]);
            }
        }
        std::cout<<i<<' '<<n<<' '<<result<<'\n';
    }
}
