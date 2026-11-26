// Two exact quotient recurrences for the full rough-square pass.
// g++ -O3 -std=c++17 dense_square_counts.cpp -o dense_square_counts
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;
using Wide = __int128_t;

Int root_floor(Int n) {
    Int r = static_cast<Int>(std::sqrt(static_cast<long double>(n)));
    while (Wide(r)*r>n) --r;
    while (Wide(r+1)*(r+1)<=n) ++r;
    return r;
}
Int rough_count(Int n) { return n-n/2-n/3+n/6; }

int main(int argc,char** argv) {
    if (argc<5) {
        std::cerr<<"Usage: dense_square_counts TOP SIEVE mobius|liouville DIVISOR...\n";
        return 2;
    }
    const Int top=std::stoll(argv[1]), cutoff=std::stoll(argv[2]);
    const std::string mode=argv[3];
    if (top<2 || top>35000000000000LL || cutoff<root_floor(top) || cutoff>top ||
        cutoff>100000000 || (mode!="mobius" && mode!="liouville"))
        throw std::invalid_argument("unsupported head, sieve or mode");
    const bool filled=mode=="liouville";
    std::vector<std::int8_t> mu(cutoff+1,1), li(cutoff+1,1);
    std::vector<bool> prime(cutoff+1,true);
    for (Int p=2;p<=cutoff;++p) if (prime[p]) {
        for (Int n=p;n<=cutoff;n+=p) mu[n]=-mu[n];
        if (p<=cutoff/p) {
            for (Int n=p*p;n<=cutoff;n+=p) prime[n]=false;
            for (Int n=p*p;n<=cutoff;n+=p*p) mu[n]=0;
        }
        if (filled) for (Int power=p;;) {
            for (Int n=power;n<=cutoff;n+=power) li[n]=-li[n];
            if (power>cutoff/p) break;
            power*=p;
        }
    }
    std::vector<Int> low(cutoff+1);
    for (Int n=1;n<=cutoff;++n)
        low[n]=low[n-1]+(n%2 && n%3 ? (filled ? li[n] : mu[n]) : 0);
    std::vector<Int> smooth;
    for (Int a=1;a<=top;a*=2)
        for (Int v=a;v<=top;v*=3) smooth.push_back(v);
    std::sort(smooth.begin(),smooth.end());
    const Int high=top/(cutoff+1);
    std::vector<Int> big(high+1);
    auto allowed=[&](Int n) {return filled ? rough_count(n) : n;};
    for (Int i=high;i>0;--i) {
        const Int n=top/i;
        // lambda_rough * rough_indicator is the indicator of rough squares.
        // mu_rough * 1 is the indicator of 2,3-smooth integers.
        Wide result=filled ? rough_count(root_floor(n)) :
            std::upper_bound(smooth.begin(),smooth.end(),n)-smooth.begin();
        Int k=2;
        for (;k<=n/k;++k) {
            if (filled && (k%2==0 || k%3==0)) continue;
            const Int z=n/k;
            result-=z<=cutoff ? low[z] : big[i*k];
        }
        Int previous=allowed(k-1);
        for (Int z=n/k;z>0;--z) {
            const Int end=allowed(n/z);
            result-=Wide(end-previous)*low[z];
            previous=end;
        }
        if (result>n || result< -Wide(n)) throw std::logic_error("rough count outside range");
        big[i]=static_cast<Int>(result);
    }
    auto get=[&](Int div) {return top/div<=cutoff ? low[top/div] : big[div];};
    std::cout<<"index head mobius_pass liouville_pass rough_mobius rough_liouville ordinary_liouville\n";
    for (int a=4;a<argc;++a) {
        const Int index=std::stoll(argv[a]);
        if (index<1 || index>top) throw std::invalid_argument("bad quotient index");
        const Int t=top/index, stop=root_floor(t);
        Int orig=0, expanded=0, raw=0, raw_filled=0, ordinary_li=0;
        for (Int r=1;r<=stop;++r) {
            Int rough=r;
            while (rough%2==0) rough/=2;
            while (rough%3==0) rough/=3;
            const Int v=r/rough;
            const Int read=get(index*r*r);
            if (filled) {
                if (rough==1) expanded+=v*read;
                orig+=v*mu[rough]*read;
                if (v==1) raw+=mu[rough]*read;
            } else {
                if (rough==1) orig+=v*read;
                expanded+=v*read;
                if (v==1) raw_filled+=read;
                const Int k=index*r*r;
                ordinary_li+=read-get(2*k)-get(3*k)+get(6*k);
            }
        }
        if (filled) {
            raw_filled=get(index);
            for (Int v:smooth) {
                if (v>t) break;
                Int n=v, sign=1;
                for (int p:{2,3}) while(n%p==0) {sign=-sign; n/=p;}
                ordinary_li+=sign*get(index*v);
            }
        } else raw=get(index);
        std::cout<<index<<' '<<t<<' '<<orig<<' '<<expanded<<' '<<raw<<' '<<raw_filled<<' '<<ordinary_li<<'\n';
    }
}
