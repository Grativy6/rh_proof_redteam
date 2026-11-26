// Zeroth and first moments of the PAL coefficients at exact quotient indices.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Int=std::int64_t;
using Wide=__int128_t;
struct Moments {Int mass; Wide first;};

std::string decimal(Wide n) {
    if (n<0) return "-"+decimal(-n);
    std::string s;
    do {s.push_back(char('0'+n%10)); n/=10;} while (n);
    std::reverse(s.begin(),s.end());return s;
}
Wide triangular(Int n) {return Wide(n)*(n+1)/2;}

std::vector<std::int8_t> mobius(Int cut) {
    std::vector<std::int8_t> mu(cut+1,1);
    std::vector<bool> prime(cut+1,true);
    for (Int p=2;p<=cut;++p) if (prime[p]) {
        for (Int k=p;k<=cut;k+=p) mu[k]=-mu[k];
        if (p>cut/p) continue;
        for (Int k=p*p;k<=cut;k+=p) prime[k]=false;
        for (Int k=p*p;k<=cut;k+=p*p) mu[k]=0;
    }
    return mu;
}

// Little-endian signed 64-bit maxima of the ordinary first moment on successive bins.
void maxima(Int limit) {
    const auto mu=mobius(limit);
    Int moment=0, start=1, end=1, maximum=0;
    auto emit=[](Int v) {
        const auto bits=static_cast<std::uint64_t>(v);
        for (int shift=0;shift<64;shift+=8) std::cout.put(static_cast<char>((bits>>shift)&255));
    };
    emit(0);
    for (Int n=1;n<=limit;++n) {
        moment+=n*mu[n];
        if (n==start) {
            end=std::min(limit,start+std::max<Int>(1,start/2048)-1);
            maximum=moment;
        } else maximum=std::max(maximum,moment);
        if (n==end) {emit(maximum);start=end+1;}
    }
}
int main(int argc,char** argv) {
    if (argc==3 && std::string(argv[1])=="bins") {
        const Int limit=std::stoll(argv[2]);
        if (limit<1 || limit>400000000) return 2;
        maxima(limit);return 0;
    }
    if (argc<5) return 2;
    const Int top=std::stoll(argv[1]),cut=std::stoll(argv[2]);
    const std::string mode=argv[3];
    if (top<1 || top>35000000000000LL || cut<1 || cut>100000000 ||
        cut>top || cut<top/(cut+1) || (mode!="physical" && mode!="ordinary")) return 2;
    const bool direct=mode=="physical";
    const auto mu=mobius(cut);
    std::vector<Int> low_mass(cut+1),low_first(cut+1);
    for (Int n=1;n<=cut;++n) {
        Int a=mu[n];
        if (direct) {
            Int k=n,v=1;
            while (k%4==0) {k/=4;v*=2;}
            while (k%9==0) {k/=9;v*=3;}
            a=(k%2 && k%3) ? v*mu[k] : 0;
        }
        low_mass[n]=low_mass[n-1]+a;
        low_first[n]=low_first[n-1]+n*a;
    }
    std::vector<std::pair<Int,Int>> source;
    for (Int a=1,i=0;a<=top;a*=2,++i) {
        for (Int q=a,u=1,j=0;q<=top;q*=3,++j) {
            Int b=((Int(1)<<(i/2+1))-1)*((3*u-1)/2);
            source.emplace_back(q,b);
            if (j%2) u*=3;
        }
    }
    std::sort(source.begin(),source.end());
    std::vector<Int> keys;
    std::vector<Moments> pref{{0,0}};
    for (auto [q,b]:source) {
        keys.push_back(q);
        pref.push_back({pref.back().mass+b,pref.back().first+Wide(q)*b});
    }
    std::vector<Moments> big(top/(cut+1)+1);
    auto get=[&](Int index) -> Moments {
        const Int n=top/index;
        return n<=cut ? Moments{low_mass[n],low_first[n]} : big[index];
    };
    for (Int i=static_cast<Int>(big.size())-1;i>0;--i) {
        const Int n=top/i;
        // With the ordinary Möbius input both divisor sums reduce to the unit.
        auto s=direct ? pref[std::upper_bound(keys.begin(),keys.end(),n)-keys.begin()] : Moments{1,1};
        Int r=2;
        for (;r<=n/r;++r) {
            const auto z=get(i*r);
            s.mass-=z.mass;
            s.first-=r*z.first;
        }
        Int prior=r-1;
        for (Int k=n/r;k>0;--k) {
            const Int last=n/k;
            s.mass-=(last-prior)*low_mass[k];
            s.first-=(triangular(last)-triangular(prior))*low_first[k];
            prior=last;
        }
        big[i]=s;
    }
    std::vector<Int> indices;
    if (std::string(argv[4])=="range" && argc==7) {
        const Int lo=std::stoll(argv[5]),hi=std::stoll(argv[6]);
        if (lo<1 || lo>hi || hi>top || hi-lo>2000000) return 2;
        for (Int k=lo;k<=hi;++k) indices.push_back(k);
    } else {
        for (int k=4;k<argc;++k) indices.push_back(std::stoll(argv[k]));
    }
    for (const Int id:indices) {
        if (id<1 || id>top) return 2;
        Moments s{0,0};
        if (direct) s=get(id);
        else for (auto [q,b]:source) {
            if (q>top/id) break;
            auto m=get(id*q);
            s.mass+=b*m.mass;
            s.first+=Wide(q)*b*m.first;
        }
        std::cout<<id<<' '<<top/id<<' '<<s.mass<<' '<<decimal(s.first)<<'\n';
    }
}
