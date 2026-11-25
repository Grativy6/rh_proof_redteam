// Exact rough Mobius moments on all quotient rows of a fixed head.
// Build with g++ -O3 -std=c++17 cubic_window_moments.cpp -o cubic_window_moments
// The companion Python script reconstructs the signed integers and checks their size.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Index = std::uint64_t;
using Wide = unsigned __int128;
constexpr Index modulus = (Index(1) << 61) - 1;

struct Mod61 {
    Index value;
    Mod61(Index n = 0) : value(n % modulus) {}
    static Mod61 reduced(Index n) {
        Mod61 out;
        out.value = n < modulus ? n : n - modulus;
        return out;
    }
    friend Mod61 operator+(Mod61 a, Mod61 b) { return reduced(a.value + b.value); }
    friend Mod61 operator-(Mod61 a, Mod61 b) { return reduced(a.value + modulus - b.value); }
    friend Mod61 operator*(Mod61 a, Mod61 b) {
        Wide p = Wide(a.value) * b.value;
        return reduced(Index(p & modulus) + Index(p >> 61));
    }
};

template <class R> using Moments = std::array<R, 4>;

template <class R> Moments<R> powers(Index n) {
    R x(n), x2 = x*x;
    return {R(1), x, x2, x2*x};
}

template <class R> Moments<R> power_sums(Index n) {
    Index a = n, b = n+1, c = 2*n+1;
    if (a % 2 == 0) a /= 2; else b /= 2;
    R triangle = R(a)*R(b);
    if (a % 3 == 0) a /= 3;
    else if (b % 3 == 0) b /= 3;
    else c /= 3;
    return {R(n), triangle, R(a)*R(b)*R(c), triangle*triangle};
}

template <class R, bool rough> Moments<R> multiplier_sums(Index n) {
    auto sums=power_sums<R>(n);
    if constexpr (rough) {
        const auto two=power_sums<R>(n/2), three=power_sums<R>(n/3), six=power_sums<R>(n/6);
        R w2(1), w3(1), w6(1);
        for (unsigned j=0;j<4;++j) {
            sums[j]=sums[j]-w2*two[j]-w3*three[j]+w6*six[j];
            w2=w2*R(2);w3=w3*R(3);w6=w6*R(6);
        }
    }
    return sums;
}

template <class R> void subtract_group(Moments<R>& total, const Moments<R>& scale,
                                       const Moments<R>& earlier) {
    for (unsigned j=0; j<4; ++j) total[j] = total[j] - scale[j]*earlier[j];
}

std::vector<std::int8_t> rough_sieve(Index limit) {
    std::vector<std::int8_t> mu(limit+1);
    std::vector<bool> composite(limit+1);
    std::vector<Index> primes;
    mu[1] = 1;
    for (Index n=2; n<=limit; ++n) {
        if (!composite[n]) { primes.push_back(n); mu[n] = -1; }
        for (Index p : primes) {
            if (n*p > limit) break;
            composite[n*p] = true;
            if (n%p == 0) break;
            mu[n*p] = -mu[n];
        }
    }
    for (Index n=2; n<=limit; ++n)
        if (n%2==0 || n%3==0) mu[n]=0;
    return mu;
}

std::string decimal(Wide n) {
    if (!n) return "0";
    std::string digits;
    while (n) { digits.push_back(char('0'+n%10)); n/=10; }
    std::reverse(digits.begin(), digits.end());
    return digits;
}
std::string decimal(Mod61 x) { return std::to_string(x.value); }

template <class R, bool rough> void run(Index top, Index cutoff, const std::vector<Index>& requests,
                            const std::vector<std::int8_t>& mu, const char* label) {
    std::vector<Moments<R>> low(cutoff+1), high(top/(cutoff+1)+1);
    for (Index d=1; d<=cutoff; ++d) {
        low[d] = low[d-1];
        if (mu[d]) {
            const auto row = powers<R>(d);
            for (unsigned j=0; j<4; ++j)
                low[d][j] = mu[d]>0 ? low[d][j]+row[j] : low[d][j]-row[j];
        }
    }
    std::vector<Index> smooth;
    for (Index two=1; two<=top; two*=2)
        for (Index n=two; n<=top; n*=3) smooth.push_back(n);
    std::sort(smooth.begin(), smooth.end());
    std::vector<Moments<R>> source(smooth.size()+1);
    for (size_t i=0; i<smooth.size(); ++i) {
        const auto row = powers<R>(smooth[i]);
        for (unsigned j=0;j<4;++j) source[i+1][j]=source[i][j]+row[j];
    }
    auto get = [&](Index n) -> const Moments<R>& {
        return n<=cutoff ? low[n] : high[top/n];
    };
    for (Index i=top/(cutoff+1); i>0; --i) {
        const Index n=top/i;
        auto a=source[std::upper_bound(smooth.begin(),smooth.end(),n)-smooth.begin()];
        if constexpr (rough) a=powers<R>(1);
        Index d=2;
        for (; d<=n/d; ++d) {
            if constexpr (rough) { if (d%2==0 || d%3==0) continue; }
            subtract_group(a,powers<R>(d),get(n/d));
        }
        auto prev=multiplier_sums<R,rough>(d-1);
        for (Index q=n/d; q>0; --q) {
            const Index r=n/q;
            const auto end=multiplier_sums<R,rough>(r);
            Moments<R> weights;
            for (unsigned j=0;j<4;++j) weights[j]=end[j]-prev[j];
            subtract_group(a,weights,low[q]);
            prev=end;
        }
        high[i]=a;
    }
    for (Index divisor : requests) {
        const auto& a=get(top/divisor);
        std::cout<<label<<' '<<divisor;
        for (auto v:a) std::cout<<' '<<decimal(v);
        std::cout<<'\n';
    }
}

#include "cubic_reciprocal_bounds.hpp"

int main(int argc, char** argv) {
    if (argc<4) { std::cerr<<"usage: cubic_window_moments TOP SIEVE [--rough-multipliers|--reciprocal|--rough-reciprocal|--direct] DIVISOR...\n";return 2; }
    try {
        const Index top=std::stoull(argv[1]), cutoff=std::stoull(argv[2]);
        const std::string mode=argv[3];
        if (top<2 || top>(Index(1)<<45) || cutoff<1 || cutoff>top ||
            cutoff>50000000 || (mode!="--direct" && cutoff<top/(cutoff+1)))
            throw std::invalid_argument("head or sieve outside documented range");
        bool reciprocal=mode=="--reciprocal" || mode=="--rough-reciprocal";
        bool rough=mode=="--rough-multipliers" || mode=="--rough-reciprocal";
        std::vector<Index> queries;
        for(int i=(rough||reciprocal||mode=="--direct")?4:3;i<argc;++i) {
            if (std::string(argv[i])=="--stdin") {
                Index value;
                while(std::cin>>value) {
                    if(value==0 || value>top) throw std::invalid_argument("divisor outside head");
                    queries.push_back(value);
                }
                continue;
            }
            auto d=std::stoull(argv[i]);
            if(d==0 || d>top) throw std::invalid_argument("divisor outside head");
            queries.push_back(d);
        }
        if (mode=="--direct") {direct_checkpoints(top,queries);return 0;}
        const auto mu=rough_sieve(cutoff);
        if (queries.empty()) throw std::invalid_argument("supply at least one divisor");
        if (reciprocal) {
            reciprocals(top,cutoff,queries,mu,rough);
        } else if (rough) {
            run<Wide,true>(top,cutoff,queries,mu,"2^128");
            run<Mod61,true>(top,cutoff,queries,mu,"2^61-1");
        } else {
            run<Wide,false>(top,cutoff,queries,mu,"2^128");
            run<Mod61,false>(top,cutoff,queries,mu,"2^61-1");
        }
    } catch(const std::exception& ex) {std::cerr<<ex.what()<<'\n';return 2;}
}
