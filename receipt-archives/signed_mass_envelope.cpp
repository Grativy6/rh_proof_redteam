// Transfer an ordinary Mertens upper envelope to the actual PAL running integer.
// g++ -O3 -std=c++17 signed_mass_envelope.cpp -o signed_mass_envelope
#include <algorithm>
#include <cmath>
#include <fstream>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

using Int=std::int64_t;
using Wide=__int128_t;
struct Range {Int first,last; int maximum;};
struct Smooth {Int q,weight;};

Int iroot(Int n) {
    Int b=static_cast<Int>(std::sqrt(static_cast<long double>(n)));
    while(Wide(b)*b>n) --b;
    while(Wide(b+1)*(b+1)<=n) ++b;
    return b;
}

int main(int argc,char**argv) {
    if(argc!=4 && argc!=5) {std::cerr<<"Usage: signed_mass_envelope direct_limit final_limit relative_subdivisions [maxima.bin]\n";return 2;}
    const int D=std::stoi(argv[1]);
    const Int T=std::stoll(argv[2]);
    const int resolution=std::stoi(argv[3]);
    if(D<201 || D>400000000 || T<D || T>10000000000000LL || resolution<16 || resolution>65536)
        throw std::invalid_argument("outside supported envelope range");
    std::vector<std::int8_t> mu(D+1,1);
    std::vector<bool> prime(D+1,true);
    for(int p=2;p<=D;++p) if(prime[p]) {
        for(int n=p;n<=D;n+=p) mu[n]=-mu[n];
        if(Int(p)*p<=D) {
            for(int n=p*p;n<=D;n+=p) prime[n]=false;
            for(Int n=Int(p)*p;n<=D;n+=Int(p)*p) mu[n]=0;
        }
    }
    // Store a rigorous maximum of ordinary M on every small cell.
    std::vector<Range> boxes{{0,0,0}};
    int M=0; Int phys=0, last_positive=0,last_nonnegative=0;
    Int start=1,end=1; int best=0;
    int last_above_published=0;
    for(int n=1;n<=D;++n) {
        M+=mu[n];
        if(n==start) {
            end=std::min<Int>(D,start+std::max<Int>(1,start/resolution)-1);
            best=M;
        } else best=std::max(best,M);
        if(n==end) {boxes.push_back({start,end,best});start=end+1;}
        if(n>200 && M>=0 && Wide(1000)*M*1000*M>=Wide(571)*571*n)
            last_above_published=n;
        int u=n,v=1;
        while(u%4==0){u/=4;v*=2;}
        while(u%9==0){u/=9;v*=3;}
        if(u%2 && u%3) phys+=v*mu[u];
        if(phys>0) last_positive=n;
        if(phys>=0) last_nonnegative=n;
    }
    if(argc==5){
        std::ofstream out(argv[4],std::ios::binary);
        if(!out) throw std::runtime_error("cannot write ordinary maxima");
        for(auto box:boxes){
            const auto value=static_cast<std::uint32_t>(box.maximum);
            for(unsigned shift=0;shift<32;shift+=8) out.put(static_cast<char>((value>>shift)&255));
        }
        if(!out) throw std::runtime_error("incomplete ordinary maxima");
    }
    auto small_max=[&](Int a,Int b) {
        auto it=std::lower_bound(boxes.begin(),boxes.end(),a,
            [](const Range& x,Int value){return x.last<value;});
        int ans=it->maximum;
        while(it->last<b){++it;ans=std::max(ans,it->maximum);}
        return ans;
    };
    auto total_max=[&](Int a,Int b) -> Int {
        if(b<=D) return small_max(a,b);
        // Lioen and van de Lune, 200 < x <= 10^13; only the positive upper bound is used.
        const Int published=iroot(Int(571)*571*b)/1000;
        return a>D ? published : std::max<Int>(published,small_max(a,D));
    };
    std::vector<Smooth> coeff;
    for(Int two=1,i=0;two<=T;two*=2,++i) {
        Int three_root=1;
        for(Int q=two,j=0;q<=T;q*=3,++j) {
            const Int two_sum=(Int(1)<<(i/2+1))-1;
            const Int three_sum=(3*three_root-1)/2;
            coeff.push_back({q,two_sum*three_sum});
            if(j%2==1) three_root*=3;
        }
    }
    std::sort(coeff.begin(),coeff.end(),[](const Smooth& a,const Smooth& b){return a.q<b.q;});
    // On each physical integer panel, separately upper-bound M(floor(x/q)) for every q.
    Int panels=0,failed=0, first_fail=0,worst_left=0,worst_right=0,worst_value=0;
    Int minimum_millionths=std::numeric_limits<Int>::max();
    Int allowable_low=1000000000, allowable_all=1000000000;
    for(Int a=Int(D)+1;a<=T;) {
        const Int b=std::min(T,a+std::max<Int>(1,a/resolution)-1);
        Int ceiling=0, measured=0, external_root_weight=0;
        for(auto row:coeff){
            if(row.q>b)break;
            const Int lo=a/row.q, hi=b/row.q;
            ceiling+=row.weight*total_max(lo,hi);
            if(hi<=D) measured+=row.weight*small_max(lo,hi);
            else {
                // At a transition through D the local check also supplies this loose upper bound.
                const Int rt=iroot(hi);
                external_root_weight+=row.weight*(rt+(rt*rt<hi));
            }
        }
        ++panels;
        if(ceiling>=0){++failed;if(!first_fail) first_fail=a;}
        const Int rt=iroot(b);
        const Int saferoot=rt+(rt*rt<b);
        const Int score=ceiling<0 ? (-ceiling)*1000000/saferoot : -ceiling*1000000;
        if(score<minimum_millionths){minimum_millionths=score;worst_left=a;worst_right=b;worst_value=ceiling;}
        if(external_root_weight) {
            const Int permille=((-measured-1)*1000)/external_root_weight;
            allowable_all=std::min(allowable_all,permille);
            if(a<=2000000000000LL) allowable_low=std::min(allowable_low,permille);
        }
        a=b+1;
    }
    std::cout<<"{\"direct_limit\":"<<D<<",\"final_limit\":"<<T<<",\"resolution\":"<<resolution
             <<",\"ordinary_bins\":"<<boxes.size()<<",\"ordinary_upper_failures_last_local\":"<<last_above_published
             <<",\"last_positive_physical_in_direct\":"<<last_positive<<",\"last_nonnegative_physical_in_direct\":"<<last_nonnegative
             <<",\"direct_end_mass\":"<<phys<<",\"panels\":"<<panels<<",\"failed_to_prove_negative\":"<<failed
             <<",\"uniform_negative_margin_per_million_sqrt\":"<<minimum_millionths
             <<",\"sufficient_ordinary_permille_through_two_trillion\":"<<allowable_low
             <<",\"sufficient_ordinary_permille_full\":"<<allowable_all
             <<",\"first_unresolved_panel_left\":"<<first_fail<<",\"representative_least_margin_panel\":["
             <<worst_left<<','<<worst_right<<','<<worst_value<<"]}\n";
}
