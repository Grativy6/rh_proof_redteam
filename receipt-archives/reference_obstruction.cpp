// Enclose the inverse profiles at every integer y up to N using a fixed integer scale.
// g++ -O3 -std=c++17 reference_obstruction.cpp -o reference_obstruction
#include <algorithm>
#include <cstdint>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Wide = __int128_t;
constexpr Wide scale = Wide{1} << 80;

std::string decimal(Wide x) {
    if (x < 0) return "-" + decimal(-x);
    if (x == 0) return "0";
    std::string out;
    while (x) { out.push_back(static_cast<char>('0'+x%10)); x/=10; }
    std::reverse(out.begin(),out.end());
    return out;
}

struct Prefix {
    int mass = 0;
    Wide reciprocal = 0;
    void add(int n,int mark) {
        mass += mark;
        if (mark) reciprocal += mark*(scale/n);
    }
};

struct Run {
    int weight, start=0, left=0, right=0;
    void cut(int last) {
        if (start && last>start &&
            (!left || Wide(last-start)*left*right>Wide(right-left)*start*last)) {
            left=start; right=last;
        }
        start=0;
    }
};

int main(int argc,char** argv) {
    if (argc!=2) { std::cerr<<"Usage: reference_obstruction N\n"; return 2; }
    const int N=std::stoi(argv[1]);
    if (N<2 || N>100000000) throw std::invalid_argument("Use 2 <= N <= 100000000");
    std::vector<std::int8_t> mu(N+1,1);
    std::vector<bool> prime(N+1,true);
    for (int p=2;p<=N;++p) if (prime[p]) {
        for (int n=p;n<=N;n+=p) mu[n]=-mu[n];
        if (std::int64_t(p)*p<=N) {
            for (int n=p*p;n<=N;n+=p) prime[n]=false;
            for (std::int64_t n=std::int64_t(p)*p;n<=N;n+=std::int64_t(p)*p) mu[n]=0;
        }
    }
    constexpr int band_left=33400000, band_right=35300000;
    Wide density_lo=scale,density_hi=scale;
    if (N>=band_right) for (int p=2;p<=band_right;++p) if (prime[p]) {
        density_lo=density_lo*(p-1)/p;
        density_hi=(density_hi*(p-1)+p-1)/p;
    }
    Prefix plain, whole, half;
    Wide slope=0, area=0, peak_slope_upper=-(Wide{1}<<120);
    Wide scale_peak=-(Wide{1}<<120), early_floor=Wide{1}<<120, whole_floor=Wide{1}<<120;
    int floor_at=0;
    auto rough_mark=[&](int n) {return n%2 && n%3 ? int(mu[n]) : 0;};
    constexpr std::uint64_t root_scale=std::uint64_t{1}<<50;
    Wide root_total=0, root_half=0;
    int first_plain=0, first_rough=0;
    Wide plain_upper=0, rough_upper=0;
    std::vector<Run> runs;
    for (int e:{1,2,4,8,16,32,64,128,256,512,1024,2048}) runs.push_back({e});
    for (int n=1;n<=N;++n) {
        if (!first_plain) {
            plain.add(n,mu[n]);
            const Wide upper=Wide(n)*plain.reciprocal-scale*plain.mass+Wide(n)*n;
            if (upper<0) { first_plain=n; plain_upper=upper; }
        }
        if (n%2 && n%3) {
            whole.add(n,mu[n]);
            if (mu[n]) {
                auto b=static_cast<std::uint64_t>(root_scale/std::sqrt(static_cast<long double>(n)));
                const Wide goal=Wide(root_scale)*root_scale;
                while (Wide(b)*b*n>goal) --b;
                while (Wide(b+1)*(b+1)*n<=goal) ++b;
                root_total+=Wide(mu[n])*b;
            }
        }
        if (n==N/2) root_half=root_total;
        const int h=n/2;
        if (n%2==0 && h%2 && h%3) half.add(h,mu[h]);
        const Wide midpoint=Wide(2)*n*whole.reciprocal-2*scale*whole.mass
                           -Wide(n)*half.reciprocal+2*scale*half.mass;
        const Wide error=Wide(2)*n*n+Wide(n)*h;
        const Wide upper=midpoint+error;
        if (n>=2 && n<=12000000) early_floor=std::min(early_floor,midpoint-error);
        if (midpoint-error<whole_floor) { whole_floor=midpoint-error; floor_at=n; }
        // A different expansion integrates the actual slope changes. Its scale is 2*scale.
        const Wide area_error=Wide(n)*(n-1)/2;
        if (2*(area+area_error)<midpoint-error || midpoint+error<2*(area-area_error))
            throw std::runtime_error("direct sum and slope recurrence disagree");
        if (n>=band_left && n<=band_right) {
            peak_slope_upper=std::max(peak_slope_upper,area+area_error);
            scale_peak=std::max(scale_peak,upper);
        }
        const int delta=rough_mark(n)-(n%2==0 ? rough_mark(n/2) : 0);
        slope+=delta*(scale/n);
        area+=slope;
        if (!first_rough && upper<0) { first_rough=n; rough_upper=upper; }
        for (auto& r:runs) {
            if (upper < -(scale/4)*r.weight) { if (!r.start) r.start=n; }
            else r.cut(n-1);
        }
    }
    if (N>=band_right && (peak_slope_upper>=-32*scale || scale_peak>=-64*scale))
        throw std::runtime_error("fixed interval misses the negative depth");
    std::cout<<"{\"max_y\":"<<N<<",\"scale\":\""<<decimal(scale)
             <<"\",\"plain_first_certified_negative\":"<<first_plain
             <<",\"plain_upper_numerator_over_twice_scale\":\""<<decimal(plain_upper)
             <<"\",\"rough_first_certified_negative\":"<<first_rough
             <<",\"rough_upper_numerator_over_four_times_scale\":\""<<decimal(rough_upper)
             <<"\",\"negative_intervals\":[";
    bool first=true;
    for (auto& r:runs) { r.cut(N); if (!r.left) continue;
        if (!first) std::cout<<',';
        first=false;
        std::cout<<"{\"left\":"<<r.left<<",\"right\":"<<r.right
                 <<",\"negative_depth_over_16\":"<<r.weight<<'}';
    }
    std::cout<<']';
    if(N>=band_right)
        std::cout<<",\"fixed_band\":{\"left\":"<<band_left<<",\"right\":"<<band_right
                 <<",\"upper_direct_over_4S\":\""<<decimal(scale_peak)
                 <<"\",\"upper_integrated_over_2S\":\""<<decimal(peak_slope_upper)
                 <<"\",\"small_prime_product_lower_over_S\":\""<<decimal(density_lo)
                 <<"\",\"small_prime_product_upper_over_S\":\""<<decimal(density_hi)<<"\"}";
    std::cout<<",\"integral_moments\":{\"full_mass\":"<<whole.mass<<",\"half_mass\":"<<half.mass
             <<",\"full_reciprocal_over_S\":\""<<decimal(whole.reciprocal)
             <<"\",\"half_reciprocal_over_S\":\""<<decimal(half.reciprocal)
             <<"\",\"root_scale\":\""<<root_scale<<"\",\"full_inverse_root_over_root_scale\":\""<<decimal(root_total)
             <<"\",\"half_inverse_root_over_root_scale\":\""<<decimal(root_half)<<"\"}";
    std::cout<<",\"early_floor_over_4S\":\""<<decimal(early_floor)
             <<"\",\"early_floor_last\":"<<std::min(N,12000000)
             <<",\"global_floor_over_4S\":\""<<decimal(whole_floor)
             <<"\",\"global_floor_at\":"<<floor_at<<'}'<<'\n';
}
