// Enumerate the previous heads that can fund the newest weighted row.
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using Int = std::int64_t;
using Wide = __int128_t;

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    const int top = std::stoi(argv[1]);
    if (top < 1 || top > 70000000) return 2;
    std::vector<std::int8_t> mu(top+1,1);
    std::vector<bool> prime(top+1,true);
    for (int p=2; p<=top; ++p) if (prime[p]) {
        for (int n=p; n<=top; n+=p) mu[n]=-mu[n];
        if (p>top/p) continue;
        for (int n=p*p; n<=top; n+=p) prime[n]=false;
        for (int n=p*p; n<=top; n+=p*p) mu[n]=0;
    }
    std::vector<int> mark(top+1);
    for (Int two=1; two*two<=top; two*=2) {
        for (Int v=two; v*v<=top; v*=3) {
            for (int d=1; d<=top/(v*v); d+=2) {
                if (d%3) mark[v*v*d]=static_cast<int>(v)*mu[d];
            }
        }
    }

    std::vector<Int> area(top+1);
    std::vector<int> hull{0}, no_free_width;
    std::vector<Int> power_counts(28);
    int last_hull = 0, largest_power = 0, largest_head = 0;
    Int mass = 0, nonpositive_full = 0, cheaper_than_full = 0;
    for (int n=1; n<=top; ++n) {
        area[n]=area[n-1]+mass;
        mass+=mark[n];
        const auto price=[&](int width) {
            return width*mass-(area[n]-area[n-width]);
        };
        // The last edge of the lower convex hull maximizes the incoming chord slope.
        while (hull.size()>=2) {
            const int a=hull[hull.size()-2], b=hull.back();
            if (Wide(area[n]-area[b])*(b-a)>Wide(area[b]-area[a])*(n-b)) break;
            hull.pop_back();
        }
        const int left=hull.back();
        if (price(n-left)>0) no_free_width.push_back(n);
        auto full=price(n);
        nonpositive_full+=(full<=0);
        cheaper_than_full+=(full>0 && price(n-left)<=0);
        int k=0, h=1;
        while (price(h)>0 && h<n) {++k; h=std::min(2*h,n);}
        if (price(h)<=0) {
            ++power_counts[k];
            if (h>largest_power) {largest_power=h; largest_head=n;}
        }
        hull.push_back(n);
        last_hull=n-left;
    }
    std::cout<<"{\"through\":"<<top<<",\"last_mass\":"<<mass
             <<",\"last_tangent_width\":"<<last_hull<<",\"no_nonpositive_width\":[";
    for (std::size_t k=0;k<no_free_width.size();++k) std::cout<<(k?",":"")<<no_free_width[k];
    std::cout<<"],\"nonpositive_full_head_count\":"<<nonpositive_full
             <<",\"rescued_when_full_is_positive\":"<<cheaper_than_full
             <<",\"largest_first_success_in_doubling_search\":["<<largest_head<<','<<largest_power
             <<"],\"counts_by_doubling_index\":[";
    for (std::size_t k=0;k<power_counts.size();++k) std::cout<<(k?",":"")<<power_counts[k];
    std::cout<<"]}\n";
}
