// Read every original physical coefficient on either side of an occupied head, starting at that head.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int=std::int64_t;
using Wide=__int128_t;

std::string decimal(Wide v) {
    if (v<0) return "-"+decimal(-v);
    std::string s;
    do {s.push_back(static_cast<char>('0'+v%10)); v/=10;} while (v);
    std::reverse(s.begin(),s.end());
    return s;
}
int main(int argc,char** argv) {
    if (argc!=4 && argc!=5) return 2;
    const std::string direction=argc==5 ? argv[4] : "past";
    if (direction!="past" && direction!="future") return 2;
    const bool past=direction=="past";
    const Int root=std::stoll(argv[1]), rough=std::stoll(argv[2]), limit=std::stoll(argv[3]);
    if (root<1 || rough<1 || Wide(root)*root*rough>100000000000000LL) return 2;
    const Int head=root*root*rough;
    if (limit<1 || limit>head) return 2;
    const Int last=past ? head : head+limit-1;
    Int bound=static_cast<Int>(std::sqrt(static_cast<long double>(last)));
    while ((bound+1)*(bound+1)<=last) ++bound;
    while (bound*bound>last) --bound;
    std::vector<bool> composite(bound+1);
    std::vector<int> primes;
    for (int p=2;p<=bound;++p) if (!composite[p]) {
        if (p>=5) primes.push_back(p);
        if (p<=bound/p) for (Int d=Int(p)*p;d<=bound;d+=p) composite[d]=true;
    }
    std::vector<Int> checkpoints{1,root/2,root,2*root,(11*root)/5,3*root,8*root,16*root,32*root,limit};
    std::sort(checkpoints.begin(),checkpoints.end());
    checkpoints.erase(std::unique(checkpoints.begin(),checkpoints.end()),checkpoints.end());

    Int signed_sum=0,absolute_sum=0,first_free=-1,first_unit=-1,head_mark=0;
    Wide charge=0,absolute_price=0;
    bool first=true;
    std::cout<<"{\"head\":"<<head<<",\"unit\":"<<root<<",\"rough\":"<<rough
             <<",\"direction\":\""<<direction<<"\",\"through_width\":"<<limit<<",\"samples\":[";
    constexpr Int block=300000;
    for (Int used=0;used<limit;used+=block) {
        const Int count=std::min(block,limit-used);
        const Int lo=past ? head-used-count+1 : head+used;
        const Int hi=lo+count-1;
        std::vector<Int> rest(count);
        std::vector<int> mark(count,1);
        for (Int k=0;k<count;++k) {
            Int d=lo+k;
            int v=1;
            for (int p:{2,3}) {
                while (d%(p*p)==0) {d/=p*p; v*=p;}
                if (d%p==0) {v=0;break;}
            }
            rest[k]=d; mark[k]=v;
        }
        for (int p:primes) {
            if (Int(p)*p>hi) break;
            for (Int k=(p-lo%p)%p;k<count;k+=p) {
                if (!mark[k]) continue;
                rest[k]/=p;
                if (rest[k]%p==0) mark[k]=0;
                else mark[k]=-mark[k];
            }
        }
        for (Int offset=0;offset<count;++offset) {
            const Int k=past ? count-1-offset : offset;
            const Int h=used+offset+1;
            const int a=rest[k]>1 ? -mark[k] : mark[k];
            if (h==1) {
                head_mark=a;
                if (std::abs(a)!=root) throw std::logic_error("head has different physical weight");
            }
            signed_sum+=a;
            absolute_sum+=std::abs(a);
            charge+=signed_sum;
            absolute_price+=absolute_sum;
            const Wide oriented=head_mark<0 ? -charge : charge;
            if (first_free<0 && oriented<=0) first_free=h;
            if (first_unit<0 && rough==1 && root*oriented<=Wide(h)*(h+1)) first_unit=h;
            if (std::binary_search(checkpoints.begin(),checkpoints.end(),h)) {
                if (!first) std::cout<<',';
                first=false;
                std::cout<<'['<<h<<','<<signed_sum<<','<<decimal(charge)<<','<<decimal(absolute_price)<<']';
            }
        }
    }
    std::cout<<"],\"head_mark\":"<<head_mark<<",\"first_nonpositive_oriented_price\":"<<first_free
             <<",\"first_unit_cost_at_square\":"<<first_unit<<"}\n";
}
