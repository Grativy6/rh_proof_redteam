// Stream the actual physical marks and certify the primitive at the fourth-power knots.
// g++ -O3 -std=c++17 fourth_primitive.cpp -o fourth_primitive
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Wide=__int128_t;
constexpr Wide S=Wide{1}<<80;

std::string printable(Wide n) {
    if(n<0) return "-"+printable(-n);
    if(!n) return "0";
    std::string out;
    while(n) {out.push_back(static_cast<char>('0'+n%10)); n/=10;}
    std::reverse(out.begin(),out.end());
    return out;
}

struct Ledger {
    Wide mass=0, absolute=0, reciprocal=0;
    Wide w_min=Wide{1}<<120, primitive_min=Wide{1}<<120;
    int w_at=0, primitive_at=0, first_possible_negative=0, first_certified_negative=0;
    void push(int n,int a,Wide inv) {
        mass+=a; absolute+=std::abs(a); reciprocal+=a*inv;
        const Wide lower=reciprocal-absolute;
        if(lower<w_min) {w_min=lower;w_at=n;}
        if(n<2) return;
        const Wide b=Wide(n)*lower-S*mass;
        if(b<primitive_min) {primitive_min=b;primitive_at=n;}
        if(b<=0 && !first_possible_negative) first_possible_negative=n;
        if(Wide(n)*(reciprocal+absolute)-S*mass<0 && !first_certified_negative)
            first_certified_negative=n;
    }
    void state() const {
        std::cout<<"[\""<<printable(mass)<<"\",\""<<printable(absolute)
                 <<"\",\""<<printable(reciprocal)<<"\"]";
    }
    void report() const {
        std::cout<<"{\"minimum_harmonic_lower_over_S\":\""<<printable(w_min)<<"\",\"harmonic_at\":"<<w_at
                 <<",\"minimum_primitive_lower_over_S_from_two\":\""<<printable(primitive_min)
                 <<"\",\"primitive_at\":"<<primitive_at<<",\"first_possible_nonpositive_primitive_from_two\":"
                 <<first_possible_negative<<",\"first_certified_negative_primitive\":"<<first_certified_negative<<"}";
    }
};

int main(int argc,char**argv) {
    if(argc!=2) {std::cerr<<"Usage: fourth_primitive max_root\n";return 2;}
    const int J=std::stoi(argv[1]);
    if(J<2 || J>100) throw std::invalid_argument("max_root must be in [2,100]");
    const int N=2*J*J*J*J;
    std::vector<std::int8_t> mu(N+1,1);
    std::vector<bool> isprime(N+1,true);
    for(int p=2;p<=N;++p) if(isprime[p]) {
        for(int n=p;n<=N;n+=p) mu[n]=-mu[n];
        if(std::int64_t(p)*p<=N) {
            for(int n=p*p;n<=N;n+=p) isprime[n]=false;
            for(std::int64_t n=std::int64_t(p)*p;n<=N;n+=std::int64_t(p)*p) mu[n]=0;
        }
    }
    std::vector<int> knots;
    for(int j=1;j<=J;++j) {const int x=j*j*j*j;knots.push_back(x);knots.push_back(2*x);}
    std::sort(knots.begin(),knots.end());
    std::size_t next=0;
    Ledger physical,raw;
    std::cout<<"{\"maximum_root\":"<<J<<",\"scale\":\""<<printable(S)<<"\",\"knots\":[";
    for(int n=1;n<=N;++n) {
        int u=n,v=1;
        while(u%4==0) {u/=4;v*=2;}
        while(u%9==0) {u/=9;v*=3;}
        const int coeff=u%2 && u%3 ? v*mu[u] : 0;
        const int base=n%2 && n%3 ? mu[n] : 0;
        const Wide inv=(coeff||base) ? S/n : 0;
        physical.push(n,coeff,inv); raw.push(n,base,inv);
        if(n==knots[next]) {
            if(next) std::cout<<',';
            std::cout<<"["<<n<<',';physical.state();std::cout<<',';raw.state();std::cout<<']';
            ++next;
        }
    }
    std::cout<<"],\"physical\":";physical.report();std::cout<<",\"raw\":";raw.report();std::cout<<"}\n";
}
