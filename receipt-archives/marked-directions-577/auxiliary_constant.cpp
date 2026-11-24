// Independent auxiliary Eisenstein constant, summed by residue classes modulo 1792.
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using Int = std::int64_t;
constexpr int ell=577, conductor=1792, weight=297;
int mod(Int a,int n){int b=int(a%n);return b<0?b+n:b;}
int power(Int a,int n,int p){
    Int v=1;
    for(;n>0;n>>=1,a=a*a%p) if(n&1)v=v*a%p;
    return int(v);
}
bool prime(int n){for(int j=2;Int(j)*j<=n;++j)if(n%j==0)return false;return n>=2;}
std::array<int,4> compute(int w,int generator){
    if(!prime(w)||w%ell!=1)throw std::runtime_error("invalid prime");
    std::array<int,256> psi{};int a=1,b=1;
    for(int j=0;j<64;++j){psi[a]=psi[256-a]=b;a=5*a%256;b=b*510%ell;}
    constexpr std::array<int,7> eta{0,1,1,-1,1,-1,-1};
    if(mod(eta[w%7]*psi[w%256],ell)!=1)throw std::runtime_error("character not split");
    std::array<int,ell> kernel{};
    int s=0,y=0;
    for(int i=0;i<ell;++i){
        kernel[s]=y;
        y=mod(y+Int(weight)*power(s,weight-1,ell),ell);
        s=(s+conductor)%ell;
    }
    if(s||y)throw std::runtime_error("difference recurrence did not close");
    // log(0) uses a discarded bucket.
    std::vector<std::uint16_t> logs(w,ell);
    a=1;b=0;
    for(int i=0;i<w-1;++i){
        if(logs[a]!=ell)throw std::runtime_error("not a generator");
        logs[a]=b;a=Int(a)*generator%w;
        if(++b==ell)b=0;
    }
    if(a!=1||b)throw std::runtime_error("wrong period");
    std::array<Int,ell+1> sums{};
    constexpr int inc=conductor%ell;
    for(int label=1;label<=conductor;++label){
        int ph=mod(psi[label%256]*eta[label%7],ell);
        if(!ph)continue;
        int z=label,t=label%ell;
        for(int j=0;j<w;++j){
            sums[logs[z]]+=ph*kernel[t];
            z+=conductor;if(z>=w)z-=w;
            t+=inc;if(t>=ell)t-=ell;
        }
    }
    std::array<int,4> ans{};
    for(int i=0;i<ell;++i){
        Int choose=1;
        for(int j=0;j<4;++j){
            ans[j]=mod(ans[j]+(sums[i]%ell)*(choose%ell),ell);
            choose=choose*(i-j)/(j+1);
        }
    }
    for(auto& x:ans)x=mod(-x*power(2*weight,ell-2,ell),ell);
    return ans;
}
int main(int argc,char** argv){
    try {
        if(argc!=2)throw std::runtime_error("usage: direct PRIME");
        int w=std::stoi(argv[1]);
        int g;std::array<int,4> check{};
        if(w==515839){g=3;check={0,348,343,309};}
        else if(w==2363393){g=3;check={0,187,42,360};}
        else if(w==12407809){g=22;check={0,291,216,361};}
        else throw std::runtime_error("unknown control prime");
        auto ans=compute(w,g);
        if(ans!=check)throw std::runtime_error("coefficient mismatch");
        std::cout<<w;for(auto x:ans)std::cout<<" "<<x;std::cout<<"\n";
    } catch(const std::exception& e){std::cerr<<e.what()<<"\n";return 1;}
}
