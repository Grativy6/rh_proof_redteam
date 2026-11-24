// Independent exact convolution and norm for the order-125 Jacobi sum.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

using Int = std::int64_t;
constexpr int m = 125, q = 2179, f = m*q, modulus = 625, r = 20*f+1;
using Poly = std::vector<int>;

static int mod(Int a, int p) {
    a %= p;
    return int(a < 0 ? a+p : a);
}

static int power(Int a, int n, int p) {
    Int out=1;
    for (a=mod(a,p); n; n>>=1, a=a*a%p)
        if (n&1) out=out*a%p;
    return int(out);
}

static bool prime(int n) {
    for (int p=2; Int(p)*p<=n; ++p) if(n%p==0) return false;
    return n>=2;
}

template<int P> static void transform(Poly& a, bool inverse) {
    const int n=int(a.size());
    for(int i=1,j=0;i<n;++i) {
        int bit=n>>1;
        for (; j&bit; bit>>=1) j^=bit;
        j^=bit;
        if(i<j) std::swap(a[i],a[j]);
    }
    for(int len=2;len<=n;len<<=1) {
        int root=power(3,(P-1)/len,P);
        if(inverse) root=power(root,P-2,P);
        for(int i=0;i<n;i+=len) {
            Int x=1;
            for(int j=0;j<len/2;++j) {
                int u=a[i+j], v=int(a[i+j+len/2]*x%P);
                a[i+j]=u+v>=P ? u+v-P : u+v;
                a[i+j+len/2]=u-v<0 ? u-v+P : u-v;
                x=x*root%P;
            }
        }
    }
    if(inverse) {
        int inv=power(n,P-2,P);
        for(auto& x:a) x=int(Int(x)*inv%P);
    }
}

template<int P> static Poly modular_convolution(const Poly& a,const Poly& b) {
    int n=1;while(n<2*f) n<<=1;
    const int omega=power(3,(P-1)/n,P);
    if((P-1)%n || power(omega,n/2,P)!=P-1)
        throw std::runtime_error("no primitive transform root");
    Poly A(n), B(n);
    std::copy(a.begin(),a.end(),A.begin());
    std::copy(b.begin(),b.end(),B.begin());
    transform<P>(A,false);transform<P>(B,false);
    for(int i=0;i<n;++i) A[i]=int(Int(A[i])*B[i]%P);
    transform<P>(A,true);
    for(int k=0;k<f;++k) A[k]=(A[k]+A[k+f])%P;
    A.resize(f);
    return A;
}

static Poly multiply(const Poly& a,const Poly& b) {
    constexpr int p=998244353, s=1004535809;
    const Int bound=Int(f)*(modulus-1)*(modulus-1);
    if(bound>=Int(p)*s) throw std::runtime_error("insufficient CRT range");
    Poly A=modular_convolution<p>(a,b);
    Poly B=modular_convolution<s>(a,b);
    int inv=power(p,s-2,s);
    for(int i=0;i<f;++i) {
        Int z=A[i]+Int(p)*mod(Int(B[i]-A[i])*inv,s);
        if(z>bound) throw std::runtime_error("integer convolution bound violated");
        A[i]=int(z%modulus);
    }
    return A;
}

static Poly conjugate(const Poly& a,int u) {
    Poly b(f);
    for(int i=0,j=0;i<f;++i) {
        b[j]=a[i];
        j+=u;if(j>=f) j-=f;
    }
    return b;
}

int main(int argc,char** argv) {
    try {
        if(argc!=2) throw std::runtime_error("usage: jacobi_norm OUTPUT");
        if(!prime(r) || !prime(q) || !prime(998244353) || !prime(1004535809))
            throw std::runtime_error("prime check");
        for(int p:{2,5,q})
            if(power(2,(r-1)/p,r)==1) throw std::runtime_error("wrong primitive root");
        Poly logs(r,-1), a(f);
        for(int i=0,x=1;i<r-1;++i) {
            if(logs[x]>=0) throw std::runtime_error("log cycle repeated");
            logs[x]=i%f;x=int(Int(x)*2%r);
        }
        for(int x=2;x<r;++x) {
            int i=mod(-logs[x]-logs[r+1-x],f);
            a[i]=(a[i]+1)%modulus;
        }
        int h=1+m*mod(Int(4)*power(m,q-2,q),q);
        if(power(h,1089,f)!=1 || power(h,363,f)==1 || power(h,99,f)==1)
            throw std::runtime_error("wrong norm subgroup");
        int size=1;
        for(int factor:{3,11,3,11}) {
            Poly v=a;
            for(int i=1;i<factor;++i) v=multiply(v,conjugate(a,power(h,size*i,f)));
            a.swap(v);size*=factor;
        }
        if(size!=1089 || a!=conjugate(a,h)) throw std::runtime_error("norm invariance");
        int nonsquare=2;while(power(nonsquare,(q-1)/2,q)==1) ++nonsquare;
        const int root=264;
        if((root*root+q)%modulus) throw std::runtime_error("local square root");
        int period=mod(Int(root-1)*313,modulus); // 2*313 = 1 mod 625.
        auto at=[&](int i,int j) {
            return a[i+m*mod(Int(j-i)*power(m,q-2,q),q)];
        };
        std::ofstream out(argv[1]);
        out<<"[";
        for(int sign=0;sign<2;++sign) {
            out<<(sign?",[":"[");
            int u=sign?mod(-1-period,modulus):period;
            for(int i=0;i<m;++i) {
                int x=mod(at(i,0)+Int(u)*at(i,1)-Int(1+u)*at(i,nonsquare),modulus);
                if(i)out<<",";
                out<<x;
            }
            out<<"]";
        }
        out<<"]\n";
        if(!out) throw std::runtime_error("could not write norm");
        std::cout<<"All 1089 square conjugates verified in the integral group ring modulo 625.\n";
    } catch(const std::exception& e) {
        std::cerr<<e.what()<<"\n";return 1;
    }
}
