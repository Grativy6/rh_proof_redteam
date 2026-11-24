// Exact norm by FLINT polynomial multiplication. Uses the square generator 4
// and a ternary decomposition of the 53309 conjugates.
#include <flint/nmod_poly.h>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>
#include <algorithm>
using Int=std::int64_t;
using Vec=std::vector<std::uint16_t>;
constexpr int m=125,q=106619,f=m*q,r=12*f+1,modulus=625;
int normalize(Int a,int p){a%=p;return int(a<0?a+p:a);}
int power(Int x,int n,int p){
    Int y=1;
    for(;n;n>>=1,x=x*x%p)if(n&1)y=y*x%p;
    return int(y);
}
Vec jacobi(){
    std::vector<int> log(r,-1);
    int inv=power(7,r-2,r),x=1,k=0;
    for(int j=0;j<r-1;++j){
        if(log[x]>=0)throw std::runtime_error("short residue cycle");
        log[x]=k;
        x=Int(x)*inv%r;
        k=k==0?f-1:k-1;
    }
    if(x!=1 || k)throw std::runtime_error("residue generator");
    Vec v(f,0);
    x=7;k=1;
    for(int j=1;j<r-1;++j){
        int index=normalize(-k-log[r+1-x],f);
        if(++v[index]==modulus)v[index]=0;
        x=Int(x)*7%r;
        if(++k==f)k=0;
    }
    return v;
}
Vec conjugate(const Vec& a,int g){
    Vec b(f);
    int j=0;
    for(int i=0;i<f;++i){
        b[j]=a[i];
        j+=g;
        if(j>=f)j-=f;
    }
    return b;
}
void import(nmod_poly_t dest,const Vec& src){
    for(int i=0;i<f;++i)dest->coeffs[i]=src[i];
    _nmod_poly_set_length(dest,f);
    _nmod_poly_normalise(dest);
}
Vec multiply(const Vec& a,const Vec& b){
    nmod_poly_t x,y,z;
    nmod_poly_init2(x,modulus,f);
    nmod_poly_init2(y,modulus,f);
    nmod_poly_init(z,modulus);
    import(x,a);import(y,b);nmod_poly_mul(z,x,y);
    Vec out(f);
    for(int i=0;i<f;++i){
        auto v=nmod_poly_get_coeff_ui(z,i)+nmod_poly_get_coeff_ui(z,i+f);
        out[i]=v%modulus;
    }
    nmod_poly_clear(z);nmod_poly_clear(y);nmod_poly_clear(x);
    return out;
}
Vec norm(const Vec& a,int n,int g){
    if(n==1)return a;
    if(n==2)return multiply(a,conjugate(a,g));
    int k=n/3;
    Vec z=norm(a,k,g);
    Vec t=multiply(z,conjugate(z,power(g,k,f)));
    t=multiply(t,conjugate(z,power(g,2*k,f)));
    for(int i=3*k;i<n;++i)t=multiply(t,conjugate(a,power(g,i,f)));
    return t;
}
int main(int argc,char** argv){
    try {
        if(argc!=2)throw std::runtime_error("usage: flint_norm OUTPUT");
        flint_set_num_threads(4);
        const int g=1+m*normalize(3LL*power(m,q-2,q),q);
        if(power(g,(q-1)/2,f)!=1 || g==1)throw std::runtime_error("wrong subgroup");
        Vec a=norm(jacobi(),(q-1)/2,g);
        if(a!=conjugate(a,g))throw std::runtime_error("norm invariance");
        int non=2;
        while(power(non,(q-1)/2,q)==1)++non;
        std::ofstream out(argv[1]);out<<"[";
        bool first=true;
        for(int j:{0,1,non}){
            out<<(first?"[":",[");first=false;
            for(int i=0;i<m;++i){
                int n=i+m*normalize(Int(j-i)*power(m,q-2,q),q);
                if(i)out<<",";
                out<<a[n];
            }
            out<<"]";
        }
        out<<"]\n";
        if(!out)throw std::runtime_error("output write");
        std::cout<<"Verified all 53309 conjugates modulo 625.\n";
    } catch(const std::exception& e){std::cerr<<e.what()<<"\n";return 1;}
}
