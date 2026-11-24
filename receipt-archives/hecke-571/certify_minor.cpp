// A positive, independently checkable nonsingularity certificate over F_125.
// Multiplication uses t^3+t+1; each field element encodes a+b*t+c*t^2 in base 5.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using U8 = std::uint8_t;
using U32 = std::uint32_t;
using U64 = std::uint64_t;

struct Field {
    U8 product[125][125]{}, diff[125][125]{}, inverse[125]{};
    U64 term[125][125]{};
    U32 packed[125]{};

    static unsigned mod5(int x) { return unsigned((x%5+5)%5); }
    static U8 reduce(U64 x, int bits) {
        U64 mask=(U64(1)<<bits)-1;
        return U8((x&mask)%5 + 5*(((x>>bits)&mask)%5) + 25*(((x>>(2*bits))&mask)%5));
    }

    Field() {
        for(int i=0;i<125;++i) {
            int a=i%5,b=i/5%5,c=i/25;
            packed[i]=a+(b<<10)+(c<<20);
            for(int j=0;j<125;++j) {
                int d=j%5,e=j/5%5,f=j/25;
                int k=b*f+c*e, h=c*f;
                int r=mod5(a*d-k), s=mod5(a*e+b*d-k-h), u=mod5(a*f+b*e+c*d-h);
                product[i][j]=U8(r+5*s+25*u);
                term[i][j]=U64(r)+(U64(s)<<20)+(U64(u)<<40);
                diff[i][j]=U8(mod5(a-d)+5*mod5(b-e)+25*mod5(c-f));
                if (product[i][j]==1) inverse[i]=U8(j);
            }
            if(i && !inverse[i]) throw std::runtime_error("field inverse failed");
        }
    }
};

struct Matrix {
    int n;
    std::vector<int> offset, col;
    std::vector<U8> value;
    explicit Matrix(const std::string& path) {
        std::ifstream f(path);std::string line;
        if(!std::getline(f,line)) throw std::runtime_error("missing matrix header");
        if(!line.empty() && line.back()=='\r') line.pop_back();
        if(line!="%%MatrixMarket matrix coordinate integer general") throw std::runtime_error("matrix format");
        do { if(!std::getline(f,line)) throw std::runtime_error("missing dimensions"); }
        while(line.empty()||line[0]=='%');
        int m,nz;std::istringstream hdr(line);
        if(!(hdr>>m>>n>>nz) || m!=n || n<1 || n>200000 || nz<0) throw std::runtime_error("matrix shape");
        std::vector<std::vector<std::pair<int,U8>>> rows(n);
        for(int t=0;t<nz;++t) {
            int i,j,a;if(!(f>>i>>j>>a)||i<1||i>n||j<1||j>n) throw std::runtime_error("matrix entry");
            U8 v=U8(Field::mod5(a)); if(v) rows[i-1].push_back({j-1,v});
        }
        offset.push_back(0);
        for(auto& r:rows) {
            int total=0;
            for(auto [j,a]:r) {total+=a;col.push_back(j);value.push_back(a);}
            if(4*total>=1024) throw std::runtime_error("packed lane overflow");
            offset.push_back(int(col.size()));
        }
    }
};

static U32 next(U32& state) {
    state ^= state<<13; state ^= state>>17; state ^= state<<5;return state;
}

static std::vector<U8> sequence(const Field& F,const Matrix& A,U32 seed) {
    int n=A.n;std::vector<U8> diagonal(n), left(n), result;
    std::vector<U32> x(n),y(n);U64 dot=0;
    for(int i=0;i<n;++i) {
        diagonal[i]=U8(1+next(seed)%124);
        left[i]=U8(next(seed)%125);
        U8 z=U8(next(seed)%125);x[i]=F.packed[z];
        dot+=F.term[left[i]][z];
    }
    result.push_back(Field::reduce(dot,20));
    for(int k=1;k<2*n;++k) {
        dot=0;
        #pragma omp parallel for schedule(static) reduction(+:dot)
        for(int i=0;i<n;++i) {
            U32 s=0;
            for(int j=A.offset[i];j<A.offset[i+1];++j) s+=A.value[j]*x[A.col[j]];
            U8 z=F.product[diagonal[i]][Field::reduce(s,10)];
            y[i]=F.packed[z]; dot+=F.term[left[i]][z];
        }
        x.swap(y);result.push_back(Field::reduce(dot,20));
    }
    return result;
}

static std::vector<U8> recurrence(const Field& f,const std::vector<U8>& a) {
    std::vector<U8> C{1}, B{1};int degree=0, delay=1;U8 last=1;
    for(int n=0;n<int(a.size());++n) {
        U64 sum=f.term[a[n]][1];
        for(int j=1;j<int(C.size());++j) sum+=f.term[C[j]][a[n-j]];
        U8 d=Field::reduce(sum,20);
        if(!d) {++delay;continue;}
        std::vector<U8> prev=C;
        U8 scale=f.product[d][f.inverse[last]];
        if(C.size()<B.size()+delay) C.resize(B.size()+delay,0);
        for(int j=0;j<int(B.size());++j)
            C[j+delay]=f.diff[C[j+delay]][f.product[scale][B[j]]];
        if(2*degree<=n) {degree=n+1-degree;B=std::move(prev);last=d;delay=1;}
        else ++delay;
    }
    C.resize(degree+1,0);
    return C;
}

int main(int argc,char** argv) {
    try {
        if(argc!=3) throw std::runtime_error("usage: certify_minor matrix.mtx nonzero_seed");
        U32 seed=U32(std::stoul(argv[2])); if(!seed) throw std::runtime_error("zero seed");
        Matrix a(argv[1]);Field f;
        auto s=sequence(f,a,seed);
        auto c=recurrence(f,s);
        std::cout<<"minor "<<a.n<<", recurrence degree "<<c.size()-1
                 <<", constant coefficient "<<int(c.back())<<", seed "<<seed<<"\n";
        if(c.size()!=std::size_t(a.n+1) || !c.back()) return 2;
    } catch(const std::exception& e) { std::cerr<<e.what()<<"\n"; return 1; }
}
