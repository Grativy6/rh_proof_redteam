// Right kernel over F_5 of an integer Matrix Market matrix minus a scalar diagonal.
// Build with c++ -O3 -march=native -fopenmp -std=c++17 discover_kernel.cpp -o discover_kernel
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Byte = std::uint8_t;

static Byte mod5(long long x) {
    int a = int(x % 5);
    return Byte(a < 0 ? a + 5 : a);
}

class Echelon {
    int m, n, stride, width;
    std::vector<Byte> data;
    std::vector<Byte*> row;
    std::vector<int> pivots;
    static constexpr int inverse[5] = {0,1,3,2,4};

    // x and y are reduced. This loop can run on packed bytes.
    static void add(const Byte* x, const Byte* y, Byte* out, int len) {
        #pragma omp simd
        for (int j=0; j<len; ++j) {
            unsigned a = unsigned(x[j]) + y[j];
            out[j] = Byte(a >= 5 ? a-5 : a);
        }
    }

    static void subtract(Byte* x, const Byte* y, int c, int start, int end) {
        for (int j=start; j<end; ++j)
            x[j] = Byte((x[j] + (5-c)*y[j]) % 5);
    }

public:
    Echelon(int rows, int cols, int panel_width)
        : m(rows), n(cols), stride(((cols+63)/64)*64), width(panel_width),
          data(std::size_t(rows)*stride, 0), row(rows) {
        for (int i=0; i<m; ++i) row[i] = data.data()+std::size_t(i)*stride;
    }

    void entry(int i, int j, long long a) {
        if (i<0 || i>=m || j<0 || j>=n) throw std::runtime_error("bad matrix index");
        row[i][j] = mod5(row[i][j]+a);
    }

    void reduce() {
        for (int start=0; start<n && int(pivots.size())<m; start+=width) {
            const int r = int(pivots.size());
            std::array<int,4> pos{};
            int k=0;
            for (int col=start; col<std::min(start+width,n) && r+k<m; ++col) {
                int candidate=r+k;
                while (candidate<m) {
                    int a=row[candidate][col];
                    for (int s=0; s<k; ++s) a-=row[candidate][pos[s]]*row[r+s][col];
                    if (a%5) break;
                    ++candidate;
                }
                if (candidate==m) continue;
                std::swap(row[r+k],row[candidate]);
                Byte* p=row[r+k];
                for (int s=0; s<k; ++s) if (p[pos[s]])
                    subtract(p,row[r+s],p[pos[s]],start,n);
                int c=inverse[p[col]];
                if (!c) throw std::runtime_error("zero pivot");
                if (c!=1) for (int j=start; j<n; ++j) p[j]=Byte(c*p[j]%5);
                for (int s=0; s<k; ++s) if (row[r+s][col])
                    subtract(row[r+s],p,row[r+s][col],start,n);
                pos[k++]=col;
                pivots.push_back(col);
            }
            if (!k || r+k==m) continue;
            int count=1;
            for (int s=0; s<k; ++s) count*=5;
            int len=n-start;
            int pitch=((len+63)/64)*64;
            std::vector<Byte> table(std::size_t(count)*pitch,0), negative(len);
            int base=1;
            for (int s=0; s<k; ++s) {
                for (int j=0; j<len; ++j) {
                    int a=row[r+s][start+j];
                    negative[j]=Byte(a ? 5-a : 0);
                }
                for (int i=0; i<4*base; ++i)
                    add(table.data()+std::size_t(i)*pitch,negative.data(),
                        table.data()+std::size_t(i+base)*pitch,len);
                base*=5;
            }
            // The selected rows form an identity matrix on the panel's pivot columns.
            #pragma omp parallel for schedule(static) if (m-r>384)
            for (int i=r+k; i<m; ++i) {
                int index=0;
                for (int s=k-1; s>=0; --s) index=5*index+row[i][pos[s]];
                if (index)
                    add(row[i]+start,table.data()+std::size_t(index)*pitch,row[i]+start,len);
            }
            if (start%2048==0) std::cerr<<"column "<<start<<", rank "<<pivots.size()<<"\n";
        }
    }

    void save(const std::string& path) const {
        std::ofstream out(path);
        if (!out) throw std::runtime_error("cannot open basis output");
        out<<n<<" "<<(n-int(pivots.size()))<<"\n";
        std::vector<bool> used(n,false);
        for (int p:pivots) used[p]=true;
        for (int free=0; free<n; ++free) if (!used[free]) {
            std::vector<Byte> x(n,0);
            x[free]=1;
            for (int i=int(pivots.size())-1; i>=0; --i) {
                int p=pivots[i];
                unsigned sum=0;
                #pragma omp simd reduction(+:sum)
                for (int j=p+1; j<n; ++j) sum+=unsigned(row[i][j])*x[j];
                x[p] = Byte((5-sum%5)%5);
            }
            for (Byte a:x) out<<char('0'+a);
            out<<"\n";
        }
        if (!out) throw std::runtime_error("incomplete basis output");
        std::cout<<"rank "<<pivots.size()<<", nullity "<<n-pivots.size()<<"\n";
    }
};

int main(int argc,char** argv) {
    try {
        if (argc!=4 && argc!=5) throw std::runtime_error("usage: discover_kernel matrix.mtx shift basis.txt [panel width 1..4]");
        int width=argc==5 ? std::stoi(argv[4]) : 4;
        if (width<1 || width>4) throw std::runtime_error("invalid panel width");
        std::ifstream in(argv[1]);
        std::string line;
        if (!std::getline(in,line)) throw std::runtime_error("empty matrix input");
        if (!line.empty() && line.back()=='\r') line.pop_back();
        if (line!="%%MatrixMarket matrix coordinate integer general")
            throw std::runtime_error("expected an integer, general Matrix Market file");
        do { if (!std::getline(in,line)) throw std::runtime_error("missing shape"); }
        while (line.empty() || line[0]=='%');
        int m,n; long long nz;
        std::istringstream header(line);
        if (!(header>>m>>n>>nz) || m<=0 || n<=0 || nz<0) throw std::runtime_error("invalid shape");
        int shift=std::stoi(argv[2]);
        if (shift && m!=n) throw std::runtime_error("shift requires square matrix");
        Echelon e(m,n,width);
        for (long long k=0;k<nz;++k) {
            int i,j; long long v;
            if (!(in>>i>>j>>v)) throw std::runtime_error("incomplete matrix");
            e.entry(i-1,j-1,v);
        }
        if (shift) for (int j=0;j<n;++j) e.entry(j,j,-shift);
        e.reduce(); e.save(argv[3]);
    } catch (const std::exception& e) { std::cerr<<e.what()<<"\n"; return 1; }
}
