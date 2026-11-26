// Count marks n=c*q by their actual sign and retain a separately identifiable semiprime supply.
// g++ -O3 -std=c++17 -fopenmp large_prime_block.cpp -lprimesieve -lprimecount -o large_prime_block
#include <primecount.hpp>
#include <primesieve.hpp>
#include <algorithm>
#include <cstdint>
#include <exception>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>

using Int = std::int64_t;

struct Bin {
    Int positive = 0, negative = 0, offered = 0, five = 0;
    void add(const Bin& b) {
        positive += b.positive; negative += b.negative; offered += b.offered; five += b.five;
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 6) {
            std::cerr << "Usage: large_prime_block A B cofactor_limit subdivisions threads\n";
            return 2;
        }
        const Int A=std::stoll(argv[1]), B=std::stoll(argv[2]), C=std::stoll(argv[3]);
        const int bins=std::stoi(argv[4]), threads=std::stoi(argv[5]);
        if (A<1 || B<=A || C<1 || C>10000000 || static_cast<__int128>(C)*C>=A
            || bins<5 || bins%5 || bins>1000000 || threads<1 || threads>64
            || static_cast<__int128>(B-A)*bins>std::numeric_limits<Int>::max())
            throw std::invalid_argument("Invalid block, cofactor limit, bin count or thread count");
        // For c=v^2*u, strip the two smooth prime valuations and compute -v*mu(u).
        std::vector<int> mu(C+1,1);
        std::vector<bool> prime(C+1,true);
        prime[0]=prime[1]=false;
        for (Int p=2;p<=C;++p) {
            if (!prime[p]) continue;
            for (Int n=p;n<=C;n+=p) mu[n]=-mu[n];
            for (Int n=p*p;n<=C;n+=p*p) mu[n]=0;
            for (Int n=p*p;n<=C;n+=p) prime[n]=false;
        }
        std::vector<int> mark(C+1);
        for (Int c=1;c<=C;++c) {
            Int u=c, v=1;
            for (int p : {2,3}) {
                while (u%(p*p)==0) { u/=p*p; v*=p; }
            }
            if (u%2 && u%3) mark[c]=static_cast<int>(-v*mu[u]);
        }
        std::vector<std::vector<Bin>> local(threads,std::vector<Bin>(bins));
        primecount::set_num_threads(1);
        primesieve::set_num_threads(1);
        std::vector<Int> rows(C+1);
        #pragma omp parallel for schedule(dynamic,1) num_threads(threads)
        for (Int c=1;c<=C;++c) {
            if (!mark[c]) continue;
            auto& table=local[omp_get_thread_num()];
            const Int lo=A/c+1, hi=B/c;
            if (lo>hi) continue;
            const bool offer = c>=5 && c<=347 && prime[c];
            primesieve::iterator it(lo,hi);
            for (Int q=it.next_prime();q<=hi;q=it.next_prime()) {
                const Int n=c*q;
                const auto bin=static_cast<int>(((n-A)*bins-1)/(B-A));
                auto& entry=table[bin];
                if (mark[c]>0) entry.positive+=mark[c];
                else entry.negative-=mark[c];
                if (offer) { ++entry.offered; if (c==5) ++entry.five; }
                ++rows[c];
            }
        }
        // Independently count every eligible cofactor row again at its two endpoints.
        for (Int c=1;c<=C;++c) {
            if (!mark[c]) continue;
            if (rows[c]!=primecount::pi(B/c)-primecount::pi(A/c))
                throw std::runtime_error("Prime count disagrees at cofactor "+std::to_string(c));
        }
        std::cout<<"left,right,positive,negative,offered,five\n";
        for (int j=0;j<bins;++j) {
            Bin sum;
            for (const auto& table:local) sum.add(table[j]);
            std::cout<<A+(B-A)*j/bins<<','<<A+(B-A)*(j+1)/bins<<','<<sum.positive<<','
                     <<sum.negative<<','<<sum.offered<<','<<sum.five<<'\n';
        }
    } catch (const std::exception& error) { std::cerr<<error.what()<<'\n'; return 1; }
}
