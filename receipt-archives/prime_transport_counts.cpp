// Count one-, two- and three-prime labels in each physical subinterval.
// Build with g++ -O3 -std=c++17 -fopenmp prime_transport_counts.cpp -lprimecount -lprimesieve
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

using Integer = std::uint64_t;

int main(int argc, char** argv) {
    try {
        if (argc != 6) {
            std::cerr << "Usage: prime_transport_counts A B subdivisions palette_limit threads\n";
            return 2;
        }
        const Integer left = std::stoull(argv[1]), right = std::stoull(argv[2]);
        const int subdivisions = std::stoi(argv[3]), limit = std::stoi(argv[4]), threads = std::stoi(argv[5]);
        if (limit < 5 || left >= right || right > std::numeric_limits<std::int64_t>::max()
            || subdivisions < 5 || subdivisions % 5 || threads < 1
            || right-left < static_cast<Integer>(subdivisions)
            || left <= static_cast<Integer>(limit)*limit)
            throw std::invalid_argument("Need five nonempty bins and all complementary primes above the palette");
        std::vector<Integer> factors{1}, primes;
        primesieve::generate_primes(5, limit, &primes);
        factors.insert(factors.end(), primes.begin(), primes.end());
        const size_t first_pair = factors.size();
        for (size_t i = 0; i < primes.size(); ++i)
            for (size_t j = i+1; j < primes.size(); ++j)
                factors.push_back(primes[i]*primes[j]);
        std::vector<Integer> cuts(subdivisions+1);
        for (int j = 0; j <= subdivisions; ++j)
            cuts[j] = left + (static_cast<unsigned __int128>(right-left)*j)/subdivisions;
        std::vector<std::vector<Integer>> counts(factors.size(), std::vector<Integer>(subdivisions));
        primecount::set_num_threads(1);
        primesieve::set_num_threads(1);
        // Each task owns one row. Count primes q with cuts[j] < r*q <= cuts[j+1].
        #pragma omp parallel for schedule(dynamic,1) num_threads(threads)
        for (int row = 0; row < static_cast<int>(factors.size()); ++row) {
            const Integer factor = factors[row];
            for (int j = 0; j < subdivisions; ++j) {
                const auto low = std::max<Integer>(limit, cuts[j]/factor), high = cuts[j+1]/factor;
                if (low < high) counts[row][j] = primesieve::count_primes(low+1, high);
            }
        }
        // Independently recompute each full row by subtracting two prime-counting values.
        for (size_t row = 0; row < factors.size(); ++row) {
            const auto factor = factors[row];
            const auto total = primecount::pi(std::max<Integer>(limit, right/factor))
                             - primecount::pi(std::max<Integer>(limit, left/factor));
            if (std::accumulate(counts[row].begin(), counts[row].end(), Integer{0}) != static_cast<Integer>(total))
                throw std::logic_error("Prime-count endpoints disagree for factor "+std::to_string(factor));
        }
        std::cout << "left,right,primes,donors,triples\n";
        for (int j = 0; j < subdivisions; ++j) {
            Integer donors = 0, triples = 0;
            for (size_t row = 1; row < first_pair; ++row) donors += counts[row][j];
            for (size_t row = first_pair; row < factors.size(); ++row) triples += counts[row][j];
            std::cout << cuts[j] << ',' << cuts[j+1] << ',' << counts[0][j] << ',' << donors << ',' << triples << '\n';
        }
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
