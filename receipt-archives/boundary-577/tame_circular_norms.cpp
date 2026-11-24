// Circular-unit power residues in two independent cyclotomic degree-577 layers.
// Build with g++ -O3 -std=c++17. Arguments are the tame conductor prime and
// a rational prime splitting the full conductor 256 * 577^2 * q.
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Wide = __uint128_t;
constexpr int p = 577;
constexpr int D = 256;
constexpr int f = D * p;
constexpr int p2 = p * p;
using Groups = std::array<Word, p>;

bool is_prime(Word n) {
    if (n < 2 || (n % 2 == 0 && n != 2)) return false;
    for (Word a = 3; a <= n / a; a += 2) if (n % a == 0) return false;
    return true;
}

Word pow_mod(Word a, Word n, Word modulus) {
    Word value = 1;
    while (n) {
        if (n & 1) value = Wide(value) * a % modulus;
        a = Wide(a) * a % modulus;
        n >>= 1;
    }
    return value;
}

Word primitive_root(Word prime) {
    Word n = prime - 1;
    std::vector<Word> divisors;
    for (Word i = 2; i <= n / i; ++i) if (n % i == 0) {
        divisors.push_back(i);
        while (n % i == 0) n /= i;
    }
    if (n > 1) divisors.push_back(n);
    for (Word g = 2; g < prime; ++g) {
        bool good = true;
        for (Word a : divisors) if (pow_mod(g, (prime - 1) / a, prime) == 1) { good = false; break; }
        if (good) return g;
    }
    throw std::runtime_error("primitive root missing");
}

int inverse_mod(int a, int m) {
    int t = 0, u = 1, r = m, s = a % m;
    while (s) {
        int q = r / s;
        int next = r - q * s; r = s; s = next;
        next = t - q * u; t = u; u = next;
    }
    if (r != 1) throw std::runtime_error("noninvertible CRT factor");
    return (t % m + m) % m;
}

struct Field {
    Word r, one, neg_inverse, generator;
    explicit Field(Word prime) : r(prime) {
        if (r >= (Word(1) << 62) || !is_prime(r)) throw std::runtime_error("unsupported residue prime");
        one = (Wide(1) << 64) % r;
        Word inv = 1;
        for (int i = 0; i < 6; ++i) inv *= 2 - r * inv;
        neg_inverse = 0 - inv;
        generator = Wide(primitive_root(r)) * one % r;
    }
    Word mul(Word a, Word b) const {
        Wide t = Wide(a) * b;
        Word k = Word(t) * neg_inverse;
        Word x = (t + Wide(k) * r) >> 64;
        return x >= r ? x - r : x;
    }
    Word one_minus(Word x) const { return one >= x ? one - x : r + one - x; }
    Word power(Word a, Word n) const {
        Word v = one;
        while (n) {
            if (n & 1) v = mul(v, a);
            a = mul(a, a);
            n >>= 1;
        }
        return v;
    }
    std::vector<Word> roots(int n, int exponent = 1) const {
        Word step = power(power(generator, (r - 1) / n), exponent);
        std::vector<Word> table(n, one);
        for (int j = 1; j < n; ++j) table[j] = mul(table[j - 1], step);
        if (mul(table.back(), step) != one) throw std::runtime_error("root table");
        return table;
    }
};

struct Factor { int index, weight; };

std::vector<Factor> indices() {
    std::array<int, D> chi{};
    int v = 1, w = 1;
    for (int j = 0; j < 64; ++j) {
        chi[v] = chi[D - v] = w;
        v = 5 * v % D; w = w * 510 % p;
    }
    std::array<int, p> wt{};
    for (int j = 1; j < p; ++j) wt[j] = pow_mod(j, 296, p);
    std::vector<Factor> res;
    for (int j = 1; j < f; j += 2) if (j % p) res.push_back({j, chi[j % D] * wt[j % p] % p});
    return res;
}

Groups identity(const Field& field) {
    Groups g; g.fill(field.one); return g;
}

Word weighted(const Field& field, const Groups& g, bool teich = false) {
    Word result = field.one;
    for (int w = 1; w < p; ++w)
        result = field.mul(result, field.power(g[w], teich ? pow_mod(w, p, p2) : w));
    return result;
}

int residue(const Field& field, const std::vector<Word>& mu, Word a, int divisor) {
    Word x = field.power(a, (field.r - 1) / divisor);
    for (int i = 0; i < p; ++i) if (mu[i] == x) return i;
    throw std::runtime_error("power residue outside mu_p");
}

struct Derivative {
    Groups norm;
    int reading = 0;
    Word direct;
    explicit Derivative(const Field& field) : norm(identity(field)), direct(field.one) {}
    void add(const Field& field, const Groups& g, const std::vector<Word>& mu, int j) {
        for (int w = 1; w < p; ++w) norm[w] = field.mul(norm[w], g[w]);
        Word u = weighted(field, g);
        reading = (reading + (p - 1 - j) * residue(field, mu, u, p)) % p;
        direct = field.mul(direct, field.power(u, p - 1 - j));
    }
    void check(const Field& field, const std::vector<Word>& mu) const {
        if (reading != residue(field, mu, direct, p)) throw std::runtime_error("derivative mismatch");
    }
};

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::runtime_error("supply q and split prime r");
        Word input_q = std::stoull(argv[1]), r = std::stoull(argv[2]);
        if (input_q > 100000 || !is_prime(input_q) || (input_q-1) % p || !is_prime(r)
            || (r-1) % (Word(f) * p * input_q)) throw std::runtime_error("conductor mismatch");
        int q = int(input_q);
        Field field(r);
        auto mu = field.roots(p), base_roots = field.roots(f);
        auto factors = indices();
        Groups base = identity(field);
        for (auto a : factors) base[a.weight] = field.mul(base[a.weight], field.one_minus(base_roots[a.index]));
        int e = residue(field, mu, weighted(field, base, true), p2);

        auto dyadic = field.roots(D, inverse_mod(p2, D));
        auto cyclo = field.roots(p2, inverse_mod(D, p2));
        std::array<int, p> teich{};
        for (int t = 1; t < p; ++t) teich[t] = pow_mod(t, p, p2);
        Derivative wild(field), tame(field);
        for (int j = 0; j < p; ++j) {
            std::array<Word, p> z{};
            for (int t = 1; t < p; ++t) z[t] = cyclo[Word(teich[t]) * (1 + p*j) % p2];
            Groups g = identity(field);
            for (auto a : factors) {
                Word root = field.mul(dyadic[a.index % D], z[a.index % p]);
                g[a.weight] = field.mul(g[a.weight], field.one_minus(root));
            }
            wild.add(field, g, mu, j);
        }
        if (wild.norm != base) throw std::runtime_error("wild distribution");
        wild.check(field, mu);

        auto old_part = field.roots(f, inverse_mod(q, f));
        auto new_part = field.roots(q, inverse_mod(f, q));
        const int qgen = primitive_root(q);
        std::vector<std::vector<Word>> cosets(p);
        int x = 1;
        for (int j = 0; j < q - 1; ++j) {
            cosets[j % p].push_back(new_part[x]);
            x = Word(x) * qgen % q;
        }
        for (int j = 0; j < p; ++j) {
            Groups g = identity(field);
            for (auto a : factors) {
                Word v = field.one;
                for (Word h : cosets[j]) v = field.mul(v, field.one_minus(field.mul(old_part[a.index], h)));
                g[a.weight] = field.mul(g[a.weight], v);
            }
            tame.add(field, g, mu, j);
        }
        tame.check(field, mu);
        int zq = 0;
        for (auto a : factors) if (a.index == q % f) zq = a.weight;
        if (zq <= 1) throw std::runtime_error("required nontrivial Euler factor");
        for (int w = 1; w < p; ++w) {
            int shifted = w * inverse_mod(zq, p) % p;
            if (field.mul(tame.norm[w], base[shifted]) != base[w]) throw std::runtime_error("tame distribution");
        }
        std::cout << q << ' ' << r << ' ' << field.mul(field.generator, 1) << ' '
                  << e << ' ' << wild.reading << ' ' << tame.reading << '\n';
    } catch (const std::exception& ex) {
        std::cerr << ex.what() << '\n';
        return 1;
    }
}
