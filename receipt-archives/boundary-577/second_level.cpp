// Local 577^2 cyclotomic Jacobi projection via FLINT and one degree-four
// unramified fiber.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <flint/nmod_poly.h>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
// Embed Y^4=t and z^m=1 using W=Y*z with W^(4m)=t^m.
// The kernel norm first visits the 128 tame 2-power embeddings, then the
// order-nine subgroup on z. The wild calculation keeps both the norm and
// the product whose j-th conjugate has exponent j.
using Int = std::int64_t;
using Vec = std::vector<std::uint32_t>;
constexpr int p = 577, c = 256, m = p * p, n = 4 * m, modulus = p * m,
              conductor = c * m;
int mod(Int x, int q) {
  int y = int(x % q);
  return y < 0 ? y + q : y;
}
int power(Int x, int k, int q) {
  Int v = 1;
  for (; k; k >>= 1, x = x * x % q)
    if (k & 1)
      v = v * x % q;
  return int(v);
}
struct Local {
  const int t = power(20, m, modulus);
  const int G = power(5, p, m);
  const int wrap = power(t, m, modulus);
  std::array<int, 64> ts{};
  std::vector<int> index = std::vector<int>(n);
  Vec to_w = Vec(n);
  Local() {
    for (int i = 0; i < 64; ++i)
      ts[i] = power(t, i, modulus);
    if (power(t, 32, modulus) != modulus - 1 || power(G, 576, m) != 1)
      throw std::runtime_error("Teichmuller root");
    for (int b = 0; b < 4; ++b)
      for (int j = 0; j < m; ++j) {
        int k = j + m * mod(b - j, 4);
        index[b * m + j] = k;
        to_w[b * m + j] = ts[mod((b - k) / 4, 64)];
      }
  }
  Vec one() const {
    Vec a(n);
    a[0] = 1;
    return a;
  }
  void fill(nmod_poly_t v, const Vec &a) const {
    for (int i = 0; i < n; ++i)
      v->coeffs[i] = a[i];
    _nmod_poly_set_length(v, n);
    _nmod_poly_normalise(v);
  }
  Vec mul(const Vec &a, const Vec &b) const {
    nmod_poly_t x, y, z;
    nmod_poly_init2(x, modulus, n);
    nmod_poly_init2(y, modulus, n);
    nmod_poly_init(z, modulus);
    fill(x, a);
    fill(y, b);
    nmod_poly_mul(z, x, y);
    Vec out(n);
    for (int i = 0; i < n; ++i)
      out[i] = (nmod_poly_get_coeff_ui(z, i) +
                Int(wrap) * nmod_poly_get_coeff_ui(z, n + i)) %
               modulus;
    nmod_poly_clear(z);
    nmod_poly_clear(y);
    nmod_poly_clear(x);
    return out;
  }
  Vec pw(const Vec &a, int e) const {
    if (!e)
      return one();
    Vec out = a;
    int top = 1;
    while (top <= e / 2)
      top *= 2;
    for (int b = top / 2; b; b /= 2) {
      out = mul(out, out);
      if (e & b)
        out = mul(out, a);
    }
    return out;
  }
  Vec act(const Vec &a, int h, int Y = 1) const {
    // W^i=(Yz)^i -> Y^(i*Y) z^(i*h); reduce modulo W^(4m)=t^m.
    Vec b(n);
    int u = h + m * mod(Y - h, 4), j = 0;
    for (int i = 0; i < n; ++i) {
      int e = mod((Int(i) * Y - j) / 4, 64);
      b[j] = Int(a[i]) * ts[e] % modulus;
      j += u;
      if (j >= n)
        j -= n;
    }
    return b;
  }
  Vec kernel(const std::string &file, int r) const {
    std::ifstream in(file, std::ios::binary);
    if (!in)
      throw std::runtime_error("histogram file");
    std::vector<std::uint16_t> h(conductor), rows(conductor);
    in.read(reinterpret_cast<char *>(h.data()), Int(conductor) * sizeof(h[0]));
    if (!in)
      throw std::runtime_error("histogram read");
    Int total = 0;
    for (int i = 0; i < conductor; ++i) {
      rows[Int(i % c) * m + i % m] = h[i];
      total += h[i];
    }
    if (total != r - 2)
      throw std::runtime_error("histogram sum");
    std::vector<std::uint16_t>().swap(h);
    std::array<int, c> exp{};
    int v = 1;
    for (int i = 0; i < 64; ++i) {
      exp[v] = exp[c - v] = i;
      v = v * 5 % c;
    }
    Vec norm;
    std::vector<Int> partial(n);
    for (int v0 = 1; v0 < 64; v0 += 2) {
      std::fill(partial.begin(), partial.end(), 0);
      for (int i = 0; i < c; ++i) {
        int e = i * v0 % c, b = e % 4;
        Int s = ts[e / 4];
        Int *dest = partial.data() + b * m;
        auto row = rows.data() + i * m;
        for (int j = 0; j < m; ++j)
          dest[j] += s * row[j];
      }
      for (auto &x : partial)
        x %= modulus;
      int q = 1;
      for (int k = 0; k < 4; ++k, q = q * (p % c) % c) {
        int v1 = v0 * q % c, autom = power(G, 441 * exp[v1], m), j2 = 0;
        Vec part(n);
        for (int b = 0; b < 4; ++b) {
          Int corr = ts[mod((q - 1) * b / 4, 64)];
          for (int j = 0; j < m; ++j) {
            int k1 = b * m + j2;
            part[index[k1]] =
                partial[b * m + j] * corr % modulus * to_w[k1] % modulus;
            j2 += autom;
            if (j2 >= m)
              j2 -= m;
          }
        }
        if (norm.empty())
          norm.swap(part);
        else
          norm = mul(norm, part);
      }
      if (v0 % 16 == 15)
        std::cout << "tame fibers " << (v0 + 1) * 2 << "/128\n" << std::flush;
    }
    int h1 = power(G, 64, m);
    for (int k : {1, 3}) {
      Vec v = norm;
      norm = mul(norm, act(v, power(h1, k, m)));
      norm = mul(norm, act(v, power(h1, 2 * k, m)));
    }
    if (norm != act(norm, h1))
      throw std::runtime_error("order-nine norm");
    if (norm != act(norm, power(G, 441 * exp[p % c], m), p % c))
      throw std::runtime_error("coupled Frobenius");
    return norm;
  }
  Vec tame(Vec z) const {
    const int sig = power(G, 575, m);
    for (int h = 1; h < 64; h *= 2) {
      z = mul(z, pw(act(z, power(sig, h, m)), power(t, h, modulus)));
    }
    return z;
  }
  std::pair<Vec, Vec> wild(const Vec &a, int d) const {
    if (d == 1)
      return {a, one()};
    const int h = d / 2;
    auto r = wild(a, h);
    int u = power(1 + p, h, m);
    Vec T = act(r.first, u);
    Vec N = mul(r.first, T);
    Vec V = mul(mul(r.second, act(r.second, u)), pw(T, h));
    if (d % 2) {
      Vec t0 = act(a, power(1 + p, 2 * h, m));
      N = mul(N, t0);
      V = mul(V, pw(t0, 2 * h));
    }
    return {std::move(N), std::move(V)};
  }
  void save(const std::string &name, const Vec &x) const {
    std::ofstream o(name, std::ios::binary);
    o.write(reinterpret_cast<const char *>(x.data()), Int(n) * sizeof(x[0]));
    if (!o)
      throw std::runtime_error("write " + name);
  }
  Vec read(const std::string &name) const {
    std::ifstream in(name, std::ios::binary);
    Vec x(n);
    in.read(reinterpret_cast<char *>(x.data()), Int(n) * sizeof(x[0]));
    if (!in)
      throw std::runtime_error("read " + name);
    return x;
  }
  void compute(int r, const std::string &file,
               const std::string &prefix) const {
    auto a = tame(kernel(file, r));
    std::cout << "tame eigenspace\n" << std::flush;
    auto v = wild(a, p);
    std::cout << "wild norm and derivative\n" << std::flush;
    save(prefix + "-N.bin", v.first);
    save(prefix + "-V.bin", v.second);
  }
  void specialize(const std::string &prefix, int e) const {
    auto N = read(prefix + "-N.bin"), V = read(prefix + "-V.bin");
    int exponent = mod(-Int(p) * (e + 1), m);
    auto b = exponent ? mul(N, pw(V, exponent)) : std::move(N);
    auto s = pw(b, p - 1);
    save(prefix + "-e" + std::to_string(e) + ".bin", s);
  }
};
int main(int argc, char **argv) {
  try {
    flint_set_num_threads(4);
    Local L;
    std::string task = argc > 1 ? argv[1] : "";
    if (task == "build" && argc == 5)
      L.compute(std::stoi(argv[2]), argv[3], argv[4]);
    else if (task == "weight" && argc == 4)
      L.specialize(argv[2], std::stoi(argv[3]));
    else
      throw std::runtime_error(
          "use build PRIME HIST PREFIX or weight PREFIX E");
  } catch (const std::exception &e) {
    std::cerr << e.what() << "\n";
    return 1;
  }
}
