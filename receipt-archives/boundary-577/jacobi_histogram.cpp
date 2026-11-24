// Count the Jacobi exponents n=-log_g(x(1-x)) modulo 256*577^2.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;
using Counts = std::vector<std::uint16_t>;
constexpr int p = 577, conductor = 256 * p * p;

int power(Int a, int exponent, int modulus) {
  Int value = 1;
  for (; exponent; exponent >>= 1, a = a * a % modulus)
    if (exponent & 1)
      value = value * a % modulus;
  return static_cast<int>(value);
}
std::vector<int> divisors(int n) {
  std::vector<int> primes;
  for (int k = 2; Int(k) * k <= n; ++k) {
    if (n % k)
      continue;
    primes.push_back(k);
    while (n % k == 0)
      n /= k;
  }
  if (n > 1)
    primes.push_back(n);
  return primes;
}
Counts quadratic_counts(int r, int g) {
  // t=x(1-x) has exactly 1+(1-4t|r) preimages in F_r when t is nonzero.
  std::vector<std::uint64_t> square((Int(r) + 63) / 64);
  Int v = 1;
  for (int i = 1; i <= (r - 1) / 2; ++i) {
    square[v / 64] |= (std::uint64_t(1) << (v % 64));
    v = (v + 2LL * i + 1) % r;
  }
  Counts out(conductor);
  int t = 1, k = 0;
  for (int j = 0; j < r - 1; ++j) {
    int d = static_cast<int>((1 - 4LL * t) % r);
    if (d < 0)
      d += r;
    int count = d == 0 ? 1 : 2 * int((square[d / 64] >> (d % 64)) & 1);
    if (out[k] > std::numeric_limits<std::uint16_t>::max() - count)
      throw std::runtime_error("bin overflow");
    out[k] += count;
    t = static_cast<int>(Int(t) * g % r);
    if (--k < 0)
      k = conductor - 1;
  }
  if (t != 1 || k)
    throw std::runtime_error("generator period");
  return out;
}
Counts log_counts(int r, int g) {
  std::vector<int> logs(r);
  int x = 1, k = 0;
  for (int i = 0; i < r - 1; ++i) {
    logs[x] = k;
    x = static_cast<int>(Int(x) * g % r);
    if (++k == conductor)
      k = 0;
  }
  if (x != 1 || k)
    throw std::runtime_error("generator period");
  Counts out(conductor);
  for (int i = 2; i < r; ++i) {
    int e = logs[i] + logs[r + 1 - i];
    if (e >= conductor)
      e -= conductor;
    e = e ? conductor - e : 0;
    if (out[e] == std::numeric_limits<std::uint16_t>::max())
      throw std::runtime_error("bin overflow");
    ++out[e];
  }
  return out;
}
int main(int argc, char **argv) {
  try {
    if (argc < 3 || argc > 4)
      throw std::runtime_error("usage: histogram PRIME OUTPUT [--logs]");
    if (argc == 4 && std::string(argv[3]) != "--logs")
      throw std::runtime_error("unknown option");
    int r = std::stoi(argv[1]);
    if (r % conductor != 1 || divisors(r) != std::vector<int>{r})
      throw std::runtime_error("prime must split");
    const auto factors = divisors(r - 1);
    int g = 2;
    while (!std::all_of(factors.begin(), factors.end(),
                        [&](int k) { return power(g, (r - 1) / k, r) != 1; }))
      ++g;
    Counts out = argc == 4 ? log_counts(r, g) : quadratic_counts(r, g);
    Int total = 0;
    for (auto n : out)
      total += n;
    if (total != r - 2)
      throw std::runtime_error("Jacobi count");
    std::ofstream stream(argv[2], std::ios::binary);
    stream.write(reinterpret_cast<const char *>(out.data()),
                 out.size() * sizeof(out[0]));
    if (!stream)
      throw std::runtime_error("output write");
    std::cout << r << " primitive " << g << " max bin "
              << *std::max_element(out.begin(), out.end()) << " sum " << total
              << "\n";
  } catch (const std::exception &e) {
    std::cerr << e.what() << "\n";
    return 1;
  }
}
