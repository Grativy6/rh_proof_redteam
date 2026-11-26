// Complete prefix search for six choices of the newest arithmetic labels.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Int = std::int64_t;

struct Window {
    std::string name;
    int peak_head = 1;
    Int peak_delta = 0;
    int last_positive = 0;
    int last_nonnegative = 0;
    Int last_delta = 0;
    Int positives = 0;

    void add(int n, Int delta) {
        last_delta = delta;
        if (delta >= 0) last_nonnegative = n;
        if (delta <= 0) return;
        ++positives;
        last_positive = n;
        // Compare the squared positive rise per unit of head without floating point.
        if (__int128(delta) * delta * peak_head > __int128(peak_delta) * peak_delta * n) {
            peak_head = n;
            peak_delta = delta;
        }
    }
};

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    const int top = std::stoi(argv[1]);
    if (top < 1 || top > 70000000) throw std::invalid_argument("head outside 1..70000000");
    std::vector<std::int8_t> mu(top + 1, 1);
    std::vector<bool> prime(top + 1, true);
    for (int p = 2; p <= top; ++p) {
        if (!prime[p]) continue;
        for (int n = p; n <= top; n += p) mu[n] = -mu[n];
        if (p > top / p) continue;
        for (int n = p*p; n <= top; n += p) prime[n] = false;
        for (int n = p*p; n <= top; n += p*p) mu[n] = 0;
    }
    std::vector<int> mass(top + 1);
    for (Int two = 1; two*two <= top; two *= 2) {
        for (Int v = two; v*v <= top; v *= 3) {
            for (int d = 1; d <= top/(v*v); d += 2) {
                if (d % 3) mass[v*v*d] = static_cast<int>(v)*mu[d];
            }
        }
    }
    std::array<Window,7> windows = {{
        {"half"}, {"quarter"}, {"sixteenth"}, {"one_256th"}, {"inverse_log_squared"}, {"square_root"}, {"mixed_two_three"}
    }};
    int root = 0;
    int bits = 0;
    for (int n = 1; n <= top; ++n) {
        if ((n & (n-1)) == 0) ++bits;
        if (Int(root+1)*(root+1) == n) ++root;
        mass[n] += mass[n-1];
        const std::array<int,6> width = {{
            (n+1)/2, (n+3)/4, (n+15)/16, (n+255)/256,
            (n+bits*bits-1)/(bits*bits), root
        }};
        for (std::size_t k = 0; k < width.size(); ++k) {
            windows[k].add(n, Int(mass[n])-mass[n-width[k]]);
        }
        windows.back().add(n, Int(mass[n])-mass[n/2]-mass[n/3]+mass[n/6]);
    }
    std::cout << "{\"top\":" << top << ",\"mass\":" << mass[top] << ",\"windows\":[";
    bool first = true;
    for (const Window& w : windows) {
        if (!first) std::cout << ',';
        first = false;
        std::cout << "{\"name\":\"" << w.name << "\",\"peak_head\":" << w.peak_head
                  << ",\"peak_delta\":" << w.peak_delta << ",\"last_positive\":" << w.last_positive
                  << ",\"last_nonnegative\":" << w.last_nonnegative << ",\"positive_heads\":" << w.positives << ",\"at_top\":" << w.last_delta << '}';
    }
    std::cout << "]}\n";
}
