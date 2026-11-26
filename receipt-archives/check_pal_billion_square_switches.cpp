// Check the first billion and follow exactly the same switches through the next billion.
// Build with c++ -O3 -std=c++20 check_pal_billion_square_switches.cpp -o square-switches
#include <algorithm>
#include <bit>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Count = std::int64_t;
constexpr int first_limit = 1'000'000'000;
constexpr int limit = 2'000'000'000;

int integer_root(int n) {
    int r = static_cast<int>(std::sqrt(n));
    while (Count(r + 1) * (r + 1) <= n) ++r;
    while (Count(r) * r > n) --r;
    return r;
}

std::vector<int> primes_through(int n) {
    std::vector<bool> prime(n + 1, true);
    std::vector<int> result;
    for (int p = 2; p <= n; ++p) {
        if (!prime[p]) continue;
        result.push_back(p);
        for (Count m = Count(p) * p; m <= n; m += p) prime[m] = false;
    }
    return result;
}

// Each odd composite gets an actual divisor. Its quotient is strictly smaller
// and was priced earlier. An odd integer with no such divisor is prime.
std::vector<std::int8_t> odd_liouville(int n, const std::vector<int>& primes) {
    std::vector<std::int8_t> odd((n + 1) / 2);
    constexpr int block_size = 1 << 17;
    std::vector<std::uint16_t> divisor(block_size);
    int odd_count = static_cast<int>(odd.size());
    for (int base = 0; base < odd_count; base += block_size) {
        int count = std::min(block_size, odd_count - base);
        int low = 2 * base + 1;
        int high = low + 2 * (count - 1);
        std::fill_n(divisor.begin(), count, 0);
        for (int p : primes) {
            if (p == 2) continue;
            if (Count(p) * p > high) break;
            Count first = std::max(Count(p) * p, Count((low + p - 1) / p) * p);
            if (first % 2 == 0) first += p;
            for (Count m = first; m <= high; m += 2 * p) {
                divisor[(m - low) / 2] = static_cast<std::uint16_t>(p);
            }
        }
        for (int j = 0; j < count; ++j) {
            int m = low + 2 * j;
            if (m == 1) odd[base + j] = 1;
            else if (divisor[j] == 0) odd[base + j] = -1;
            else odd[base + j] = -odd[(m / divisor[j]) / 2];
        }
    }
    return odd;
}

int at(int m, const std::vector<std::int8_t>& odd) {
    int twos = std::countr_zero(static_cast<unsigned>(m));
    int sign = odd[(m >> twos) / 2];
    return twos % 2 == 0 ? sign : -sign;
}

struct Walk {
    Count value = 0, positive_area = 0, negative_area = 0;
    int positive_count = 0, first_positive_after_one = 0;
    int maximum_after_one = -1, first_maximum = 0;

    void add(int n, int step) {
        value += step;
        if (value > 0) {
            positive_area += value;
            ++positive_count;
            if (n > 1 && first_positive_after_one == 0) first_positive_after_one = n;
        } else {
            negative_area -= value;
        }
        if (n > 1 && value > maximum_after_one) {
            maximum_after_one = static_cast<int>(value);
            first_maximum = n;
        }
    }

    void print() const {
        std::cout << "{\"last\":" << value << ",\"positive_area\":" << positive_area
                  << ",\"negative_area\":" << negative_area << ",\"positive_prefixes\":" << positive_count
                  << ",\"first_positive_after_one\":" << first_positive_after_one
                  << ",\"maximum_after_one\":" << maximum_after_one
                  << ",\"first_maximum\":" << first_maximum << "}";
    }
};

int main() {
    const auto primes = primes_through(integer_root(limit));
    std::vector<int> changed;
    for (int p : primes) {
        if (Count(p) * p > first_limit / 2 && changed.size() < 415) changed.push_back(p);
    }
    if (changed.size() != 415) throw std::runtime_error("Insufficient proper square positions");
    const auto odd = odd_liouville(limit, primes);
    Walk original, repaired, seventeen;
    // Below two billion no changed square can share a multiple with another
    // changed square, and none recurs to its own fourth power.
    std::vector<int> events;
    for (int p : changed) {
        Count square = Count(p) * p;
        for (Count m = square; m <= limit; m += square) events.push_back(static_cast<int>(m));
    }
    std::sort(events.begin(), events.end());
    if (std::adjacent_find(events.begin(), events.end()) != events.end())
        throw std::runtime_error("Unexpected overlap between switched squares");
    Walk first_original, first_repair, first_seventeen;
    std::size_t used = 0;
    Count offset = 0;
    int positive_step_edits = 0, negative_step_edits = 0;
    for (int n = 1; n <= limit; ++n) {
        int step = at(n, odd);
        bool toggle = used < events.size() && n == events[used];
        if (toggle) {
            ++used;
            offset -= 2*step;
            if (step > 0) ++positive_step_edits;
            else ++negative_step_edits;
        }
        original.add(n, step);
        repaired.add(n, toggle ? -step : step);
        if (repaired.value != original.value + offset)
            throw std::runtime_error("Local square correction did not match its full prefix");
        bool flip17 = (n % 289 == 0) ^ (n % 83521 == 0) ^ (n % 24137569 == 0);
        seventeen.add(n, flip17 ? -step : step);
        if (n == first_limit) {
            first_original = original;
            first_repair = repaired;
            first_seventeen = seventeen;
            if (positive_step_edits != 415 || negative_step_edits != 0)
                throw std::runtime_error("First-billion edit support mismatch");
        }
    }
    std::cout << "{\"last_integer\":" << first_limit << ",\"changed_primes\":" << changed.size()
              << ",\"first_changed_prime\":" << changed.front()
              << ",\"last_changed_prime\":" << changed.back() << ",\"ordinary\":";
    first_original.print();
    std::cout << ",\"large_square_switches\":";
    first_repair.print();
    std::cout << ",\"only_17_negative\":";
    first_seventeen.print();
    std::cout << ",\"after_revisits\":{\"last_integer\":" << limit
              << ",\"positive_steps_flipped\":" << positive_step_edits
              << ",\"negative_steps_flipped\":" << negative_step_edits << ",\"ordinary\":";
    original.print();
    std::cout << ",\"same_fixed_switches\":";
    repaired.print();
    std::cout << ",\"only_17_negative\":";
    seventeen.print();
    std::cout << "}";
    std::cout << "}\n";
}
