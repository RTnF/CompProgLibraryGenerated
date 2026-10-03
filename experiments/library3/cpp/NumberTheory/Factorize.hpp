#pragma once
#include "Template/SmallTemplate.hpp"
#include "NumberTheory/IsPrime.hpp"

namespace in {
    vector<ull> factorize(ull n) {
        auto f = [n](ull x, ull c) -> ull { return ((__uint128_t)x * x + c) % n; };
        auto rho = [f](ull m, ull c) -> ull {
            ull x = 2, y = 2, d = 1;
            while(d == 1) {
                x = f(x, c);
                y = f(f(y, c), c);
                d = gcd(x > y ? x - y : y - x, m);
            }
            return d == m ? 0 : d;
        };
        vector<ull> factor;
        while(!(n & 1)) {
            factor.emplace_back(2);
            n >>= 1;
        }
        if(n <= 1) {
            return factor;
        }
        if(isPrime(n)) {
            factor.emplace_back(n);
            return factor;
        }
        ull r = 0;
        for(int i = 1; !r && i <= 3; ++i) {
            r = rho(n, i);
        }
        if(r) {
            auto f1 = factorize(r);
            auto f2 = factorize(n / r);
            factor.insert(factor.end(), f1.begin(), f1.end());
            factor.insert(factor.end(), f2.begin(), f2.end());
            return factor;
        } else {
            // fallback O(sqrt(n))
            for(ull i = 3; i * i <= n; i += 2) {
                while(n % i == 0) {
                    factor.emplace_back(i);
                    n /= i;
                }
            }
            if(n > 1) {
                factor.emplace_back(n);
            }
            return factor;
        }
        return factor;
    }
}; // namespace in

vector<ull> factorize(ull n) {
    auto f = in::factorize(n);
    sort(f.begin(), f.end());
    return f;
}
