#include "../experiments/library/cpp/template/small_template.hpp"
#include "../library/number/square_matrix.hpp"
#include <random>
#include <vector>

int main() {
    std::mt19937_64 random(20261027);
    for (int n = 0; n <= 14; ++n) {
        for (int round = 0; round < 6; ++round) {
            std::vector<unsigned long long> a(n * n), b(n * n), c(n * n, 12345);
            for (auto &x : a) x = random();
            for (auto &x : b) x = random();
            // reference: accumulate in a different loop order (i, k, j); both wrap modulo 2^64
            std::vector<unsigned long long> expected(n * n, 0);
            for (int i = 0; i < n; ++i)
                for (int k = 0; k < n; ++k)
                    for (int j = 0; j < n; ++j) expected[i * n + j] += a[i * n + k] * b[k * n + j];
            cp::mat_mul(a, b, c, n);
            assert(c == expected);

            // entrywise sum / difference wrap modulo 2^64
            std::vector<unsigned long long> s = a, d = a;
            cp::mat_add_assign(s, b, n);
            cp::mat_sub_assign(d, b, n);
            for (int i = 0; i < n * n; ++i) {
                assert(s[i] == a[i] + b[i]);
                assert(d[i] == a[i] - b[i]);
            }
            cp::mat_sub_assign(s, b, n);
            assert(s == a);

            // zero and identity overwrite every entry
            std::vector<unsigned long long> z = a, id = a;
            cp::mat_zero(z, n);
            cp::mat_identity(id, n);
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j) {
                    assert(z[i * n + j] == 0);
                    assert(id[i * n + j] == (i == j ? 1ULL : 0ULL));
                }
            // negation: a + (-a) == 0, and -a == 0 - a entrywise
            std::vector<unsigned long long> ng = a, sum = a;
            cp::mat_negate(ng, n);
            for (int i = 0; i < n * n; ++i) assert(ng[i] == 0ULL - a[i]);
            cp::mat_add_assign(sum, ng, n);
            for (int i = 0; i < n * n; ++i) assert(sum[i] == 0);
            // I * A == A * I == A
            std::vector<unsigned long long> left(n * n), right(n * n);
            cp::mat_mul(id, a, left, n);
            cp::mat_mul(a, id, right, n);
            assert(left == a && right == a);
        }
    }
    // the two read-only arguments may be the same vector (squaring)
    std::vector<unsigned long long> m = {1, 1, 1, 0}, sq(4, 0);
    cp::mat_mul(m, m, sq, 2);
    assert((sq == std::vector<unsigned long long>{2, 1, 1, 1}));
    // Fibonacci by repeated multiplication stays exact up to the wrap-around of 2^64
    std::vector<unsigned long long> p = {1, 0, 0, 1}, q(4);
    for (int i = 0; i < 90; ++i) {
        cp::mat_mul(p, m, q, 2);
        p = q;
    }
    assert(p[1] == 2880067194370816120ULL);
    // the element type is a template parameter
    {
        std::vector<double> a = {1, 2, 3, 4}, b = {0.5, 0, 0, 2}, c(4);
        cp::mat_mul(a, b, c, 2);
        assert(c[0] == 0.5 && c[1] == 4 && c[2] == 1.5 && c[3] == 8);
        cp::mat_add_assign(a, b, 2);
        assert(a[0] == 1.5 && a[3] == 6);
        cp::mat_negate(b, 2);
        assert(b[0] == -0.5 && b[3] == -2);
        cp::mat_identity(a, 2);
        assert(a[0] == 1 && a[1] == 0 && a[2] == 0 && a[3] == 1);
    }
    // mat_equal
    {
        std::vector<unsigned long long> x = {1, 2, 3, 4}, y = x, z = {1, 2, 3, 5};
        assert(cp::mat_equal(x, y, 2) && !cp::mat_equal(x, z, 2) && cp::mat_equal(x, x, 2));
        std::vector<unsigned long long> long_a = {1, 2, 3, 4, 9}, long_b = {1, 2, 3, 4, 7};
        assert(cp::mat_equal(long_a, long_b, 2));
        assert(cp::mat_equal(x, z, 0));
        std::vector<double> d = {1.5, 2, 0, 1}, e = {1.5, 3, 0, 1};
        assert(cp::mat_equal(d, e, 1) && !cp::mat_equal(d, e, 2));
    }
    // mat_pow against repeated multiplication (reference loops written out), and the law A^(x + y) = A^x * A^y
    {
        std::mt19937_64 random(20261029);
        auto reference_mul = [](const std::vector<unsigned long long> &x, const std::vector<unsigned long long> &y, int n) {
            std::vector<unsigned long long> z(n * n, 0);
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j)
                    for (int k = 0; k < n; ++k) z[i * n + j] += x[i * n + k] * y[k * n + j];
            return z;
        };
        for (int round = 0; round < 400; ++round) {
            int n = (int)(random() % 7);
            std::vector<unsigned long long> a(n * n), r(n * n, 5), y(n * n, 7), t(n * n, 9);
            for (auto &x : a) x = random();
            std::vector<unsigned long long> keep = a;
            unsigned long long e = random() % 40;
            std::vector<unsigned long long> expect(n * n, 0);
            for (int i = 0; i < n; ++i) expect[i * n + i] = 1;
            for (unsigned long long k = 0; k < e; ++k) expect = reference_mul(expect, a, n);
            cp::mat_pow(a, r, y, t, n, e);
            assert(r == expect);
            assert(a == keep);
            unsigned long long e1 = random(), e2 = random() >> 1;
            std::vector<unsigned long long> p1(n * n), p2(n * n), p3(n * n);
            cp::mat_pow(a, p1, y, t, n, e1);
            cp::mat_pow(a, p2, y, t, n, e2);
            cp::mat_pow(a, p3, y, t, n, e1 + e2);  // e1 + e2 may wrap around 2^64: skip then
            if (e1 + e2 >= e1) assert(p3 == reference_mul(p1, p2, n));
        }
        // the Fibonacci matrix: [[1, 1], [1, 0]]^e has F(e + 1), F(e), F(e), F(e - 1)
        std::vector<unsigned long long> f = {1, 1, 1, 0}, r(4), y(4), t(4);
        cp::mat_pow(f, r, y, t, 2, 90);
        assert(r[1] == 2880067194370816120ULL);
        cp::mat_pow(f, r, y, t, 2, 0);
        assert(r[0] == 1 && r[1] == 0 && r[2] == 0 && r[3] == 1);
    }
    return 0;
}
