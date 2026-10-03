#pragma once
#include "Template/SmallTemplate.hpp"

/**
 * @brief 剰余を取り[0, mod)に収めるint
 * based on ACL
 * @tparam mod 素数に限る
 */
template<uint32_t mod, enable_if_t<(2 <= mod)> * = nullptr>
class ModInt {
    uint32_t x;

public:
    ModInt(): x(0) {}
    template<class T, enable_if_t<is_signed_v<T>> * = nullptr>
    ModInt(T x_): x(x_ < 0 ? x_ % (ll)mod + (ll)mod : x_ % (ll)mod) {}
    template<class U, enable_if_t<!is_signed_v<U>> * = nullptr>
    ModInt(U x_): x(x_ % mod) {}

    uint32_t get() const { return x; }
    template<class T, enable_if_t<is_signed_v<T>> * = nullptr>
    void set(T x_) {
        x = x_ < 0 ? x_ % (ll)mod + (ll)mod : x_ % (ll)mod;
    }
    template<class U, enable_if_t<!is_signed_v<U>> * = nullptr>
    void set(U x_) {
        x = x_ % mod;
    }

    ModInt operator++(int) {
        ModInt y = *this;
        ++*this;
        return y;
    }
    ModInt &operator++() {
        x = x == mod - 1 ? 0u : x + 1;
        return *this;
    }
    ModInt operator--(int) {
        ModInt y = *this;
        --*this;
        return y;
    }
    ModInt &operator--() {
        x = x == 0u ? mod - 1 : x - 1;
        return *this;
    }
    ModInt &operator+=(const ModInt &y) {
        x += y.x;
        if(x >= mod) {
            x -= mod;
        }
        return *this;
    }
    ModInt &operator-=(const ModInt &y) {
        x -= y.x;
        if(x >= mod) {
            x += mod;
        }
        return *this;
    }
    ModInt &operator*=(const ModInt &y) {
        x = (ull)x * (ull)y.x % mod;
        return *this;
    }
    ModInt &operator/=(const ModInt &y) { return *this *= y.inv(); }
    ModInt operator+() const { return *this; }
    ModInt operator-() const { return ModInt(mod - x); }

    ModInt pow(ll n) const {
        if(n < 0) {
            return pow(-n).inv();
        }
        ModInt y = *this, r = 1;
        while(n) {
            if(n & 1) {
                r *= y;
            }
            y *= y;
            n >>= 1;
        }
        return r;
    }
    ModInt inv() const {
        assert(x);
        return pow(mod - 2);
    }

    friend ModInt operator+(const ModInt &a, const ModInt &b) { return ModInt(a) += b; }
    friend ModInt operator-(const ModInt &a, const ModInt &b) { return ModInt(a) -= b; }
    friend ModInt operator*(const ModInt &a, const ModInt &b) { return ModInt(a) *= b; }
    friend ModInt operator/(const ModInt &a, const ModInt &b) { return ModInt(a) /= b; }
    friend bool operator==(const ModInt &a, const ModInt &b) { return a.x == b.x; }
    friend bool operator!=(const ModInt &a, const ModInt &b) { return a.x != b.x; }

    friend istream &operator>>(istream &is, ModInt &m) {
        ll y;
        is >> y;
        m.set(y);
        return is;
    }
    friend ostream &operator<<(ostream &os, const ModInt &m) {
        os << m.x;
        return os;
    }
};

using mint = ModInt<998244353u>;
using mint1 = ModInt<1000000007u>;