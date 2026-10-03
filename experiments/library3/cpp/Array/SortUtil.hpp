#pragma once
#include "Template/SmallTemplate.hpp"

/**
 * @brief 逆置換
 * 例：[2, 4, 0, 1, 3] -> [2, 3, 0, 4, 1]
 * @param v 0-indexed 順列
 */
template<class T>
vector<int> invPerm(const vector<T> &v) {
    int n = v.size();
    vector<int> inv(n, -1);
    for(int i = 0; i < n; i++) {
        assert(0 <= v[i] && v[i] < n);
        assert(inv[v[i]] == -1);
        inv[v[i]] = i;
    }
    return inv;
}

/**
 * @brief ソート結果を配列のindexで得る O(n log n)
 * 例：[3, 3, 1, 5, 2] -> [1(2), 2(4), 3(0), 3(1), 5(3)] -> [2, 4, 0, 1, 3]
 */
template<class T>
vector<int> argSort(const vector<T> &v) {
    vector<int> arg(v.size());
    iota(arg.begin(), arg.end(), 0);
    stable_sort(arg.begin(), arg.end(), [&](int a, int b) { return v[a] < v[b]; });
    return arg;
}

/**
 * @brief ソートでindexがどこに移動するか O(n log n)
 * 例：[3, 3, 1, 5, 2] -> [2, 3, 0, 4, 1]
 */
template<class T>
vector<int> invArgSort(const vector<T> &v) {
    return invPerm(argSort(v));
}

/**
 * @brief 座標圧縮 O(n log n)
 * 例：[3, 3, 1, 5, 2] -> [2, 2, 0, 3, 1] + offset
 * unzip: [1, 2, 3, 5]
 */
template<typename T>
vector<T> compress(const vector<T> &x, vector<T> &unzip, int offset = 0) {
    int n = x.size();
    vector<T> cmp(n);
    unzip = x;
    sort(unzip.begin(), unzip.end());
    unzip.erase(unique(unzip.begin(), unzip.end()), unzip.end());
    for(int i = 0; i < n; i++) {
        cmp[i] = lower_bound(unzip.begin(), unzip.end(), x[i]) - unzip.begin() + offset;
    }
    return cmp;
}

/**
 * @brief 座標圧縮 O(n log n)
 * 例：[3, 3, 1, 5, 2] -> [2, 2, 0, 3, 1] + offset
 */
template<typename T>
vector<T> compress(const vector<T> &x, int offset = 0) {
    vector<T> y = x;
    return compress(x, y, offset);
}