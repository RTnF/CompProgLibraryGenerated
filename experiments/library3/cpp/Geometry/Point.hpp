#pragma once
#include "Template/SmallTemplate.hpp"

template<class T = ll>
struct Point {
    T x, y;
    int8_t quadrant; // 0-index 象限
    Point(): x(0), y(0) { setQuadrant(); }
    Point(T x_, T y_): x(x_), y(y_) { setQuadrant(); }
    void setX(T x_) {
        x = x_;
        setQuadrant();
    }
    void setY(T y_) {
        y = y_;
        setQuadrant();
    }
    void setQuadrant() {
        int8_t xm = x < 0, ym = y < 0;
        // 0123
        // quadrant = (ym << 1) + (xm ^ ym);
        // 2301
        quadrant = (!ym << 1) + (xm ^ ym);
    }
};

template<class T>
bool operator<(const Point<T> &a, const Point<T> &b) {
    if(a.quadrant != b.quadrant) {
        return a.quadrant < b.quadrant;
    }
    T cross = a.x * b.y - b.x * a.y;
    if(cross != 0) {
        return cross > 0;
    } else if(a.x != b.x) {
        return a.x < b.x;
    } else {
        return a.y < b.y;
    }
}

template<class T>
ostream &operator<<(ostream &os, const Point<T> &p) {
    os << p.x << ' ' << p.y;
    return os;
}

template<class T = ll>
struct Point3 {
    T x, y, z;
    Point3(T x_, T y_, T z_): x(x_), y(y_), z(z_) {}
};
