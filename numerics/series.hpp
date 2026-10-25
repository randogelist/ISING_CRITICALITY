#ifndef ISING_CRITICALITY_SERIES_HPP
#define ISING_CRITICALITY_SERIES_HPP

#include <array>
#include <cmath>
#include <stdexcept>

// Literature-input asymptotic estimators; no threshold benchmark enters these functions.
// HJ: Hellmund & Janke, Phys. Rev. E 74, 051113 (2006), Eq. (12).
//     https://arxiv.org/abs/cond-mat/0607423
// BP: Butera & Pernici, Phys. Rev. E 86, 011139 (2012), Eq. (12).
//     https://arxiv.org/abs/1209.3592
// These truncations are NOT rigorous physical critical-point enclosures.
namespace pcd_series {

inline long double hj_fk(int q, int d, int order = 8) {
    if ((q != 1 && q != 2) || d < 3 || order < 0 || order > 8)
        throw std::invalid_argument("HJ requires q=1 or 2, d>=3, 0<=order<=8");
    const long double Q = q, s = 2.L*d - 1.L;
    const std::array<long double,9> a = {
        1.L, 0.L,
        (8.L - 3.L*Q)/2.L,
        3.L*(8.L - 3.L*Q)/2.L,
        3.L*(68.L - 31.L*Q + Q*Q)/2.L,
        (8664.L - 3798.L*Q - 11.L*Q*Q)/12.L,
        (78768.L - 36714.L*Q + 405.L*Q*Q - 50.L*Q*Q*Q)/12.L,
        (1476192.L - 685680.L*Q - 2760.L*Q*Q - 551.L*Q*Q*Q)/24.L,
        (7446864.L - 3524352.L*Q - 11204.L*Q*Q - 6588.L*Q*Q*Q
            - 9.L*Q*Q*Q*Q)/12.L
    };
    long double y = a[order];
    for (int k=order-1; k>=0; --k) y = y/s + a[k];
    // The paper's v=(e^K-1)/(e^K-1+q), NOT the FK odds e^K-1.
    const long double u = y/s;
    return Q*u/(1.L + (Q-1.L)*u);
}

inline long double bp12_ising_K(int d, int order = 12) {
    if (d < 3 || order < 0 || order > 12)
        throw std::invalid_argument("BP requires d>=3, 0<=order<=12");
    // The source denotes z=2d by q. Here q remains the Potts state count.
    const long double z = 2.L*d;
    const std::array<long double,13> a = {
        1.L, -1.L, -4.L/3.L, -13.L/3.L, -979.L/45.L,
        -2009.L/15.L, -176749.L/189.L, -6648736.L/945.L,
        -765907148.L/14175.L, -5446232381.L/14175.L,
        -829271458256.L/467775.L, 164976684314.L/22275.L,
        6495334834824112.L/638512875.L
    };
    long double t = a[order];
    for (int k=order-1; k>=0; --k) t = t/z + a[k];
    if (!(t>0.L)) throw std::domain_error("Nonpositive truncated BP temperature");
    return 1.L/(z*t);
}

inline long double bp12_fk(int d, int order = 12) {
    return -std::expm1(-2.L*bp12_ising_K(d,order));
}

} // namespace pcd_series
#endif
