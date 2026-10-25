// ISING_CRITICALITY -- independent numerical evaluation of the PCD formulas.
// C++17, standard library only. No benchmark values are read by the estimators.
// Printed digits are floating-point evaluations, not certified physical digits.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include "series.hpp"
#include "pade.hpp"

namespace pcd {
using Real = long double;

Real odds_to_p(Real v) { return v / (1 + v); }
Real p_to_odds(Real p) { return p / (1 - p); }
Real ising_K_to_p(Real K) { return -std::expm1(-2 * K); }
Real potts_K_to_p(Real K) { return -std::expm1(-K); }

Real gp4(int q, int d) {
  if ((q != 1 && q != 2) || d < 3)
    throw std::invalid_argument("GP4 requires q=1 or q=2 and d>=3");
  const Real s = 2 * static_cast<Real>(d) - 1;
  const Real Q = q;
  const Real A = 1 + (8 - 3 * Q) / (2 * s * s)
      + 3 * (8 - 3 * Q) / (2 * s * s * s)
      + 3 * (68 - 31 * Q + Q * Q) / (2 * s * s * s * s);
  return Q * A / (s + (Q - 1) * A);
}

Real square_loop(int d) {
  if (d < 2) throw std::invalid_argument("square-loop requires d>=2");
  // expm1 avoids loss of relative precision when d is large.
  const Real xm1 = std::expm1(std::log(Real(2)) / d);
  const Real vB = 2 * xm1 / (1 - xm1);
  const Real tB = 2 * xm1 / (3 - xm1);
  const Real x2m1 = std::sqrt(Real(2)) - 1;
  const Real tB2 = 2 * x2m1 / (3 - x2m1);
  const Real ratio = tB / tB2;
  const Real delta = (static_cast<Real>(d) - 1) / 2 * std::log(Real(1.5))
      * ratio * ratio * ratio * ratio;
  return odds_to_p(vB * std::exp(delta));
}

Real estimate(int q, int d) {
  if (q < 1 || q > 3 || d < 2)
    throw std::invalid_argument("estimator domain: q=1,2,3 and integer d>=2");
  if (d == 2) return odds_to_p(std::sqrt(static_cast<Real>(q)));
  return q == 3 ? square_loop(d) : gp4(q, d);
}

const char* method(int q, int d) {
  return d == 2 ? "exact-square-lattice-anchor" :
      (q == 3 ? "square-loop-coexistence-model" : "GP4-continuous-model");
}

// Exact integer spin enumeration for a finite wired box [-R,R]^d.
// Boundary spins all have color zero. Boundary-boundary edges contribute the
// same factor to every spin state and are omitted, so normalized probabilities
// are unchanged. Histograms count states by the number of disagreeing edges.
// Integer coefficients are exact; their evaluation and root are floating-point.
struct WiredBox {
  int q, d, radius, interior, center;
  std::uint64_t configurations;
  std::vector<std::pair<int, int>> edges; // second=-1 means fixed boundary color 0
  std::vector<std::uint64_t> total, center_zero;

  WiredBox(int dimension, int R, int colors) : q(colors), d(dimension), radius(R) {
    if (q != 2 && q != 3)
      throw std::invalid_argument("wired spin enumeration supports q=2 or 3 only");
    if (d < 1 || d > 11 || R < 1 || R > 20)
      throw std::invalid_argument("finite domain: 1<=d<=11 and 1<=R<=20");
    constexpr std::uint64_t max_states = 1ULL << 24;
    const int side = 2 * R - 1;
    std::uint64_t count = 1;
    for (int j = 0; j < d; ++j) {
      count *= side;
      if (count > 24)
        throw std::invalid_argument("finite enumeration exceeds 24 interior vertices");
    }
    interior = static_cast<int>(count);
    configurations = 1;
    for (int i = 0; i < interior; ++i) {
      configurations *= q;
      if (configurations > max_states)
        throw std::invalid_argument("finite enumeration exceeds 2^24 spin assignments");
    }
    center = 0;
    int stride = 1;
    for (int j = 0; j < d; ++j) {
      center += (R - 1) * stride;
      for (int i = 0; i < interior; ++i) {
        const int c = (i / stride) % side;
        if (c == 0) edges.emplace_back(i, -1);
        if (c == side - 1) edges.emplace_back(i, -1);
        else edges.emplace_back(i, i + stride);
      }
      stride *= side;
    }
    total.assign(edges.size() + 1, 0);
    center_zero.assign(edges.size() + 1, 0);
    std::vector<int> spins(interior);
    for (std::uint64_t state = 0; state < configurations; ++state) {
      auto code = state;
      for (int i = 0; i < interior; ++i) {
        spins[i] = static_cast<int>(code % q);
        code /= q;
      }
      std::size_t disagreements = 0;
      for (const auto& edge : edges) {
        const int other = edge.second < 0 ? 0 : spins[edge.second];
        disagreements += (spins[edge.first] != other);
      }
      ++total[disagreements];
      if (spins[center] == 0) ++center_zero[disagreements];
    }
  }

  Real connection(Real p) const {
    if (p < 0 || p > 1) throw std::invalid_argument("p must be in [0,1]");
    if (p == 0) return 0;
    if (p == 1) return 1;
    const Real y = 1 - p;
    Real z = 0, numerator = 0;
    // Edwards-Sokal identity W=(q P(spin_center=0)-1)/(q-1).
    // Evaluate the numerator polynomial directly to reduce cancellation.
    for (std::size_t k = total.size(); k-- > 0;) {
      z = z * y + static_cast<Real>(total[k]);
      numerator = numerator * y + q * static_cast<Real>(center_zero[k])
          - static_cast<Real>(total[k]);
    }
    return numerator / ((q - 1) * z);
  }

  Real root() const {
    const Real target = 1 / static_cast<Real>(radius + 1);
    Real lo = 0, hi = 1;
    for (int i = 0; i < 160; ++i) {
      const Real mid = (lo + hi) / 2;
      if (mid == lo || mid == hi) break;
      if (connection(mid) < target) lo = mid;
      else hi = mid;
    }
    return (lo + hi) / 2;
  }
};

void require(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error("self-test failed: " + message);
}

void self_test() {
  // Regression against the attached Lean-certified q=3 rounded values.
  const long long q3[] = {42473310, 32233576, 26065061, 21906526, 18902489,
                         16627150, 14842644, 13405008, 12221782};
  for (int d = 3; d <= 11; ++d)
    require(std::llround(square_loop(d) * 100000000) == q3[d - 3],
            "q=3 certified decimal d=" + std::to_string(d));
  require(std::abs(gp4(1, 3) - Real(782) / 3125) < 2e-17L, "q=1,d=3 rational");
  // sigma=5: A=1+1/25+3/125+15/625=136/125.
  require(std::abs(gp4(2, 3) - Real(272) / 761) < 2e-17L, "q=2,d=3 rational");
  require(std::abs(square_loop(2) - estimate(3, 2)) < 2e-17L, "q3 exact d2 anchor");
  for (int q = 1; q <= 3; ++q) {
    Real previous = 1;
    for (int d = 2; d <= 100; ++d) {
      const Real p = estimate(q, d);
      require(p > 0 && p < 1 && p < previous, "range and dimension trend");
      require(std::abs(odds_to_p(p_to_odds(p)) - p) < 2e-17L, "odds round trip");
      previous = p;
    }
  }
  require(std::abs(ising_K_to_p(0.2L) - potts_K_to_p(0.4L)) < 2e-17L,
          "Ising/Potts coupling factor");
  for (int q : {1, 2})
    for (int d = 3; d <= 11; ++d)
      require(std::abs(pcd_series::hj_fk(q, d, 4) - gp4(q, d)) < 2e-17L,
              "literature series order-four agreement");
  require(std::abs(pcd_series::hj_fk(1, 8) - 0.0677080826968788633L) < 2e-17L,
          "HJ q1 d8 reference");
  require(std::abs(pcd_series::hj_fk(2, 8) - 0.125681966378058737L) < 2e-17L,
          "HJ q2 d8 reference");
  require(std::abs(pcd_series::bp12_fk(8) - 0.125682277416671048L) < 2e-17L,
          "BP q2 d8 reference");
  for (int q : {2, 3}) {
    for (int d : {2, 3}) {
      WiredBox box(d, 1, q);
      require(box.connection(0) == 0 && box.connection(1) == 1, "finite endpoints");
      const Real r = box.root();
      // One free central spin and 2d incident boundary edges:
      // W=(1-y^(2d))/(1+(q-1)y^(2d)), W=1/2 gives y^(2d)=1/(q+1).
      const Real exact_r = -std::expm1(-std::log(static_cast<Real>(q + 1)) / (2 * d));
      require(std::abs(r - exact_r) < 2e-16L, "finite R1 analytic root");
      require(std::abs(box.connection(r) - 0.5L) < 2e-16L, "finite root residual");
    }
  }
  WiredBox larger(2, 2, 2);
  std::uint64_t sum = 0, center_sum = 0;
  for (auto c : larger.total) sum += c;
  for (auto c : larger.center_zero) center_sum += c;
  require(sum == 512 && center_sum == 256, "finite histogram counts");
  Real previous = -1;
  for (int j = 0; j <= 100; ++j) {
    const Real w = larger.connection(static_cast<Real>(j) / 100);
    require(w >= previous - 2e-16L && w >= -2e-16L && w <= 1 + 2e-16L,
            "finite probability range and monotonic sample");
    previous = w;
  }
  require(std::abs(larger.connection(larger.root()) - Real(1) / 3) < 2e-16L,
          "finite R2 root residual");
  // Independent bond-subset enumeration of the wired one-dimensional R=2
  // box. Wiring its two endpoints gives a four-edge cycle. This checks the
  // spin-to-FK conversion against a calculation with different raw states.
  for (int q : {2, 3}) {
    const Real p = 0.37L;
    Real z = 0, c = 0;
    for (int mask = 0; mask < 16; ++mask) {
      int parent[] = {0, 1, 2, 3};
      auto find = [&](int x) {
        while (parent[x] != x) x = parent[x];
        return x;
      };
      int open = 0;
      for (int e = 0; e < 4; ++e) {
        if ((mask & (1 << e)) != 0) {
          ++open;
          const int a = find(e), b = find((e + 1) % 4);
          parent[a] = b;
        }
      }
      int components = 0;
      for (int v = 0; v < 4; ++v) components += (find(v) == v);
      const Real weight = std::pow(static_cast<Real>(q), components - 1)
          * std::pow(p, open) * std::pow(1 - p, 4 - open);
      z += weight;
      if (find(0) == find(2)) c += weight;
    }
    WiredBox path(1, 2, q);
    require(std::abs(path.connection(p) - c / z) < 2e-16L,
            "independent FK bond enumeration");
  }
  if (pcd_pade::supported) require(pcd_pade::self_test(), "Dlog-Pade tests");
  std::cout << "SELF_TEST=PASS\nQ3_CERTIFIED_ROUNDING_REGRESSIONS=9\n"
            << "DLOG_PADE_SELF_TEST=" << (pcd_pade::supported ? "PASS" : "UNSUPPORTED") << '\n'
            <<
               "PHYSICAL_DECIMALS_CERTIFIED_BY_CPP=0\n";
}

int parse_integer(const char* arg) {
  std::size_t used = 0;
  int value = std::stoi(arg, &used);
  if (arg[used] != '\0') throw std::invalid_argument("expected integer argument");
  return value;
}
} // namespace pcd

int main(int argc, char** argv) {
  try {
    std::cout << std::setprecision(17);
    if (argc == 2 && std::string(argv[1]) == "--self-test") {
      pcd::self_test();
      return 0;
    }
    if (argc == 2 && std::string(argv[1]) == "--help") {
      std::cout << "Usage: pcd [--q 1|2|3] [--d INTEGER]\n"
                   "       pcd --method original|hj9|bp12|dlog-pade [--q Q] [--d D]\n"
                   "       pcd --finite DIMENSION RADIUS COLORS\n"
                   "       pcd --pade-details [--d 3..11]\n"
                   "       pcd --self-test\n"
                   "Default: CSV model table for q=1,2,3 and d=2..11.\n"
                   "--finite: wired Potts spin enumeration (q=2 or 3), root W_R=1/(R+1).\n"
                   "Finite roots and model values are not certified physical thresholds.\n";
      return 0;
    }
    if (argc >= 2 && std::string(argv[1]) == "--pade-details") {
      int d = 3;
      if (argc == 4 && std::string(argv[2]) == "--d") d = pcd::parse_integer(argv[3]);
      else if (argc != 2) throw std::invalid_argument("use --pade-details [--d 3..11]");
      if (d < 3 || d > 11) throw std::invalid_argument("Pade details require 3<=d<=11");
      pcd_pade::write_csv(std::cout, d);
      return 0;
    }
    if (argc == 5 && std::string(argv[1]) == "--finite") {
      const int d = pcd::parse_integer(argv[2]);
      const int R = pcd::parse_integer(argv[3]);
      const int q = pcd::parse_integer(argv[4]);
      pcd::WiredBox box(d, R, q);
      const pcd::Real root = box.root();
      std::cout << "q,d,R,interior_vertices,spin_assignments,finite_root,target,residual,method\n"
                << q << ',' << d << ',' << R << ',' << box.interior << ','
                << box.configurations << ',' << root << ','
                << pcd::Real(1) / (R + 1) << ','
                << box.connection(root) - pcd::Real(1) / (R + 1)
                << ",wired-spin-enumeration\n";
      return 0;
    }
    int chosen_q = 0, chosen_d = 0;
    std::string chosen_method = "original";
    for (int i = 1; i < argc; ++i) {
      const std::string arg = argv[i];
      if (i + 1 >= argc || (arg != "--q" && arg != "--d" && arg != "--method"))
        throw std::invalid_argument("invalid arguments; use --help");
      if (arg == "--method") {
        chosen_method = argv[++i];
        if (chosen_method != "original" && chosen_method != "hj9" && chosen_method != "bp12"
            && chosen_method != "dlog-pade")
          throw std::invalid_argument("unknown method; use original, hj9, bp12 or dlog-pade");
        continue;
      }
      const int value = pcd::parse_integer(argv[++i]);
      if (arg == "--q") {
        if (value < 1 || value > 3) throw std::invalid_argument("q must be 1, 2 or 3");
        chosen_q = value;
      } else {
        if (value < 2) throw std::invalid_argument("d must be at least 2");
        chosen_d = value;
      }
    }
    const bool original = chosen_method == "original";
    const bool pade = chosen_method == "dlog-pade";
    const int q_min = chosen_q ? chosen_q : ((chosen_method == "bp12" || pade) ? 2 : 1);
    const int q_max = chosen_q ? chosen_q : (original ? 3 : 2);
    const int d_min = chosen_d ? chosen_d : (original ? 2 : 3);
    const int d_max = chosen_d ? chosen_d : 11;
    if (!original && d_min < 3)
      throw std::invalid_argument("literature-series methods require d>=3");
    if (chosen_method == "hj9" && q_max > 2)
      throw std::invalid_argument("hj9 requires q=1 or q=2");
    if (chosen_method == "bp12" && q_min != 2)
      throw std::invalid_argument("bp12 requires q=2");
    if (pade && (q_min != 2 || d_min < 3 || d_max > 11))
      throw std::invalid_argument("dlog-pade requires q=2,3<=d<=11");
    std::cout << "q,d,p_model,method\n";
    for (int q = q_min; q <= q_max; ++q)
      for (int d = d_min;; ++d) {
        const pcd::Real value = original ? pcd::estimate(q, d) :
            (chosen_method == "hj9" ? pcd_series::hj_fk(q, d) :
             (pade ? pcd_pade::estimate(d).median_p : pcd_series::bp12_fk(d)));
        const char* label = original ? pcd::method(q, d) :
            (chosen_method == "hj9" ? "HJ-sigma9-continuous-series" :
             (pade ? (d == 3 ? "HT32-Dlog-Pade-median" : "HT20-Dlog-Pade-median")
                   : "BP-z12-Ising-series"));
        std::cout << q << ',' << d << ',' << value << ',' << label << '\n';
        if (d == d_max) break;
      }
    return 0;
  } catch (const std::exception& e) {
    std::cerr << "ERROR: " << e.what() << '\n';
    return 1;
  }
}
