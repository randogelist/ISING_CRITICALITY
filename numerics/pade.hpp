#ifndef ISING_CRITICALITY_PADE_HPP
#define ISING_CRITICALITY_PADE_HPP

#include <algorithm>
#include <cmath>
#include <iomanip>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>
#include "susceptibility_data.hpp"

namespace pcd_pade {
struct Estimate {
    int d = 3, L = 0, M = 0, series_order = 0;
    long double v = 0, p = 0, gamma = 0, equation_residual = 0;
    bool accepted = false;
    std::string reason;
};
struct EnsembleResult {
    long double median_p = 0, min_p = 0, max_p = 0;
    std::size_t count = 0;
    std::vector<Estimate> rows;
};
#if defined(__SIZEOF_FLOAT128__)
inline constexpr bool supported = true;
using Real = __float128;
inline Real decimal(const char* s) {
    Real result=0;
    for (; *s; ++s) {
        if (*s<'0'||*s>'9') throw std::invalid_argument("decimal integer required");
        result=result*10+(*s-'0');
    }
    return result;
}
inline Real absolute(Real x) { return x<0 ? -x : x; }
inline Real maxreal(Real a, Real b) { return a>b?a:b; }
inline std::vector<Real> coefficients(int d=3) {
    if(d<3||d>11) throw std::invalid_argument("Dlog-Pade requires d=3..11");
    static const char* raw[]={"1","6","30","150","726","3510","16710","79494","375174","1769686","8306862","38975286","182265822","852063558","3973784886","18527532310","86228667894","401225368086","1864308847838","8660961643254","40190947325670","186475398518726","864404776466406","4006394107568934","18554916271112254","85923704942057238","397637244058624494","1839992653230056950","8509528288325589438","39350934581190850230","181885145332015353030","840628109226856546326","3883554493872938687622"};
    std::vector<Real> result;
    Real scale=1;
    const int count=d==3 ? 33:21;
    for(int i=0;i<count;++i) {
        const char* value=d==3 ? raw[i]:ht20_data[d-2][i];
        result.push_back(decimal(value)/scale);
        scale*=2*d-1;
    }
    return result;
}
inline std::vector<Real> logarithmic_derivative(const std::vector<Real>& c) {
    if (c.size()<2 || c.front()==0) throw std::invalid_argument("invalid susceptibility series");
    std::vector<Real> f(c.size()-1);
    for(std::size_t n=0;n<f.size();++n) {
        Real s=Real(n+1)*c[n+1];
        for(std::size_t k=1;k<=n;++k) s-=c[k]*f[n-k];
        f[n]=s/c.front();
    }
    return f;
}
inline Real poly(const std::vector<Real>& p, Real x) {
    Real y=0;
    for(auto it=p.rbegin();it!=p.rend();++it) y=y*x+*it;
    return y;
}
inline std::vector<Real> derivative(const std::vector<Real>& p) {
    std::vector<Real> d;
    for(std::size_t i=1;i<p.size();++i) d.push_back(Real(i)*p[i]);
    return d;
}
// Recursive derivative isolation. Finds all simple real roots on (lo,hi),
// plus detected stationary roots; it is a numerical diagnostic, not a certificate.
inline std::vector<Real> real_roots(std::vector<Real> p, Real lo, Real hi) {
    while(!p.empty()&&p.back()==0) p.pop_back();
    if(p.size()<2) return {};
    if(p.size()==2) {
        Real r=-p[0]/p[1];
        return lo<r&&r<hi ? std::vector<Real>{r}:std::vector<Real>{};
    }
    Real norm=0;
    for(Real v:p) norm=maxreal(norm,absolute(v));
    if(norm==0) return {};
    for(Real& v:p) v/=norm;
    auto turning=real_roots(derivative(p),lo,hi);
    std::vector<Real> bounds{lo};
    bounds.insert(bounds.end(),turning.begin(),turning.end()); bounds.push_back(hi);
    std::vector<Real> roots;
    const Real zero=Real(1)/decimal("1000000000000000000000000000");
    for(Real t:turning) if(absolute(poly(p,t))<zero) roots.push_back(t);
    for(std::size_t i=1;i<bounds.size();++i) {
        Real a=bounds[i-1],b=bounds[i],fa=poly(p,a),fb=poly(p,b);
        if((fa<0&&fb>0)||(fa>0&&fb<0)) {
            for(int k=0;k<125;++k) {
                Real m=(a+b)/2;
                if(m==a||m==b) break;
                Real fm=poly(p,m);
                if(fm==0) { a=m; b=m; break; }
                if((fa<0&&fm>0)||(fa>0&&fm<0)) b=m;
                else {a=m;fa=fm;}
            }
            roots.push_back((a+b)/2);
        }
    }
    std::sort(roots.begin(),roots.end());
    roots.erase(std::unique(roots.begin(),roots.end(),[&](Real a,Real b){return absolute(a-b)<zero*100;}),roots.end());
    return roots;
}
struct RationalFit { std::vector<Real> numerator, denominator; Real residual=0; };
inline RationalFit fit(const std::vector<Real>& f,int L,int M) {
    if(L<0||M<1||std::size_t(L+M)>=f.size()) throw std::invalid_argument("invalid Pade degree");
    std::vector<std::vector<Real>> a(M,std::vector<Real>(M+1));
    for(int i=0;i<M;++i) {
        const int k=L+1+i;
        for(int j=0;j<M;++j) a[i][j]=k-j-1>=0 ? f[k-j-1]:0;
        a[i][M]=-f[k];
    }
    const auto original=a;
    const Real singular=Real(1)/decimal("1000000000000000000000000000000");
    for(int i=0;i<M;++i) {
        int pivot=i;
        for(int j=i+1;j<M;++j) if(absolute(a[j][i])>absolute(a[pivot][i])) pivot=j;
        if(absolute(a[pivot][i])<singular) throw std::runtime_error("near-singular Pade system");
        std::swap(a[i],a[pivot]);
        for(int j=i+1;j<M;++j) {
            const Real factor=a[j][i]/a[i][i];
            for(int k=i;k<=M;++k) a[j][k]-=factor*a[i][k];
        }
    }
    RationalFit result;
    auto& q=result.denominator;q.assign(M+1,0);q[0]=1;
    for(int i=M-1;i>=0;--i) {
        Real rhs=a[i][M];
        for(int j=i+1;j<M;++j) rhs-=a[i][j]*q[j+1];
        q[i+1]=rhs/a[i][i];
    }
    for(int i=0;i<M;++i) {
        Real lhs=0,norm=1+absolute(original[i][M]);
        for(int j=0;j<M;++j) {lhs+=original[i][j]*q[j+1]; norm+=absolute(original[i][j]*q[j+1]);}
        result.residual=maxreal(result.residual,absolute(lhs-original[i][M])/norm);
    }
    if(result.residual>Real(1)/decimal("10000000000000000000000")) throw std::runtime_error("Pade equation residual too large");
    result.numerator.assign(L+1,0);
    for(int i=0;i<=L;++i) for(int j=0;j<=M&&j<=i;++j) result.numerator[i]+=q[j]*f[i-j];
    return result;
}
inline Estimate analyze(const std::vector<Real>& f,int L,int M,int d=3) {
    const Real scale=2*d-1;
    Estimate row;row.d=d;row.L=L;row.M=M;row.series_order=L+M+1;
    try {
        const auto r=fit(f,L,M);
        row.equation_residual=static_cast<long double>(r.residual);
        const auto poles=real_roots(r.denominator,0,scale);
        const auto zeros=real_roots(r.numerator,0,scale);
        const auto dq=derivative(r.denominator);
        for(Real pole:poles) {
            const Real slope=poly(dq,pole);
            if(slope==0) continue;
            const Real gamma=-poly(r.numerator,pole)/slope;
            if(gamma<=0) continue;
            bool cancellation=false;
            for(Real zero:zeros) if(absolute(pole-zero)<Real(1)/10000*maxreal(1,absolute(pole))) cancellation=true;
            if(cancellation) continue;
            const Real v=pole/scale;
            row.v=static_cast<long double>(v);
            row.p=static_cast<long double>(2*v/(1+v));
            row.gamma=static_cast<long double>(gamma);
            row.accepted=true;row.reason="accepted";
            return row;
        }
        row.reason="no positive-residue uncancelled pole in 0<v<1";
    } catch(const std::runtime_error& e) { row.reason=e.what(); }
    return row;
}
inline EnsembleResult estimate(int d=3) {
    const auto f=logarithmic_derivative(coefficients(d));
    EnsembleResult result;
    std::vector<long double> values;
    for(int n=(d==3 ? 24:14);n<=(d==3 ? 31:19);++n) for(int M=1;M<=n;++M) {
        const int L=n-M;
        if(std::abs(L-M)>2) continue;
        auto row=analyze(f,L,M,d);
        if(row.accepted) values.push_back(row.p);
        result.rows.push_back(row);
    }
    if(values.empty()) throw std::runtime_error("no accepted Dlog-Pade approximants");
    std::sort(values.begin(),values.end());
    result.count=values.size();result.min_p=values.front();result.max_p=values.back();
    result.median_p=values[values.size()/2];
    if(values.size()%2==0) result.median_p=(result.median_p+values[values.size()/2-1])/2;
    return result;
}
inline bool self_test() {
    // chi(x)=(1-2x)^-2 => logarithmic derivative 4/(1-2x).
    std::vector<Real> c;
    Real power=1;
    for(int n=0;n<=8;++n) {c.push_back(Real(n+1)*power);power*=2;}
    auto f=logarithmic_derivative(c);
    const auto r=fit(f,0,1);
    auto roots=real_roots(r.denominator,0,1);
    if(roots.size()!=1||absolute(roots[0]-Real(1)/2)>Real(1)/decimal("1000000000000000000000000")) return false;
    if(absolute(-poly(r.numerator,roots[0])/poly(derivative(r.denominator),roots[0])-2)>Real(1)/decimal("1000000000000000000000000")) return false;
    auto mixed=real_roots({Real(-6),Real(11),Real(-6),Real(1)},0,4);
    if(mixed.size()!=3) return false;
    for(int i=0;i<3;++i) if(absolute(mixed[i]-(i+1))>Real(1)/decimal("1000000000000000000000")) return false;
    const auto e=estimate();
    return e.count>0&&0<e.min_p&&e.max_p<1;
}
#else
inline constexpr bool supported = false;
inline EnsembleResult estimate(int =3) {throw std::runtime_error("Dlog-Pade requires a compiler supporting __float128 (GCC/MinGW)");}
inline bool self_test() {return true;}
#endif
inline void write_csv(std::ostream& out,int d=3) {
    const auto result=estimate(d);
    out<<"d,susceptibility_order,L,M,accepted,v,p,gamma,equation_residual,reason\n"<<std::setprecision(18);
    for(const auto& row:result.rows) {
        out<<row.d<<','<<row.series_order<<','<<row.L<<','<<row.M<<','<<(row.accepted?"true":"false")<<',';
        if(row.accepted) out<<row.v<<','<<row.p<<','<<row.gamma;
        else out<<",,";
        out<<','<<row.equation_residual<<','<<row.reason<<'\n';
    }
}
} // namespace pcd_pade
#endif
