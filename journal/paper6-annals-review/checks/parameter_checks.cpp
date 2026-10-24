// Exact rational comparisons for revised constants; no analytic theorem is inferred.
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
struct Q {
    int64_t n,d;
    Q(int64_t a,int64_t b=1):n(a),d(b){auto g=std::gcd(n,d);n/=g;d/=g;}
    Q operator+(Q b)const{return Q(n*b.d+b.n*d,d*b.d);}
    Q operator-(Q b)const{return Q(n*b.d-b.n*d,d*b.d);}
    Q operator*(Q b)const{return Q(n*b.n,d*b.d);}
    bool operator==(Q b)const{return n==b.n&&d==b.d;}
    bool operator<(Q b)const{return n*b.d<b.n*d;}
};
int main(){
    Q s=Q(11,12)+Q(6)*Q(1,2000);
    assert(s==Q(2759,3000));
    assert(Q(49,50)-(Q(1)+s-Q(47,50))==Q(1,3000));
    assert(Q(1800,50)-Q(34)==Q(2));
    assert(Q(25)*(Q(1)-s)-Q(2)==Q(1,120));
    assert(Q(700,50)<Q(34)&&Q(17)*(Q(1)-s)<Q(2));
    assert(150+441<=600&&600*617==370200);
    std::cout<<"PASS: C++ exact rational review constants; no nonvanishing theorem asserted.\n";
}
