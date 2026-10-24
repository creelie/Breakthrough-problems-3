/* Exact integer comparisons for revised constants; no analytic theorem is inferred. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
int main(void) {
    const int64_t d=6000, s=5518;
    assert(11*(d/12)+6*(d/2000)==s);
    assert(49*(d/50)-(d+s-47*(d/50))==d/3000);
    assert(1800-34*50==2*50);
    assert((25*(d-s)-2*d)*120==d);
    assert(700<34*50 && 17*(d-s)<2*d);
    assert(150+441<=600 && 600*617==370200);
    puts("PASS: C exact integer review constants; no nonvanishing theorem asserted.");
    return 0;
}
