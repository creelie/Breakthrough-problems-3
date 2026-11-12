/* For each prime q in [lo,hi]: M(chi) = max_x |sum_{n<=x} chi(n)| for every nonprincipal chi mod q.
   Output per q: q, max ratio M/sqrt(q) and its character index, mean of M/sqrt q, and the counts of
   characters with M/(sqrt(q) loglog q) above thresholds 0.5,0.75,1,1.25,1.5; also the parity of the max. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
static int isprime(int n){ if(n<2) return 0; for(int d=2;d*d<=n;d++) if(n%d==0) return 0; return 1; }
static int primroot(int q){ int phi=q-1, f[32], nf=0, m=phi; for(int p=2;p*p<=m;p++) if(m%p==0){f[nf++]=p; while(m%p==0) m/=p;} if(m>1) f[nf++]=m;
  for(int g=2;g<q;g++){ int ok=1; for(int i=0;i<nf&&ok;i++){ long long r=1,b=g; int e=phi/f[i]; while(e){ if(e&1) r=r*b%q; b=b*b%q; e>>=1;} if(r==1) ok=0;} if(ok) return g;} return -1; }
int main(int argc,char**argv){ int lo=atoi(argv[1]), hi=atoi(argv[2]);
  for(int q=lo;q<=hi;q++){ if(!isprime(q)||q<5) continue; int g=primroot(q); int *ind=malloc(q*sizeof(int)); long long r=1; for(int k=0;k<q-1;k++){ ind[r]=k; r=r*g%q; }
    double complex *w=malloc((q-1)*sizeof(double complex)); for(int k=0;k<q-1;k++) w[k]=cexp(2*M_PI*I*k/(q-1));
    double sq=sqrt(q), ll=log(log(q)), best=0, sum=0; int bj=0; long cnt[5]={0}; double th[5]={0.5,0.75,1,1.25,1.5};
    for(int j=1;j<q-1;j++){ double complex s=0; double m=0; for(int n=1;n<q;n++){ s+=w[(long long)j*ind[n]%(q-1)]; double a=cabs(s); if(a>m) m=a; }
      double rr=m/sq; sum+=rr; if(rr>best){best=rr;bj=j;} for(int t=0;t<5;t++) if(rr>th[t]*ll) cnt[t]++; }
    printf("%d %.6f %d %s %.6f %.6f %ld %ld %ld %ld %ld\n", q, best, bj, (bj%2)?"odd":"even", sum/(q-2), ll, cnt[0],cnt[1],cnt[2],cnt[3],cnt[4]); fflush(stdout);
    free(ind); free(w); }
  return 0; }
