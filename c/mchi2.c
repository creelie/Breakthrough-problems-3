/* Per prime q: max of M/sqrt q over odd and over even nonprincipal characters, and a histogram of
   M/sqrt q (bins of width 0.05 on [0,2.5)) accumulated over all characters with q in [lo,hi]. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
static int isprime(int n){ if(n<2) return 0; for(int d=2;d*d<=n;d++) if(n%d==0) return 0; return 1; }
static int primroot(int q){ int phi=q-1, f[32], nf=0, m=phi; for(int p=2;p*p<=m;p++) if(m%p==0){f[nf++]=p; while(m%p==0) m/=p;} if(m>1) f[nf++]=m;
  for(int g=2;g<q;g++){ int ok=1; for(int i=0;i<nf&&ok;i++){ long long r=1,b=g; int e=phi/f[i]; while(e){ if(e&1) r=r*b%q; b=b*b%q; e>>=1;} if(r==1) ok=0;} if(ok) return g;} return -1; }
int main(int argc,char**argv){ int lo=atoi(argv[1]), hi=atoi(argv[2]); long hist[50]={0};
  for(int q=lo;q<=hi;q++){ if(!isprime(q)||q<5) continue; int g=primroot(q); int *ind=malloc(q*sizeof(int)); long long r=1; for(int k=0;k<q-1;k++){ ind[r]=k; r=r*g%q; }
    double complex *w=malloc((q-1)*sizeof(double complex)); for(int k=0;k<q-1;k++) w[k]=cexp(2*M_PI*I*k/(q-1));
    double sq=sqrt(q), bo=0, be=0;
    for(int j=1;j<q-1;j++){ double complex s=0; double m=0; for(int n=1;n<q;n++){ s+=w[(long long)j*ind[n]%(q-1)]; double a=cabs(s); if(a>m) m=a; }
      double rr=m/sq; if(j%2){ if(rr>bo) bo=rr; } else { if(rr>be) be=rr; } int b=(int)(rr/0.05); if(b>49) b=49; hist[b]++; }
    printf("Q %d %.6f %.6f\n", q, bo, be); fflush(stdout); free(ind); free(w); }
  printf("H"); for(int b=0;b<50;b++) printf(" %ld",hist[b]); printf("\n"); return 0; }
