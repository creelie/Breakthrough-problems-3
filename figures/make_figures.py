import math, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Rectangle, FancyArrowPatch
plt.rcParams.update({'font.family':'serif','mathtext.fontset':'cm','font.size':11})
OUT='paper/figures/'
def box(ax,x,y,w,h,txt,fs=10,dashed=False):
    ax.add_patch(FancyBboxPatch((x-w/2,y-h/2),w,h,boxstyle='round,pad=0.02,rounding_size=0.06',fc='white',ec='black',lw=1.2,ls='--' if dashed else '-'))
    ax.text(x,y,txt,ha='center',va='center',fontsize=fs)
def arr(ax,x1,y1,x2,y2,dashed=False):
    ax.add_patch(FancyArrowPatch((x1,y1),(x2,y2),arrowstyle='-|>',mutation_scale=13,lw=1.1,color='black',ls='--' if dashed else '-'))
# flow
fig,ax=plt.subplots(figsize=(9,4.8)); ax.set_xlim(0,9); ax.set_ylim(0.3,4.6); ax.axis('off')
box(ax,1.6,4.0,2.5,0.7,'Explicit formula\n(Z1)–(Z3)')
box(ax,4.5,4.0,2.5,0.7,'Montgomery–Vaughan\nestimate (2.2)')
box(ax,7.4,4.0,2.5,0.7,'Zero density (2.1)')
box(ax,1.6,2.6,2.5,0.8,'Prime sums of $\\chi\\psi$\nLemmas 3.1–3.3')
box(ax,4.5,2.6,2.5,0.8,'Transfer\nTheorem 1.3')
box(ax,7.4,2.6,2.5,0.8,'Theorem 1.1\nCorollary 1.2')
box(ax,1.6,1.0,2.5,0.8,'$L\'/L$ near zeros\nProposition 6.1')
box(ax,7.4,1.0,2.5,0.8,'Theorem 1.5')
box(ax,4.5,1.0,2.5,0.8,'Half-plane $\\Re s>\\theta$\n(Corollary 1.4)',dashed=True)
arr(ax,1.6,3.65,1.6,3.0); arr(ax,2.85,2.6,3.25,2.6); arr(ax,4.5,3.65,4.5,3.0); arr(ax,5.75,2.6,6.15,2.6)
arr(ax,7.4,3.65,7.4,3.0)
ax.plot([0.25,0.25],[4.0,1.0],color='black',lw=1.1); ax.plot([0.25,0.35],[4.0,4.0],color='black',lw=1.1); arr(ax,0.25,1.0,0.35,1.0)
ax.plot([8.75,8.75],[4.0,1.0],color='black',lw=1.1); ax.plot([8.65,8.75],[4.0,4.0],color='black',lw=1.1); arr(ax,8.75,1.0,8.65,1.0)
arr(ax,2.85,1.0,6.15,1.0) if False else None
ax.annotate('',xy=(6.15,0.75),xytext=(2.85,0.75),arrowprops=dict(arrowstyle='-|>',lw=1.1,color='black',connectionstyle='arc3,rad=0.25'))
arr(ax,4.5,1.4,4.5,2.2,dashed=True)
fig.tight_layout(); fig.savefig(OUT+'fig_flow.png',dpi=220); plt.close(fig)
# arcs
fig,ax=plt.subplots(figsize=(9,2.6)); R=5
from math import gcd
fr=sorted({(a,r) for r in range(1,R+1) for a in range(0,r+1) if gcd(a,r)==1})
for a,r in fr:
    c=a/r; wd=0.035
    ax.add_patch(Rectangle((c-wd,0),2*wd,1.0/r,fc='0.75',ec='black',lw=0.8))
    ax.text(c,1.0/r+0.06,f'${a}/{r}$' if r>1 else f'${a}$',ha='center',fontsize=8)
ax.plot([0,1],[0,0],color='black',lw=1.2); ax.set_xlim(-0.05,1.05); ax.set_ylim(-0.12,1.25); ax.axis('off')
ax.text(0.5,-0.1,'minor arcs: bound (2.2) for $r>R$',ha='center',fontsize=10)
fig.tight_layout(); fig.savefig(OUT+'fig_arcs.png',dpi=220); plt.close(fig)
# contour (in 1+s)
fig,ax=plt.subplots(figsize=(6.4,4.4)); th=0.75; d=(1-th)/2; T=3.0
ax.add_patch(Rectangle((th,-T-1),1-th,2*T+2,fc='0.88',ec='none'))
ax.plot([th,th],[-T-1.2,T+1.2],ls=':',color='black'); ax.text(th-0.03,T+1.25,r'$\theta$',ha='right')
ax.plot([1,1],[-T-1.2,T+1.2],ls='-',color='0.5',lw=0.8); ax.text(1.0,T+1.25,'$1$',ha='center')
pts=[(2,-T-1.4),(2,-T),(1-d,-T),(1-d,T),(2,T),(2,T+1.4)]
for (x1,y1),(x2,y2) in zip(pts[:-1],pts[1:]): ax.annotate('',xy=(x2,y2),xytext=(x1,y1),arrowprops=dict(arrowstyle='-|>',lw=1.3,color='black'))
ax.plot([1],[0],'ko'); ax.text(1.03,0.1,'$s=0$',fontsize=10)
ax.text(1-d-0.02,0.5,r'$\Re(1+s)=\theta+\delta$',rotation=90,ha='right',va='center',fontsize=9)
ax.text(2.04,0,r'$\Re(1+s)=2$',rotation=90,va='center',fontsize=9)
ax.text(1.5,T+0.15,'$\\pm T$',ha='center',fontsize=9)
ax.text(0.79,-T-0.5,'zero-free',ha='center',fontsize=8,rotation=90)
ax.set_xlim(0.45,2.25); ax.set_ylim(-T-1.6,T+1.6); ax.set_xticks([]); ax.set_yticks([])
for sp in ax.spines.values(): sp.set_visible(False)
fig.tight_layout(); fig.savefig(OUT+'fig_contour.png',dpi=220); plt.close(fig)
# max ratios
Q=[l.split() for f in ['data/n1.txt','data/n2.txt','data/n3.txt'] for l in open(f) if l[0]=='Q']
qs=[int(x[1]) for x in Q]; ll=[math.log(math.log(q)) for q in qs]
ro=[float(x[2])/l for x,l in zip(Q,ll)]; re=[float(x[3])/l for x,l in zip(Q,ll)]
Co=math.exp(0.5772156649)/math.pi; Ce=Co/math.sqrt(3)
fig,ax=plt.subplots(figsize=(8,4.2))
ax.scatter(qs,ro,s=4,c='black',label='odd $\\chi$'); ax.scatter(qs,re,s=4,facecolors='none',edgecolors='0.45',label='even $\\chi$')
for c,lab,ls in [(Co,'$e^\\gamma/\\pi$','--'),(2*Co,'$2e^\\gamma/\\pi$',':'),(Ce,'$e^\\gamma/(\\sqrt{3}\\pi)$','--'),(2*Ce,'$2e^\\gamma/(\\sqrt{3}\\pi)$',':')]:
    ax.axhline(c,ls=ls,color='black',lw=0.8); ax.text(10150,c,lab,va='center',fontsize=9)
ax.set_xlim(0,10000); ax.set_ylim(0.2,1.4); ax.set_xlabel('prime modulus $q$'); ax.set_ylabel(r'$\max_\chi M(\chi)/(\sqrt{q}\,\log\log q)$')
ax.legend(loc='upper right',fontsize=9,frameon=False)
fig.tight_layout(); fig.savefig(OUT+'fig_max.png',dpi=220); plt.close(fig)
# histogram
H=[int(v) for l in open('data/n3.txt') if l[0]=='H' for v in l.split()[1:]]
fig,ax=plt.subplots(figsize=(8,3.6)); tot=sum(H)
ax.bar([0.05*i+0.025 for i in range(50)],[h/tot/0.05 for h in H],width=0.05,color='0.8',edgecolor='black',lw=0.6)
ax.set_xlim(0.3,2.0); ax.set_xlabel(r'$M(\chi)/\sqrt{q}$'); ax.set_ylabel('density')
fig.tight_layout(); fig.savefig(OUT+'fig_hist.png',dpi=220); plt.close(fig)
print('ok')
