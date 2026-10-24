# Independent proof status

No new independent proof of the zero-free theorem has been obtained. This note
is separate from the manuscript. Its purpose is to state the outstanding
mathematical obligation exactly, not to claim that finite tests discharge it.

One sufficient replacement is the following assertion. For each nonprincipal
Dirichlet character chi, every epsilon>0 and every smooth W supported in (1,2),
prove, for all X>=1,

    abs(sum_n mu(n) chi(n) W(n/X)) <= C(chi,W,epsilon) X^(11/12+epsilon).

The constant may depend on the fixed character and weight; the exponent must
have the same boundary 11/12 for every character. This implies the required
nonvanishing, as follows. If L(s,chi) had a zero rho with Re(rho)>11/12, choose
epsilon smaller than that gap and a nonnegative nonzero smooth phi supported
in (1,2). Put W(y)=y^(-rho) phi(y). Its Mellin transform at rho is the strictly
positive integral of phi(y)/y. The displayed bound makes the Mellin transform
in X of the smoothed sum holomorphic on Re(s)>11/12. For Re(s)>1, absolute
convergence identifies it with Mellin(W)(s)/L(s,chi). Analytic continuation
then gives L(s,chi) M(s)=Mellin(W)(s) throughout that half-plane. Evaluation at
rho contradicts the chosen positive value. For the holomorphy assertion at any
point, choose epsilon smaller than its distance from 11/12; constants need not
be uniform in epsilon. The integral near X=0 vanishes by compact support.

This reduction does not prove the displayed Möbius bound. The cited OpenAI
argument obtains the corresponding cancellation through a specialised mean
square, theta transformation and transfer iteration. Restating those steps
with attribution would be a reconstruction of that argument, not an
independent replacement.

The Burgess-shaped substitution considered earlier gives no nontrivial bound
at the required polylogarithmic lengths. A coefficient-uniform substitute for
the special Möbius mean square is also false because coherent sixth-power rows
can align the selected prime columns. Neither observation disproves OpenAI's
special-coefficient theorem; neither supplies the missing replacement.

The current manuscript therefore uses the author's authorised fallback: the
exact external theorem is cited and credited. A successful Lean rebuild would
verify the stated formal dependency and endpoints. Python, Julia, C and C++
checks test specified arithmetic and finite ranges; they do not prove the
displayed estimate for all X or construct a new proof of nonvanishing.
