# Exact constants for the revised 11/12 presentation, not a zero-free proof.
theta=big(11)//12; delta=big(1)//2000; sigma=theta+6delta
@assert sigma==big(2759)//3000
@assert big(49)//50-(1+sigma-big(47)//50)==big(1)//3000
@assert big(1800)//50-34==2
@assert 25*(1-sigma)-2==big(1)//120
@assert big(700)//50<34 && 17*(1-sigma)<2
@assert 150+441<=600 && 600*617==370200
println("PASS: Julia exact rational review constants; no nonvanishing theorem asserted.")
