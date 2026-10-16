import ShortGCD

-- The refutations.
#print axioms ShortGCD.not_conjecture_3_4
#print axioms ShortGCD.not_main_conjecture_4F5
#print axioms ShortGCD.not_main_conjecture_4F5_Neps
#print axioms ShortGCD.eventually_calls_le
-- The intrinsic complexities and their relation to the reduction.
#print axioms ShortGCD.certifiesCoprimeness_of_certifiesCoprime
#print axioms ShortGCD.callsCoprimeness_eq_callsRem
#print axioms ShortGCD.callsCoprimeness_le
#print axioms ShortGCD.callsGcd_le
#print axioms ShortGCD.callsRemGcd_le_callsGcd
#print axioms ShortGCD.callsGcd_zero_left
#print axioms ShortGCD.callsGcd_zero_right
#print axioms ShortGCD.callsRem_eq_D
#print axioms ShortGCD.G_eq_D
-- Certificates.
#print axioms ShortGCD.coprime_certificate_bound
#print axioms ShortGCD.noncoprime_certificate_bound
#print axioms ShortGCD.uniform_gcd_certificates
#print axioms ShortGCD.gcd_certificate_lower
-- The upper bound.
#print axioms ShortGCD.prefix_pairs_distinct
#print axioms ShortGCD.small_remainder
#print axioms ShortGCD.sizeCost_step
#print axioms ShortGCD.uniform_bit_bound
#print axioms ShortGCD.uniform_size_real_bound
#print axioms ShortGCD.uniform_real_bound
#print axioms ShortGCD.sizeCost_isBigO
#print axioms ShortGCD.sizeCost_isLittleO_log
