import ShortGCD

-- The refutations.
#print axioms ShortGCD.not_conjecture_3_4
#print axioms ShortGCD.not_main_conjecture_4F5
#print axioms ShortGCD.not_main_conjecture_4F5_Neps
#print axioms ShortGCD.not_conjecture_3_4_literal
#print axioms ShortGCD.not_main_conjecture_4F5_literal
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
-- The refined leading coefficient and its certificate consequences.
#print axioms ShortGCD.Sharp.limsup_profile_le_six
#print axioms ShortGCD.eventually_sizeCost_add_le_six
#print axioms ShortGCD.uniform_real_bound_six
#print axioms ShortGCD.uniform_intrinsic_bound_six
-- Fixed finite nondeterministic programs and their first-order syntax.
#print axioms ShortGCD.RegisterProgram.maxCost_step
#print axioms ShortGCD.RegisterProgram.Fixed.limsup_profile_le
#print axioms ShortGCD.RegisterProgram.Fixed.eventually_accepts_bound
#print axioms ShortGCD.RegisterProgram.Fixed.arbitrarily_small_coefficient
#print axioms ShortGCD.RegisterProgram.Syntax.run_invokes
#print axioms ShortGCD.RegisterProgram.Syntax.accepts_eval
#print axioms ShortGCD.RegisterProgram.Syntax.eval_head_correct
#print axioms ShortGCD.RegisterProgram.Syntax.eval_head_exists
#print axioms ShortGCD.RegisterProgram.Syntax.eventually_eval_bound
#print axioms ShortGCD.RegisterProgram.Syntax.arbitrarily_small_program
-- Exact-cost small-step machine correspondence and operational bounds.
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.Step.context
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.eval_iff_steps
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.head_correct
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.head_exists
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.eventually_steps_bound
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.arbitrarily_small_program
