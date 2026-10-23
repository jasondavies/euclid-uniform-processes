module

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
-- The register programs, and the same programs as tail-recursive programs on the book's
-- recursive machine.
#print axioms ShortGCD.TailProgram.Run.dvd
#print axioms ShortGCD.TailProgram.Run.scale
#print axioms ShortGCD.TailProgram.Accepts.correct
#print axioms ShortGCD.TailProgram.exists_accepts
#print axioms ShortGCD.TailProgram.maxCost_step
#print axioms ShortGCD.TailProgram.Fixed.limsup_profile_le
#print axioms ShortGCD.TailProgram.Fixed.eventually_accepts_bound
#print axioms ShortGCD.TailProgram.Fixed.arbitrarily_small_coefficient
#print axioms ShortGCD.TailSource.total_registers
#print axioms ShortGCD.TailSource.run_trace_relabel
#print axioms ShortGCD.TailSource.executes_iff
#print axioms ShortGCD.TailSource.executes_correct
#print axioms ShortGCD.TailSource.executes_total
#print axioms ShortGCD.TailSource.arbitrarily_small_coefficient
#print axioms ShortGCD.TailRecursive.bodies_finite
#print axioms ShortGCD.TailRecursive.program_tailRecursive
#print axioms ShortGCD.TailRecursive.executes_iff_eval
#print axioms ShortGCD.TailRecursive.executes_iff_steps
#print axioms ShortGCD.TailRecursive.steps_correct
#print axioms ShortGCD.TailRecursive.steps_total
#print axioms ShortGCD.TailRecursive.arbitrarily_small_coefficient
#print axioms ShortGCD.Recursive.Machine.eval_iff_steps
#print axioms ShortGCD.Recursive.Machine.stacks_bounded
#print axioms ShortGCD.TailRecursive.stacks_bounded
-- The closure-depth question of van den Dries and Moschovakis.
#print axioms ShortGCD.ClosureDepth.rem_natCast
#print axioms ShortGCD.ClosureDepth.depth_le
#print axioms ShortGCD.ClosureDepth.depth_bound
#print axioms ShortGCD.ClosureDepth.no_logarithmic_sequences
-- The almost-all lower bound.
#print axioms ShortGCD.AlmostAll.within_iff_D_le
#print axioms ShortGCD.AlmostAll.le_of_within_regular
#print axioms ShortGCD.AlmostAll.card_irr_le
#print axioms ShortGCD.AlmostAll.card_within_le
#print axioms ShortGCD.AlmostAll.card_D_le
#print axioms ShortGCD.AlmostAll.tendsto_card_within_loglog
-- Lower bounds for the intrinsic complexities.
#print axioms ShortGCD.exists_certifiesCoprimeness
#print axioms ShortGCD.exists_certifiesGcd
#print axioms ShortGCD.G_le_callsRemGcd
#print axioms ShortGCD.G_le_callsGcd
#print axioms ShortGCD.callsCoprimeness_eq_G
#print axioms ShortGCD.tendsto_card_callsCoprimeness_loglog
