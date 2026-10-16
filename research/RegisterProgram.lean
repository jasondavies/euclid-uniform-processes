import ShortGCD.RegisterSmallStep

/-! Research entry point and axiom audit. The development now belongs to the
normal library build; this file preserves the original verification command. -/

#print axioms ShortGCD.RegisterProgram.Accepts.correct
#print axioms ShortGCD.RegisterProgram.Run.scale
#print axioms ShortGCD.RegisterProgram.exists_accepts
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
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.Step.context
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.eval_iff_steps
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.head_correct
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.head_exists
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.eventually_steps_bound
#print axioms ShortGCD.RegisterProgram.Syntax.Machine.arbitrarily_small_program
