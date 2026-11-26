import PALRH.DysonOctave

noncomputable section

def fixedOctaveKernel (z : ℂ) : ℂ :=
  let a:=Complex.exp ((Real.log 2:ℝ)*z)
  (a-1)^2/(a*z^2)

def fixedPrimeResponse : Prop :=
  ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {s : ℂ | 1/2<s.re} ∧
    ∀ s : ℂ, 1<s.re → H s = fixedOctaveKernel (s-1/2)*
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n:ℂ)) s-fixedOctaveKernel (1/2)/(s-1)

theorem primeResponseReduction (h : fixedPrimeResponse) : RiemannHypothesis := by
  obtain ⟨H,regular,values⟩:=h
  exact PALRH.DysonOctave.rh_of_centered_response H regular values

#print axioms primeResponseReduction
