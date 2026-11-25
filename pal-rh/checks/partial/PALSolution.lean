import PALRH

/- Controlled submission for the fixed-target rejection test. Its premise is explicit. -/
theorem riemannHypothesis (h : PALRH.FiniteCertificates) : RiemannHypothesis :=
  PALRH.rh_of_finite_certificates h
