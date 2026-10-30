-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTraceOf.lean.
The flat trace of the sub-proofs' lookup, cut at its steps: if each step of the flat function gives
what
is named, the trace is the record of the names. Lists alone.

* `shiftRd h θ`: the shift's round as plain data, if there are several calls.
* `theta_of`, `after_of`: the flat readers of the shift and of the rounds behind it, at rounds that
begin
  with `shiftRd h θ`.
* `forTrace_of`: at rounds that begin with the shift's round and the round that draws alpha: if the
tie's
  loop, the two loops over levels and the two last sumchecks give the named values, each handing on
    what is
  behind it, then `Fo.forTrace` is the record of these values, and `Fo.forN` is `Fo.numsF` at the
    shift.

A frame: it says nothing until its premises are filled.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEnds
import Cb.Pv.Lookup.Out.TwTraceL

set_option autoImplicit false

namespace Fo
open TwV FoNums

section
variable {K : Type} [CommRing K]

/-- The shift's round, if there are several calls. -/
def shiftRd (h : Sh) (θ : K) : Rounds K := if several h then [([], [θ])] else []

/-- The shift as the flat function reads it: 0 if there is one call. -/
def shiftOf (h : Sh) (θ : K) : K := if several h then θ else 0

theorem theta_of (h : Sh) (θ : K) (rs : Rounds K) :
    thetaOf h (shiftRd h θ ++ rs) = shiftOf h θ := by
  unfold thetaOf shiftRd shiftOf
  cases several h <;> rfl

omit [CommRing K] in
theorem after_of (h : Sh) (θ : K) (rs : Rounds K) : afterShift h (shiftRd h θ ++ rs) = rs := by
  unfold afterShift shiftRd
  cases several h <;> rfl

theorem forN_of (h : Sh) (lm jLK : ℕ) (θ : K) (rs : Rounds K) :
    forN h lm jLK (shiftRd h θ ++ rs) = numsF h lm jLK (shiftOf h θ) := by
  unfold forN
  rw [theta_of]

/-- The trace, from its steps. -/
theorem forTrace_of (h : Sh) (lm jLK : ℕ) (θ lam : K) (r1 r2 r3 r4 r5 r6 : Rounds K)
    (tieL : List (Sc K)) (join : List K) (keysL : List (Sc K × K)) (kT : K) (kp : List K)
    (tabL : List (Sc K × K)) (tg : K) (pt : List K) (cls : Sc K) (zero : List K) (bits : Sc K)
    (h1 : tieGo ((numsF h lm jLK (shiftOf h θ)).n + 1) 0 0 r1 = (tieL, ([], join) :: r2))
    (h2 : lvGo (numsF h lm jLK (shiftOf h θ)).oK ((numsF h lm jLK (shiftOf h θ)).v' + 1) 0
      (tK (⟨lam, tieL, join, [], 0, [], Sc.zero, [], Sc.zero⟩ : Trace K)) [] r2 =
        (keysL, kT, kp, r3))
    (h3 : lvGo (numsF h lm jLK (shiftOf h θ)).oT (numsF h lm jLK (shiftOf h θ)).d 0
      (tgT0 (numsF h lm jLK (shiftOf h θ))
        (⟨lam, tieL, join, [], 0, [], Sc.zero, [], Sc.zero⟩ : Trace K)) join r3 =
        (tabL, tg, pt, r4))
    (h4 : takeSc r4 tg (inRounds (numsF h lm jLK (shiftOf h θ)).oE pt) false =
      (cls, ([], zero) :: r5))
    (h5 : takeSc r5 0 (inRounds (numsF h lm jLK (shiftOf h θ)).oB zero ++ [0]) true = (bits, r6)) :
    forTrace h lm jLK (shiftRd h θ ++ ([], [lam]) :: r1) =
      ⟨lam, tieL, join, keysL, kT, tabL, cls, zero, bits⟩ := by
  unfold forTrace
  rw [forN_of, after_of]
  exact Tw.traceOfFlat_of _ lam r1 r2 r3 r4 r5 r6 tieL join keysL kT kp tabL tg pt cls zero bits
    h1 h2 h3 h4 h5

end
end Fo
