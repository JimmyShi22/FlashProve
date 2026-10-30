-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotDigitsFast.lean: the honest side of the kind "lookup" (K3): at a
site of a lookup on digits the seated row of the lot's honest side is the same row with `fastAsk`
for its reader. Conditional. Theorems alone.

Terms. Honest/K3/GLOSSARY.md ("lot", "site", "seated filling", "summand").

Why. The lot's honest side (`theLot`, Honest/K3/LotFilled.lean) lays at a site s the parts of
`proverSideOfLookupInChainAtOneOwner theReads (A.jobs s).asked (A.wit s) s.at_` (`rowLot`, Honest/K3/LotRow.lean), A :=
`fastFill (sourcesAt cells weights req Z)`; `A.wit s` is `askOf` over `tiedOwnSources` at `whoOf s`.
`fastAsk` (Honest/K3/WitDigitsFast.lean) is the structure of the lookup on the digits with the
counts of a call made in one pass. So a program that plays the row with `fastAsk` for its reader
plays the lot's own row.

What is shown.
  `whoOf_digits`: a site that names a round which samples the matrix is a lookup on digits.
  `wit_digits_fast`, `wit_digits_spec`: **the letter wit of `fastFill`, and of `specFill`, at such a
    site is `fastAsk`.**
  `seat_digits_fast`, `seat_digits_spec`: **the seated row at such a site is the row with `fastAsk`
    for its reader.**

Hypotheses that remain.
  `hr`: s.rng = some r: a site that `siteAt` makes names such a round at the digits and nowhere else
    (`siteAt_rng`, Honest/K3/LotLaw.lean). There is no other.

Users. Honest/K3/LotInstFast.lean imports this file.

Limits. The stages' summands (jobs) are the filling's own: nothing is exchanged there.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotFilled
import Johnson.Desc.ProofFile.Honest.K3.WitDigitsFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {W₀ Rc Xi Tr : Type}

theorem whoOf_digits (s : Site) (r : ℕ) (hr : s.rng = some r) : whoOf s = .digits s.link r := by
  unfold whoOf
  rw [hr]

/-- **The letter wit of fastFill at a site of a lookup on digits is fastAsk.** -/
theorem wit_digits_fast (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) (r : ℕ)
    (hr : s.rng = some r) :
    (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s =
      fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard := by
  funext t heard
  show askOf (tiedOwnSources Z.p.X cells weights req) (whoOf s) t heard = _
  rw [whoOf_digits s r hr]
  exact fastAsk_tied Z.p.X cells weights req s.link r t heard

/-- The same of specFill. -/
theorem wit_digits_spec (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) (r : ℕ)
    (hr : s.rng = some r) :
    (specFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s =
      fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard :=
  wit_digits_fast cells weights req Z s r hr

/-- **The seated row of the lot's honest side at a site of a lookup on digits is the row with
fastAsk for its reader.** -/
theorem seat_digits_fast {V X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) (r : ℕ)
    (hr : s.rng = some r) :
    (proverSideOfLookupInChainAtOneOwner theReads ((fastFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs s).asked
        ((fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s) s.at_ :
        Placed V (Local W₀ Rc Xi Tr) X) =
      proverSideOfLookupInChainAtOneOwner theReads ((fastFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs s).asked
        (fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard) s.at_ := by
  rw [wit_digits_fast cells weights req Z s r hr]

/-- The same at the specification's summands. -/
theorem seat_digits_spec {V X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) (r : ℕ)
    (hr : s.rng = some r) :
    (proverSideOfLookupInChainAtOneOwner theReads ((specFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs s).asked
        ((specFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s) s.at_ :
        Placed V (Local W₀ Rc Xi Tr) X) =
      proverSideOfLookupInChainAtOneOwner theReads ((specFill (Rc := Rc) (sourcesAt cells weights req Z)).jobs s).asked
        (fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard) s.at_ := by
  rw [wit_digits_spec cells weights req Z s r hr]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.whoOf_digits
#print axioms ProofFile.Honest.K3.wit_digits_fast
#print axioms ProofFile.Honest.K3.wit_digits_spec
#print axioms ProofFile.Honest.K3.seat_digits_fast
#print axioms ProofFile.Honest.K3.seat_digits_spec
