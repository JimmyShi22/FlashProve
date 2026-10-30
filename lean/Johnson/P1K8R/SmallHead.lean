-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/SmallHead.lean: THE OUTPUT HEAD's OWN PART "small" OF THE COMPOSED MEANING HOLDS BY
THE MAKE, AT EVERY WITNESS: AT THE CLOSED CONSTANT, FROM THE HEAD `P5J.AtMgA` ALONE. A piece of the
payment of the field "small" of `K8LeftT` (Johnson/P1K8R/TightAt.lean): the premise hHead of
`small_at_head` (Johnson/Desc/First/K8/SmallAtNine.lean).
What the part says. `h.𝔇.headPart` := `headPartK6 …` (Johnson/P5J/LettersAll.lean); at `.small` it
is `Hd.SmallH X.hS X.HLy (borderOf X.y) (P5J.ownQ cs arr ms N s seat w 24)`
(Johnson/Desc/Kinds/Law/HeadCutsK6.lean); `Hd.SmallH` (Johnson/Road/HeadL5B.lean) asks that the
entries of the head's list be below 2 ^ 18 in absolute value, inside four ranges, AND NOTHING ELSE;
`P5J.ownQ` := `Meaning.ownOf s` at symbols read off the witness (Johnson/P5J/CellQ.lean): integers
that are made by UNPACKING symbols: each is small or 0, whatever the symbols.
  `smallH_ownOf`: at every family of symbols, where the shift is not 0 and twice the shift is at
    most 2 ^ 18 at segment 24: by `Meaning.small_ownOf_all` (Johnson/Goal/Meaning/HidReads.lean)
    and `Hd.smallH_of_all`.
  `headSmall_at`: **the part, at the constant, at every index, state, strings and witness.**
WHAT IT DOES NOT SAY. THE PART IS IDLE: it holds of every witness, so IT IS NO EVIDENCE THAT THE
COMMITTED SYMBOLS ARE SMALL OR ARE A PACKING (the head of Johnson/Goal/Meaning/HidFamilyParts.lean
says the like of the three clauses on smallness): that weight lies in the other premise of
`small_at_head`, `SeatShows`, and in the tie.
Limits. A member of the head `AtMgA` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness or on hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Goal.Meaning.HidReads
import Johnson.Road.HeadL5B

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open P5J (AtMgA)

/-- **By the make**: the head's list behind symbols meets the head's clause on smallness. -/
theorem smallH_ownOf {s : ℕ → Cb.Pv.Tail.Size} (y : ∀ k, Cb.Pv.Tail.Syms Cb.Gl.E (s k))
    (h0 : (0 : ℤ) < ((s 24).beta : ℤ)) (h2 : 2 * ((s 24).beta : ℤ) ≤ 2 ^ 18)
    (X : Model.Verify.Public) :
    OnBytes.Road.Hd.SmallH X.hS X.HLy (borderOf X.y) (Meaning.ownOf s y 24) :=
  OnBytes.Road.Hd.smallH_of_all fun a r c => Meaning.small_ownOf_all y h0 h2 a r c

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE HEAD's OWN PART "small", AT THE CLOSED CONSTANT.** -/
theorem headSmall_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    ∀ i a y w, h.𝔇.headPart .small i a y w := by
  intro i a y w
  show OnBytes.Road.Hd.SmallH (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y)
    (P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (Meaning.sizesOf (P5J.At.X Zp))
      (VerifiableInference.Desc.Kinds.Head.Law.seatLay (P5J.At.X Zp) (P5J.At.layout Zp)
        (P5J.At.num Zp)) w 24)
  exact smallH_ownOf _ (by
    show (0 : ℤ) < (((2 : ℕ) ^ 17 : ℕ) : ℤ)
    norm_num) (by
    show 2 * (((2 : ℕ) ^ 17 : ℕ) : ℤ) ≤ 2 ^ 18
    norm_num) _

end

end P1K8T

#print axioms P1K8T.smallH_ownOf
#print axioms P1K8T.headSmall_at
