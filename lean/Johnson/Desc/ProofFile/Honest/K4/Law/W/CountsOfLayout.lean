-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CountsOfLayout.lean: CONDITIONAL. THE FOUR COUNTS OF
`K4Counts` (Law/W/RowIsPlanForm.lean) ARE NOT 0 AT EVERY LAYOUT THAT THE VERIFIER's OWN FUNCTION
RETURNS, WHERE THE NUMBER OF LIMBS IS NOT 0.

What is here. PUBLIC NUMBERS ALONE. By the library's `laySizes_of_layout`
(Johnson/Road/K4/PlanSizes.lean) a layout that `Layer.layout` returns has NI = 2 * 2 ^ ll norms in a
group, NN = 2 and Lam = 2 ^ ll; the ledger's three numbers are 2 xl - 1, and 7 or 3, and 4 or 3
(OnBytes/Model/Ledger.lean). Statements and proofs. No number of the full size enters.

  `k4Counts_of_layout`: **the four, from «the layout is returned» and xl ≠ 0.**
  `k4Counts_of_covers`: the same where K4 covers the plan (`covers`,
      OnBytes/Desc/First/K4/Rounds.lean: five limbs).
  `k4Counts_of_public`: **at the layers' record of what the verifier's public part returns**,
      where K4 covers it.
  `k4Counts_no`: the definition is not always true: where a group has no norm, `K4Counts` is false.

Not shown here. hy: that the layout is one that the verifier's function returns · hx | hc: on the
number of limbs · hX: that the public part returns · hQ: that the public data's plan is that layers'
record: hypotheses. A record of the type `Lay` that no call of `layout` returns can have NI = 0:
there `k4Counts_no` speaks. It says nothing on the field states of `K4RowIsPlan`.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlanForm
import Johnson.Road.K4.PlanSizes
import Johnson.Road.HeadMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (nEndT)
open OnBytes.Road.K4 (laySizes_of_layout)
open OnBytes.Desc.First.K4 (covers)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub}

/-- CONDITIONAL: on hy and hx. **THE FOUR COUNTS AT A LAYOUT THAT THE VERIFIER's FUNCTION RETURNS.**
-/
theorem k4Counts_of_layout {h : Layer.Shape} {pc : List (List String)}
    (hy : Layer.layout h pc = .ok Q.P.y) (hx : Q.P.y.h.xl ≠ 0) : K4Counts Q := by
  have L := laySizes_of_layout hy
  have h2 : 0 < 2 ^ h.ll := Nat.two_pow_pos h.ll
  have hNI : Q.P.y.NI ≠ 0 := by
    rw [L.NI]
    omega
  have hS : ledNS Q.P.y.h.xl ≠ 0 := by
    unfold ledNS
    omega
  have hP : ledNP Q.P.y.h.xl ≠ 0 := by
    unfold ledNP
    split <;> decide
  have hO : ledNO Q.P.y.h.xl ≠ 0 := by
    unfold ledNO
    split <;> decide
  refine ⟨Nat.mul_ne_zero hS hNI, Nat.mul_ne_zero hP hNI, Nat.mul_ne_zero hO hNI, ?_⟩
  unfold nEndT
  rw [L.NN, L.Lam]
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega) (Nat.le_add_right _ _))

/-- CONDITIONAL: on hy and hc. The same where K4 covers the plan. -/
theorem k4Counts_of_covers {h : Layer.Shape} {pc : List (List String)}
    (hy : Layer.layout h pc = .ok Q.P.y) (hc : covers Q.P = true) : K4Counts Q := by
  refine k4Counts_of_layout hy fun e => ?_
  unfold covers at hc
  rw [e] at hc
  simp at hc

/-- CONDITIONAL: on hX, hQ and hc. **AT THE LAYERS' RECORD OF THE VERIFIER's PUBLIC PART.** -/
theorem k4Counts_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL lay = .ok X) (hQ : Q.P = X.layers) (hc : covers Q.P = true) :
    K4Counts Q :=
  k4Counts_of_covers (by rw [hQ]; exact (OnBytes.Road.Hd.publicH_of_public hX).lay) hc

/-- CONDITIONAL: on h. The definition is not always true: where a group has no norm the four do not
hold. -/
theorem k4Counts_no (h : Q.P.y.NI = 0) : ¬ K4Counts Q := fun c => c.1 (by rw [h, Nat.mul_zero])

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Counts_of_layout
#print axioms ProofFile.Honest.K4.W.k4Counts_of_covers
#print axioms ProofFile.Honest.K4.W.k4Counts_of_public
#print axioms ProofFile.Honest.K4.W.k4Counts_no
