-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/DeadMark.lean: THE SMALLNESS TEST: "SOME COLUMN OF THE DRAWN MATRIX IS ALL 0" AS A
MARK (`Mark`, Johnson/Desc/ProofFile/Honest/Law/Marks.lean): A PLACE, A TEST ON CHALLENGES, A STATED
SHARE; THE SHARE HELD AGAINST THE TEST (`Held`, Johnson/Desc/ProofFile/Honest/Law/SharesHeld.lean)
AT TYPED CHALLENGES AND AT STRINGS OF HASH BLOCKS; THE PLACE HELD AGAINST THE DESCRIPTION's LIST.
Definitions and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

The verifier refuses nothing at the round that draws the matrix. The event is counted there all the
same: the first fall's test (`k8Front`) is small at the batching's round only where no column is all
0 (Johnson/Desc/ProofFile/Honest/K8/FrontDead.lean).
  `drawPlace link o`   the place of the member that hears the draw: piece 5 + o of the segment, o =
      1 at the head's, else 0
  `deadMark link o sz`   the mark: that place; `deadT sz` (Johnson/Desc/K8/Honest/DeadTest.lean) on
      the member's own challenges; the share columns of 2 ^ tau
  `dead_mark_ok`, `dead_mark_val`, `dead_mark_test`   the share's denominator is not 0; its value;
      the test says something just where `deadT` says yes
  **`dead_mark_held`**, **`dead_mark_held_blocks`**   d a round's data whose list of draws is
      [.trits (columns * tau)]: at every list of challenges in front: the stated share is held
      against the mark's test at [d], at Run.ck .two; and at Run.ckP .two, if the entry's positions
      have at most 64 bits
  `drawB`, `drawB_full`, **`draw_place`**, `draw_there`   in the goals' scope: drawPlace l o stands
      at number 14 l + 6, or 343 at the head's, of the first chain's flat list, and nowhere else: a
      closed evaluation by Lean's kernel on the written list of places
  `kap_val`, `share_val_gen`, **`fall_share_val`**, `fall_share_ok`   the share columns * (tau - 1)
      * (2 ^ 128 + 1) ^ 3 of pGold ^ 3 * 2 ^ 384 has the value kapSl 128 ^ 3 * (columns * (tau - 1))
      / p ^ 3: the number of `front_gate_blocks` (Johnson/P1K8R/FrontBlocks.lean); its denominator
      is not 0
By: `dead_gate_test` · `dead_gate_blocks` (Johnson/P1K8R/DeadBlocks.lean) · `onlyAt` and its laws,
`place_at` (Johnson/P1K8R/PlacesAtFlat.lean) · two_p (OnBytes/Slice/Field.lean).
Limits. That sz is the size of the place, and d the data of the description's round, is not said.
Which falls lean on the mark is not said. No number is evaluated.
-/
import Johnson.P1K8R.DeadBlocks
import Johnson.P1K8R.PlacesAtFlat
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld
import OnBytes.Slice.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound (linksFull)
open ProofFile.Honest (Odds Mark Held)
open Iop
open scoped ENNReal

/-- The place of the member that hears the draw. -/
def drawPlace (link o : Nat) : Place := ⟨1, some link, 5 + o, .K8⟩

/-- **The mark.** -/
def deadMark (link o : Nat) (sz : Size) : Mark :=
  { place := drawPlace link o
    test := fun _ own =>
      if deadT sz own then some "the smallness test: a column of the drawn matrix is all 0"
      else none
    share := ⟨sz.columns, 2 ^ sz.tau⟩ }

theorem dead_mark_ok (link o : Nat) (sz : Size) : (deadMark link o sz).share.ok = true := by
  show ((2 ^ sz.tau : ℕ) != 0) = true
  simp

theorem dead_mark_val (link o : Nat) (sz : Size) :
    (deadMark link o sz).share.val = (sz.columns : ℝ≥0∞) / 2 ^ sz.tau := by
  show ((sz.columns : ℕ) : ℝ≥0∞) / ((2 ^ sz.tau : ℕ) : ℝ≥0∞) = _
  push_cast
  rfl

theorem dead_mark_test (link o : Nat) (sz : Size) (fr own : List Fmt.Drawn) :
    ((deadMark link o sz).test fr own).isSome = deadT sz own := by
  show (if deadT sz own then some _ else none : Option String).isSome = _
  cases deadT sz own <;> rfl

/-- **The stated share is held, at typed challenges.** -/
theorem dead_mark_held (link o : Nat) (sz : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (sz.columns * sz.tau)]) (fr : List Fmt.Drawn) :
    Held (_root_.Run.ck .two) [d] (fun own => ((deadMark link o sz).test fr own).isSome)
      (deadMark link o sz).share := by
  refine ⟨dead_mark_ok link o sz, ?_⟩
  rw [dead_mark_val]
  simp only [dead_mark_test]
  exact dead_gate_test sz d h

/-- **The stated share is held, at strings of hash blocks.** -/
theorem dead_mark_held_blocks (link o : Nat) (sz : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (sz.columns * sz.tau)]) (hlog : d.entry.logN ≤ 64)
    (fr : List Fmt.Drawn) :
    Held (_root_.Run.ckP .two) [d] (fun own => ((deadMark link o sz).test fr own).isSome)
      (deadMark link o sz).share := by
  refine ⟨dead_mark_ok link o sz, ?_⟩
  rw [dead_mark_val]
  simp only [dead_mark_test]
  exact dead_gate_blocks sz d h hlog

/-! ## The place -/

/-- The test at the written list, at all 25 segments. -/
def drawB : Bool :=
  (List.range 25).all fun l =>
    onlyAt (flatPlacesOf linksFull true) (drawPlace l (if l = 24 then 1 else 0))
      (14 * l + (if l = 24 then 5 else 4) + 2)

set_option maxRecDepth 1000000 in
theorem drawB_full : drawB = true := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The mark's place stands at the draw's number alone.** -/
theorem draw_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) {n : ℕ}
    (h : (c.blocksInOrder[n]?).map (·.place) = some (drawPlace l (if l = 24 then 1 else 0))) :
    n = 14 * l + (if l = 24 then 5 else 4) + 2 :=
  onlyAt_gives (List.all_eq_true.1 drawB_full l (List.mem_range.2 hl))
    ((place_at hS hR O n).trans h)

theorem draw_there (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    (c.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]?).map (·.place) =
      some (drawPlace l (if l = 24 then 1 else 0)) :=
  (place_at hS hR O _).symm.trans
    (onlyAt_there (List.all_eq_true.1 drawB_full l (List.mem_range.2 hl)))

end

/-! ## The value of the fall's share with the factor -/

/-- The factor as a quotient of two naturals. -/
theorem kap_val (k : ℕ) : kapSl k = ((2 ^ k + 1 : ℕ) : ℝ≥0∞) / ((2 ^ k : ℕ) : ℝ≥0∞) := by
  have h0 : ((2 ^ k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (2 ^ k : ℕ) ≠ 0)
  have ht : ((2 ^ k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have e : ((2 ^ k : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by
    push_cast
    rfl
  unfold kapSl
  rw [Nat.cast_add, Nat.cast_one, ENNReal.add_div, ENNReal.div_self h0 ht, one_div, e]

/-- A share that bears the factor's cube, at whatever exponent. -/
theorem share_val_gen (n q k : ℕ) :
    (⟨n * (2 ^ k + 1) ^ 3, q * (2 ^ k) ^ 3⟩ : Odds).val =
      kapSl k ^ 3 * (n : ℝ≥0∞) / (q : ℝ≥0∞) := by
  have h0 : ((2 ^ k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (2 ^ k : ℕ) ≠ 0)
  have ht : ((2 ^ k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  show ((n * (2 ^ k + 1) ^ 3 : ℕ) : ℝ≥0∞) / ((q * (2 ^ k) ^ 3 : ℕ) : ℝ≥0∞) = _
  rw [kap_val, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  generalize ((2 ^ k + 1 : ℕ) : ℝ≥0∞) = A
  generalize ((2 ^ k : ℕ) : ℝ≥0∞) = B at h0 ht
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top ht)) (Or.inr (pow_ne_zero _ h0)), mul_pow,
    ENNReal.inv_pow]
  ring

theorem fall_share_ok (columns tau : ℕ) :
    (⟨columns * (tau - 1) * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * 2 ^ 384⟩ : Odds).ok = true := by
  have hp : Code.pGold ^ 3 ≠ 0 := by
    rw [← OnBytes.Slice.two_p]
    decide
  show ((Code.pGold ^ 3 * 2 ^ 384 : ℕ) != 0) = true
  simp only [bne_iff_ne, ne_eq, Nat.mul_eq_zero, not_or]
  exact ⟨hp, by positivity⟩

/-- **The share with the factor has the proved number as its value.** -/
theorem fall_share_val (columns tau : ℕ) :
    (⟨columns * (tau - 1) * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * 2 ^ 384⟩ : Odds).val =
      kapSl 128 ^ 3 * ((columns * (tau - 1) : ℕ) : ℝ≥0∞) /
        ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have e384 : (2 : ℕ) ^ 384 = (2 ^ 128) ^ 3 := by rw [← pow_mul]
  rw [e384, OnBytes.Slice.two_p]
  exact share_val_gen (columns * (tau - 1)) (Code.pGold ^ 3) 128

end P1K8

#print axioms P1K8.drawPlace
#print axioms P1K8.deadMark
#print axioms P1K8.dead_mark_ok
#print axioms P1K8.dead_mark_val
#print axioms P1K8.dead_mark_test
#print axioms P1K8.dead_mark_held
#print axioms P1K8.dead_mark_held_blocks
#print axioms P1K8.drawB
#print axioms P1K8.drawB_full
#print axioms P1K8.draw_place
#print axioms P1K8.draw_there
#print axioms P1K8.kap_val
#print axioms P1K8.share_val_gen
#print axioms P1K8.fall_share_ok
#print axioms P1K8.fall_share_val
