-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowWhole.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), AT THE BLOCK's ONE HEARING, UNDER ONE
RULE BY NAME: STATED AND PROVED.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like.
That the 35 forms are 0, that the claim on the weights is true: premises (what the block OPENS).
How probable a bad draw is: lists are counted, no sum of errors is taken. THE POINT pV HAS NO PLACE IN THE RULE: its lt
coordinates are drawn in one round, and a rule of NoBad's shape sees no coordinate of the round at whose message it
stands: "pV is not bad" (the bridge's BadP) IS ONE PREMISE OF ITS OWN, BY NAME (GoodPoint). That an honest run meets the
premises: not shown. 0 < d IS A PREMISE ON THE PLAN's PUBLIC NUMBERS: planOk does not test it (d % S2 = 0 holds at d = 0),
and ls ≤ lPd, which the squares' level wants, fails at d = 0 < ls.
WHAT IT IS.
  rowRule            THE BLOCK's ONE RULE: at a front of the block's rounds, the list of the normalization's own rounds' rule
                     (normRule, Law/NormRule.lean) and behind it the list of Law/OutBlock.lean's blockRule.
  rowRule_length_sum its ceiling AS A SUM: at most twice (the last message's scalars and one). (The two lists are never both
                     non-empty: Law/RowCeil.lean: there the ceiling is the one that each has.)
  normReads_true     the three reads that the normalization's 26 forms spend, READ AS THE STATED SUMS OF THE CELLS
                     (normReadsAtCells), are true by their definition, where pV and the products' challenges have lt
                     coordinates.
  RowWholeStatement  OPENED, behind the block, at any ledger G later than the one that the block lays: ALL 35 FORMS of the
                     block's three runs worth 0; the claim on the weights true. CLOSED, in front: at every position's
                     corner the row's 17 forms are 0 (the clause "rows" of CellRelN), and all that Law/RowHalf.lean closes.
IMPORTED, NOT PROVED HERE: norm_block, norm_parts (Law/NormRule.lean, Law/NormHear.lean), rd_sum_point (Law/NormPoint.lean; the
lines of digit_true follow its cv_rowForm_point); keeps_sumcheck (Law/Keeps.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowHalf
import Johnson.Desc.Kinds.Law.NormRule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- **THE BLOCK's ONE RULE, BY NAME.** -/
noncomputable def Came.rowRule [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) : List Fmt.RoundView → List E :=
  fun h => normRule c mask F h ++ Came.blockRule c mask F h

/-- **The one bad event that is no rule**: the point on the positions, drawn whole in the block's first round. -/
def GoodPoint [Sizes] [Policy] [Request] [Token] (c : NCells) (pV : Point) : Prop :=
  ¬ (dataOf c).BadP (tupK pV)

/-- **THE ROW, WITH THE 17 ROW FORMS.** -/
def RowWholeStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork),
    planOk sT = true → 0 < d → Request.ok = true → y < V → WellLaid F → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∀ (rs : List Fmt.RoundView) (H : HeardAll) (F1 G : Fork),
      Canonical rs → hear F rs = some (H, F1, []) → Later F1 G → NoBad (Came.rowRule c mask F) rs →
      GoodPoint c H.1.pV →
      let _ : Norm.Heard := H.1
      let _ : FinalNorm.Heard := H.2.1
      let _ : Heard := H.2.2
      let _ : FinalNorm.Reads := normReadsAtCells c
      let _ : Reads := readsAt c.toCells
      WeightTrue c.toCells G mask noEnt →
      (∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) →
      (∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) ∧
      (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
      (∀ call, call < 6 →
        rd (atWorld G mask noEnt
            (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
          = (Finset.range (2 ^ (zk call).size)).sum fun i =>
              rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
      (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
      (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0

namespace Came

theorem noBad_left {a b : List Fmt.RoundView → List E} {rs : List Fmt.RoundView}
    (h : NoBad (fun f => a f ++ b f) rs) : NoBad a rs :=
  fun i r hi x hx hm => h i r hi x hx (List.mem_append_left _ hm)

theorem noBad_right {a b : List Fmt.RoundView → List E} {rs : List Fmt.RoundView}
    (h : NoBad (fun f => a f ++ b f) rs) : NoBad b rs :=
  fun i r hi x hx hm => h i r hi x hx (List.mem_append_right _ hm)

/-- The ceiling, as a sum. -/
theorem rowRule_length_sum [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) (h : List Fmt.RoundView) : (rowRule c mask F h).length
      ≤ 2 * (((h.getLast?.map fun r => r.vals.length).getD 0) + 1) := by
  unfold rowRule
  rw [List.length_append]
  have h1 := normRule_length c mask F h
  have h2 := blockRule_length c mask F h
  omega

section Sized
variable [Sizes] [Policy] [Request] [Token]

theorem ls_le_lPd (hd : 0 < d) (hdS : S2 ∣ d) : ls ≤ lPd := by
  have h1 : 2 ^ ls ≤ d := Nat.le_of_dvd hd hdS
  have h2 : d ≤ 2 ^ lPd := le_two_pow_clog2 d
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h1.trans h2)

/-- A digit of the row, read under a point's weights, with its offset: the extension of the positions' digits. -/
theorem digit_true (c : NCells) (z : Point) (hz : z.size = lt) (j : Nat) :
    rd (sumTo T fun t' => eq z t' * ofInt (c.cell .row j t')) + ((off1 : Nat) : K)
      = Blocks.ext lt (fun t => dK c t j) (ptK z) := by
  rw [rd_sum_point _ hz]
  have : (fun t => dK c t j) = fun t => rd (ofInt (c.cell .row j t)) + ((off1 : Nat) : K) := by
    funext t
    rw [rd_ofInt]
    unfold dK digZ off1
    push_cast
    ring
  rw [this, Blocks.ext_add, Blocks.ext_const]

/-- **The normalization's three reads, in truth.** -/
theorem normReads_true [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] (W : World K) (c : NCells)
    (hz : (Norm.pV).size = lt) (hr : (Norm.products.r).size = lt) :
    let _ : FinalNorm.Reads := normReadsAtCells c
    NormReads W c := by
  intro _
  refine ⟨fun j _ => ?_, fun j _ => ?_, fun i _ => val_coe _ _⟩
  · show val W (HAdd.hAdd (α := Form) (β := Nat) (γ := Form)
      ((sumTo T fun t' => eq Norm.pV t' * ofInt (c.cell .row j t') : E) : Form) off1) = _
    rw [val_addN, val_coe]
    exact digit_true c Norm.pV hz j
  · show val W (HAdd.hAdd (α := Form) (β := Nat) (γ := Form)
      ((sumTo T fun t' => eq Norm.products.r t' * ofInt (c.cell .row j t') : E) : Form) off1) = _
    rw [val_addN, val_coe]
    exact digit_true c Norm.products.r hr j

end Sized

theorem rowWhole : RowWholeStatement := by
  intro _ _ _ _ nI hI sT floor zx zk c mask F hplan hd0 hreq hy hWL hP hn hh rs H F1 G hcan hhear hL hnb
    hgood _ _ _ _ _ hwt hall
  refine ⟨?_, rowHalf sT floor zx zk c mask F hplan hreq hy hWL hP hn hh rs H F1 G hcan hhear hL
    (noBad_right hnb) hwt hall⟩
  have P := planFacts hplan
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  obtain ⟨Fa, Fb, l1, hNorm, _, _, hsN, hsL, _⟩ := hear_parts hWL hhear
  have LG : Later Fa G :=
    ((keeps_sumcheck _ _ _ _ _ _ _ hsN).trans (keeps_sumcheck _ _ _ _ _ _ _ hsL)).trans hL
  obtain ⟨p0, p1, tS, p2, tP, _, _, Fc, _, h0, _, _, _, _, h5, _⟩ := norm_parts hWL hNorm
  have hz : H.1.pV.size = lt := drawPoint_size h0
  have hr : H.1.products.r.size = lt := (sum_r_size h5).trans hz
  exact norm_block c mask F hWL (ls_le_lPd hd0 hdS) hdS (worldE G mask noEnt) hcan hNorm LG
    (fun _ => rfl) (noBad_left hnb) hgood (normReads_true _ c hz hr) (fun f hf => by
      show vW (worldE G mask noEnt) f = 0
      rw [← rd_atWorld, hall "norm" FinalNorm.forms (by simp [claims]) f
        (List.mem_append_left _ hf), rd_zero])

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowRule_length_sum
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.normReads_true
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowWhole
