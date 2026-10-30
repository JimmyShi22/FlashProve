-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SecondNz.lean: THE SMALLNESS TEST: UNDER THE EQUALITIES OF THE VERIFIER's TWO
TESTS ON WEIGHTS BY A SECOND COMPUTATION (`SecondEqs`, Johnson/Desc/K8/Honest/SecondParts.lean), AND
WHERE THE LOOKUP's OWN VALUES ARE NOT 0 (`PieceLive`), THE REST OF THE TWO TESTS ("NOT 0", "ALL
DIFFERENT") FAILS ONLY WHERE THE BATCHING ELEMENT IS 0 OR TWO OF ITS POWERS MEET. A definition and
lemmas; none of the library's goals. No prover stands in them; nothing on completeness, soundness or
hiding.

  `ne_of_val`, `wants_rp`, `kappa_val`, `radb_val`   a word whose value is not 0 is not the word 0;
      every wanted piece has a row; the claim's weight by text reads as the power; the radix 2^20 is
      not 0 in the field
  `PieceLive tl g W`   on what the lookup heard and the plan's numbers, by values: at each wanted
      piece the call's weight and the equality weights that the test multiplies are not 0
  **`pieceNz_of`**, **`tieNz_of`**   under its equalities each test's "not 0" comes down to such
      values and to the batching element's
  **`second_speaks`**   the sentence of the title
By: `differ_no_powers`, with `coef_mat`: the row's weights ARE the data's powers, whole
(Johnson/Desc/K8/Honest/CoefClosed.lean) · TailClaims.wants_iff, neighboursDiffer_iff
(Johnson/Desc/First/TailClaims/AgainMeans.lean), wants_eq, neighboursDiffer_eq (AgainAgrees.lean) ·
powersAgain_val (OnBytes/Tie/Pv/Tail/EndTested.lean) · val_two_pow (EndClaims.lean) · scaleE_val
(OnBytes/Iop/RowLaws.lean) · gl_two_ne_zero (Cb/Pv/Head/NormGl.lean) · K9L.core_coefBody
(Johnson/Desc/First/Batch/Law/Coef.lean).
Limits. `SecondEqs`, `PieceLive`, `Powered` and the three premises on the ledger's frame are shown
of no state here. No count.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.SecondParts
import Johnson.Desc.K8.Honest.CoefClosed
import Johnson.Desc.First.Batch.Law.Coef
import OnBytes.Tie.Pv.Tail.EndTested
import OnBytes.Iop.RowLaws
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (coefAll rowAt HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered powersAgain_val val_two_pow)
open VerifiableInference.Desc.First.TailClaims (eqAt coefBody)

/-- A word whose value is not 0 is not the word 0. -/
theorem ne_of_val {a : E} (h : Reading.gl.val a ≠ 0) : a ≠ zeroE := fun e =>
  h (by rw [e, Reading.gl.zero])

/-- Every wanted piece has a row. -/
theorem wants_rp {tl : HTailF2} {nbW : Nat} {W : List Want} (h : tl.wants = some (nbW, W)) :
    ∀ w ∈ W, 0 < w.Rp := by
  have h' : TailClaims.wants tl = some (nbW, W) := by
    rw [TailClaims.wants_eq]
    exact h
  obtain ⟨-, e⟩ := (TailClaims.wants_iff tl _).1 h'
  obtain ⟨-, rfl⟩ := Prod.mk.inj e
  intro w hw
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 hw
  rcases List.mem_cons.1 hq with rfl | hq
  · exact Nat.two_pow_pos _
  · split at hq
    · rename_i hne
      obtain rfl := List.mem_singleton.1 hq
      exact Nat.pos_of_ne_zero (by simpa using hne)
    · exact absurd hq List.not_mem_nil

/-- **On what the lookup heard and the plan's numbers**: the call's weight and the equality weights
that the test on a piece's weights multiplies are not 0, by values. -/
def PieceLive (tl : HTailF2) (g : Forest.Heard) (W : List Want) : Prop :=
  ∀ w ∈ W, Reading.gl.val (callWeightAgain g w.call) ≠ 0 ∧
    (∀ cc < w.Cp, Reading.gl.val
      (eqAt (g.zk.getD w.call #[]) ((tl.zOf w.call).pieces.getD w.i {}).off cc) ≠ 0) ∧
    ∀ r < w.Rp, Reading.gl.val (eqPlainF (g.zk.getD w.call #[])
      (((tl.zOf w.call).pieces.getD w.i {}).off + r * ((tl.zOf w.call).pieces.getD w.i {}).CP)) ≠ 0

/-- **Under its equalities the piece's "not 0" comes down to values outside the ledger.** -/
theorem pieceNz_of (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want)
    (hE : PieceEqs tl F g kappa w) (hR : 0 < w.Rp) (hk : Reading.gl.val kappa ≠ 0)
    (h1 : Reading.gl.val (callWeightAgain g w.call) ≠ 0)
    (h2 : ∀ cc < w.Cp, Reading.gl.val
      (eqAt (g.zk.getD w.call #[]) ((tl.zOf w.call).pieces.getD w.i {}).off cc) ≠ 0)
    (h3 : ∀ r < w.Rp, Reading.gl.val (eqPlainF (g.zk.getD w.call #[])
      (((tl.zOf w.call).pieces.getD w.i {}).off + r * ((tl.zOf w.call).pieces.getD w.i {}).CP)) ≠
        0) : PieceNz tl F g kappa w := by
  unfold PieceEqs at hE
  unfold PieceNz
  dsimp only at hE ⊢
  obtain ⟨-, e2, -⟩ := hE
  have hka : Reading.gl.val (mulE kappa (callWeightAgain g w.call)) ≠ 0 := by
    rw [Reading.gl.mul]
    exact mul_ne_zero hk h1
  have hmk : Reading.gl.val (subE zeroE (mulE kappa (callWeightAgain g w.call))) ≠ 0 := by
    rw [Reading.gl.sub, Reading.gl.zero, zero_sub]
    exact neg_ne_zero.2 hka
  have hv : ∀ e, Reading.gl.val e ≠ 0 →
      mulE (subE zeroE (mulE kappa (callWeightAgain g w.call))) e ≠ zeroE := fun e he =>
    ne_of_val (by rw [Reading.gl.mul]; exact mul_ne_zero hmk he)
  have h0 := e2 0 hR
  have hp : Reading.gl.val
      (((F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}).coef.getD (w.r0 + 0) zeroE) *
      Reading.gl.val (((F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}).L.getD w.c0 zeroE) ≠ 0 := by
    rw [← Reading.gl.mul, h0, Reading.gl.mul]
    exact mul_ne_zero hmk (h3 0 hR)
  exact ⟨ne_of_val hka, ne_of_val (left_ne_zero_of_mul hp), ne_of_val (right_ne_zero_of_mul hp),
    fun cc h => hv _ (h2 cc h), fun r h => hv _ (h3 r h)⟩

/-- The weight of claim number c, one factor at a time, reads as the power. -/
theorem kappa_val (theta : E) : ∀ c : Nat,
    Reading.gl.val (t2fKappaByText theta c) = Reading.gl.val theta ^ c
  | 0 => by
    show Reading.gl.val oneE = _
    rw [Reading.gl.one, pow_zero]
  | c + 1 => by
    have e : t2fKappaByText theta (c + 1) = mulE (t2fKappaByText theta c) theta := by
      unfold t2fKappaByText
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e, Reading.gl.mul, kappa_val theta c, pow_succ]

/-- The radix is not 0 in the field. -/
theorem radb_val : Reading.gl.val (ofF (fOfNat radb)) ≠ 0 := by
  have e : Reading.gl.val (ofF (fOfNat radb)) = (2 : Cb.Gl.E) ^ 20 :=
    val_two_pow Reading.gl 20 (by decide +kernel)
  rw [e]
  exact pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero

/-- **Under its equalities the tie's "not 0" comes down to the batching element's.** -/
theorem tieNz_of (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) (hE : TieEqs tl F L5 mu)
    (hRS : (tl.shp.getD mu {}).R = (tl.shp.getD mu {}).mS)
    (ht : Reading.gl.val F.theta ≠ 0) : TieNz tl F mu := by
  unfold TieEqs at hE
  unfold TieNz
  dsimp only at hE ⊢
  obtain ⟨-, e2, -⟩ := hE
  have hhi : ∀ R < (tl.shp.getD mu {}).mS, Reading.gl.val
      ((powersAgain F.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD R zeroE) ≠ 0 :=
    fun R h => by
      rw [powersAgain_val Reading.gl _ _ _ _ h]
      exact pow_ne_zero _ ht
  refine ⟨fun R h => ?_, fun R h i _ _ => ?_⟩
  · rw [e2 R h]
    exact ne_of_val (hhi R (hRS ▸ h))
  · have hx : Reading.gl.val (mulE (powE F.theta (F.planClaimsF + tl.firstAgain mu))
        ((powersAgain F.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD R zeroE)) ≠ 0 := by
      rw [Reading.gl.mul, Reading.gl.pow]
      exact mul_ne_zero (pow_ne_zero _ ht) (hhi R h)
    have hxB := mul_ne_zero radb_val hx
    rw [← OnBytes.scaleE_val] at hxB
    have hxBB := mul_ne_zero radb_val hxB
    rw [← OnBytes.scaleE_val] at hxBB
    split_ifs
    · exact ne_of_val hx
    · exact ne_of_val hxB
    · exact ne_of_val hxBB

/-- **WHERE THE REST FAILS: THE BATCHING ELEMENT IS 0, OR TWO OF ITS POWERS MEET.** -/
theorem second_speaks (tl : HTailF2) (F : Fork) {g : Forest.Heard} {jo nbW : Nat} {W : List Want}
    (hg : tl.heard = some g) (hj : tl.joinObj9 = some jo) (hw : tl.wants = some (nbW, W))
    (hE : SecondEqs tl F) (hL : PieceLive tl g W) (hP : Powered tl F.theta)
    (hsz : tl.NM ≤ tl.shp.size) (hr : ∀ mu < tl.NM, HasRow F (tl.gtTree.getD mu 0) 0)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b)
    (hno : ¬ SecondRest tl F) :
    Reading.gl.val F.theta = 0 ∨ ∃ mu, mu < tl.NM ∧ ∃ i j, i < j ∧
      j < (tl.shp.getD mu {}).mS ∧
      (Reading.gl.val F.theta ^ tl.stepF) ^ i = (Reading.gl.val F.theta ^ tl.stepF) ^ j := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨ht, hm⟩ := hc
  have et : (coefBody tl g F).theta = F.theta := congrArg (·.2.1) (K9L.core_coefBody tl g F)
  refine hno fun g' jo' nbW' W' e1 e2 e3 => ?_
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans e1)
  obtain rfl : jo = jo' := Option.some.inj (hj.symm.trans e2)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hw.symm.trans e3))
  obtain ⟨p1, t1⟩ := hE g jo nbW W hg hj hw
  refine ⟨fun w hw' => ?_, fun mu hmu => ⟨?_, ?_⟩⟩
  · obtain ⟨l1, l2, l3⟩ := hL w hw'
    refine pieceNz_of tl _ g _ w (p1 w hw') (wants_rp hw w hw') ?_ l1 l2 l3
    rw [kappa_val, et]
    exact pow_ne_zero _ ht
  · exact tieNz_of tl _ _ mu (t1 mu hmu) (hP.shape mu hmu).2.2.1 (by rw [et]; exact ht)
  · by_contra hd
    have hb : neighboursDiffer
        ((rowAt (coefAll tl g F) (tl.gtTree.getD mu 0) 0).coef.toList.mergeSort
          TailClaims.leE) = false := by
      rw [← Bool.not_eq_true, ← TailClaims.neighboursDiffer_eq, TailClaims.neighboursDiffer_iff]
      exact hd
    exact hm ⟨mu, hmu, differ_no_powers tl g F F.theta TailClaims.leE hmu
      (Nat.lt_of_lt_of_le hmu hsz) (hr mu hmu) hinj hP hb⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.ne_of_val
#print axioms VerifiableInference.Desc.First.K8.Honest.wants_rp
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceNz_of
#print axioms VerifiableInference.Desc.First.K8.Honest.kappa_val
#print axioms VerifiableInference.Desc.First.K8.Honest.radb_val
#print axioms VerifiableInference.Desc.First.K8.Honest.tieNz_of
#print axioms VerifiableInference.Desc.First.K8.Honest.second_speaks
