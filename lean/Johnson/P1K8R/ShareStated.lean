-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ShareStated.lean: THE SMALLNESS TEST's SECOND FALL: THE LAWS ON ITS STATED NUMBER
(`shareCount`, `k8CountShare`, `k8ShareAt`: definitions with code in a light file of their own,
Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean): IT IS THE NUMBER THAT
`share_fallDebt_last_blocks` (Johnson/P1K8R/BehindLast.lean) COUNTS; AND THE FALL's RECORD AT THAT
SHARE AND AT THE LOT's OWN LENGTHS OF THE VECTORS OF READS HAS ITS OWN SHARE's VALUE AS ITS BOUND,
UNDER `PLast` (Johnson/P1K8R/LastAtFrame.lean). Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  `shareCount_eq`   the light file's count, where three counts are written out in place, is the
      count with `linkedCount`, `symCount`, `secondN` by their names: by rfl
  `k8ShareAt_of`   where both look-ups return
  `nU_is_lot`   (ProofFile.k8ParW Z G X l).nU is ProofFile.k8NU G X (Johnson/Desc/ProofFile/Lot/K8.lean): by
      definition
  `countShare_ok`, `countShare_val`, **`countShare_sum`**   the share's denominator is not 0; its
      value; that value is the written sum: `share_val_gen` (Johnson/P1K8R/DeadMark.lean)
  **`last_hF_stated`**, **`last_hF_at`**   `last_hF_blocks` at that share
Limits. THE NUMBER IS HELD UNDER `PLast` ALONE: it counts values of the one batching element at a
state that meets `WrapEnd`, `ShareLive`, `LiveFore` and `StillAtZ`. THE CHANCE THAT AN EARLIER DRAW
LEAVES A STATE THAT FAILS `ShareLive` OR `LiveFore` IS NOT IN IT: that is the matter of marks, each
with a number of its own. Marks that bear on these are typed by several kinds' authors. What their
silence gives is typed, test by test, in younger files of this folder: `symbolsLive`
(AsksSymbols.lean); `planesLive`, `digitsLive` and `LiveFore` (AsksLooks.lean); `readsLive`
(AsksLayersLive.lean, AsksHeadLive.lean, AsksAllLive.lean). NOT OUTRIGHT: every one of these lemmas
has hypotheses of its own and speaks of the state in which a walk ends: see what those files say
under "Limits". NONE OF THIS IS JOINED TO `PLast` OR TO THIS NUMBER IN THIS FILE. It is another
number than `k8FallShare` (Johnson/Desc/ProofFile/Honest/K8/FallShare.lean: the format's own counts,
held against nothing). WHERE THE BUILT SEGMENT OR THE BATCHING's NUMBERS LACK, `k8ShareAt` SAYS 0 OF
1: A FILLER, NO CLAIM THAT NOTHING FALLS THERE; in the goals' scope, under an opening, at l < 25,
both are there: they are the X and the p of `last_hF_at`. `RowsAsked Z` is a premise. No number is
evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LastAtFrame
import Johnson.P1K8R.DeadMark
import Johnson.Desc.ProofFile.Honest.K8.FallNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- **The count of the light file (Johnson/Desc/ProofFile/Honest/K8/FallNumbers.lean), where three
counts are written out in place, is the count with these three by their names.** -/
theorem shareCount_eq (nU : Array Nat) (tl : HTailF2) (rows : Nat) :
    shareCount nU tl rows =
      nU.getD 2 0 * (rows - 1) + (2 * (tl.zzBlocks * tl.mz) * (rows - 1) +
        (linkedCount tl * (rows - 1) + (3 * tl.bzColumns * (rows - 1) +
          (symCount tl * (rows - 1) + secondN tl)))) := rfl

theorem k8ShareAt_of {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {X : LinkH} {p : K9.Where}
    (hX : G.built[l]? = some X) (hp : IM.k9At Z l = some p) :
    k8ShareAt Z G l = k8CountShare (ProofFile.k8ParW Z G X l).nU X.tl p.rows := by
  unfold k8ShareAt
  rw [hX, hp]

/-- The lengths of the vectors of reads in the lot's own numbers of a place are those at which the
counted sentences speak. -/
theorem nU_is_lot (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : LinkH) (l : ℕ) :
    (ProofFile.k8ParW Z G X l).nU = ProofFile.k8NU G X := rfl

/-- Its denominator is not 0. -/
theorem countShare_ok (nU : Array Nat) (tl : HTailF2) (rows : Nat) :
    (k8CountShare nU tl rows).ok = true := by
  have hp : Code.pGold ^ 3 ≠ 0 := by
    rw [← OnBytes.Slice.two_p]
    decide
  show ((Code.pGold ^ 3 * 2 ^ 384 : ℕ) != 0) = true
  simp only [bne_iff_ne, ne_eq, Nat.mul_eq_zero, not_or]
  exact ⟨hp, by positivity⟩

/-- Its value. -/
theorem countShare_val (nU : Array Nat) (tl : HTailF2) (rows : Nat) :
    (k8CountShare nU tl rows).val =
      kapSl 128 ^ 3 * ((shareCount nU tl rows : ℕ) : ℝ≥0∞) /
        ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have e384 : (2 : ℕ) ^ 384 = (2 ^ 128) ^ 3 := by rw [← pow_mul]
  unfold k8CountShare
  rw [e384, OnBytes.Slice.two_p]
  exact share_val_gen (shareCount nU tl rows) (Code.pGold ^ 3) 128

/-- **Its value is the written sum of `share_fallDebt_last_blocks`.** -/
theorem countShare_sum (Bs : ProofFile.PureBase) (p : K9.Where) (X : LinkH) :
    (k8CountShare (ProofFile.k8NU Bs.G₀ X) X.tl p.rows).val =
      (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
      ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      (kapSl 128 ^ 3 * ((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
      ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      (kapSl 128 ^ 3 * ((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
      ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      (kapSl 128 ^ 3 * ((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) /
      ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      (kapSl 128 ^ 3 * ((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
      ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      (kapSl 128 ^ 3 * ((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
      0)))))) := by
  rw [countShare_val, shareCount_eq]
  simp only [Nat.cast_add, mul_add, ENNReal.add_div, add_zero]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SECOND FALL's RECORD WITH THE COUNTED NUMBER AS ITS STATED SHARE, AT THE LOT's OWN nU: ITS
BOUND IS ITS OWN SHARE's VALUE**, at strings of hash blocks, in the form of the frame's hypothesis
hF, under `PLast`. `last_hF_blocks` (Johnson/P1K8R/LastAtFrame.lean) at that share. -/
theorem last_hF_stated (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (ft : ℕ) (dsb : List RDT), List.Forall₂ KindFits dsb b.rounds →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8ParW Z Bs.G₀ X l).nU
            (k8CountShare (ProofFile.k8ParW Z Bs.G₀ X l).nU X.tl p.rows)) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) dsb [] (PLast Z c Bs l)
          (k8CountShare (ProofFile.k8ParW Z Bs.G₀ X l).nU X.tl p.rows).val := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := last_hF_blocks hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun ft dsb hd => ?_⟩
  rw [nU_is_lot, countShare_sum]
  exact H ft _ dsb hd

/-- **The same with the share as a function of the segment's number.** -/
theorem last_hF_at (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (ft : ℕ) (dsb : List RDT), List.Forall₂ KindFits dsb b.rounds →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8ParW Z Bs.G₀ X l).nU
            (k8ShareAt Z Bs.G₀ l)) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) dsb [] (PLast Z c Bs l)
          (k8ShareAt Z Bs.G₀ l).val := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := last_hF_stated hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun ft dsb hd => ?_⟩
  rw [k8ShareAt_of (by rw [← Array.getElem?_toList]; exact hX) hp]
  exact H ft dsb hd

end

end P1K8

#print axioms P1K8.shareCount_eq
#print axioms P1K8.k8ShareAt_of
#print axioms P1K8.nU_is_lot
#print axioms P1K8.countShare_ok
#print axioms P1K8.countShare_val
#print axioms P1K8.countShare_sum
#print axioms P1K8.last_hF_stated
#print axioms P1K8.last_hF_at
