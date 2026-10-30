-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldHolds.lean: behind a fold of the proximity test the claim is true at an
honest prover's three folded messages: on the fold's values alone (that the fold accepts is
FormFoldLaws.lean's). General in the stage; the core
names no record, no round's format and no place.

What the honest prover sends, as values of the field. In the round "FOLD epsilon": hMu W, the sum
over the cube of the polynomial with the coefficients W (hU, Cb/Ld/LdHide.lean). In each round "FOLD
round": the constant and the quadratic coefficient of that round's part of foldQ, the library's own
honest round polynomials (honQ, Cb/Ld/LdSum.lean). A round's part does not hang on later draws
(foldQ_causal).

Main names (namespace Johnson.Prover.Link).
  runQ k σ q γ   the verifier's running claim behind k rounds in which two of three coefficients are
      sent: the right side of readE_foldClaimRound (OnBytes/Slice/BlkFold.lean), k times
  runQ_rounds    at the round polynomials of ANY summand it ends in the summand's value at the
      drawn point
  Pairs s n0 W φ   THE ONE PREMISE ON THE FRESH TABLE φ, which is sent ahead of the fold: at every
      point the public weights (hideW, OnBytes/Slice/FoldPeel.lean) applied to φ folded at the
      point's first h coordinates give the polynomial's value
  foldQ          the honest round polynomials
  fold_core      THE CORE: the claim in front is true at μ, and φ pairs with W: then the claim
      behind (the running claim; midVec, OnBytes/Slice/FoldPeel.lean) is true at foldMsg s μ φ γ
      (Johnson/Prover/Link/FoldEnc.lean): at every drawn coefficient and every drawn point
  fold_turned    a test that can fail: another first scalar, no drawn element 0: false
  packed, pairs_packed   the library's packing of W (pkC, Cb/Ld/LdSumPack.lean) at the format's
      places (hidePlace, OnBytes/Slice/SimFold.lean) pairs with W
  Pairs.add_free   the columns from h + 2 g + 1 on are free: their weights are 0 (hideW_off)
  fr_room        the four folding stages of the full size have room for the packing
  Shows, claimOf_shows, sent_written   the rounds as the description's view has them
  fold_holds     the single rows that the description's fold returns (foldOutAt,
      Johnson/Prover/Link/FormFold.lean) are true at the three folded messages
  fold_V         the same from the record in front of a fold (FoldFront), at the rows in foldT

By calls: honQ_rounds, summand_sum, honQ_causal (Cb/Ld/LdSumHon.lean); fill_drop, hev_split
(Cb/Ld/LdHideShort.lean); ld_pack_law, ld_pack_place (Cb/Ld/LdSumPackProofs.lean); hidePlace_inj,
hidePlace_lt; vecS_foldOutput_fits (OnBytes/Slice/BlkProxFold.lean); readE_foldClaimRound,
readE_maddE; foldRowFits_agrees (Johnson/Desc/Own/FoldAgree.lean). The library's three lemmas are
called at s.par 0 (OnBytes/Slice/FoldPeel.lean): they read neither its packing, which is 0 there,
nor its weights.

Limits. NOT EVERY TABLE PAIRS: at a table that is no packing on the first h + 2 g + 1 columns there
may be no W, and fold_core, fold_holds and fold_V then say nothing. fold_V serves a sender who lays
these columns as packed does, off the same W that the fold's rounds read: that any sender does so is
not shown here; whether another table pairs with the same W is neither shown nor excluded. That the
fold says yes is not shown here (fold5_yes, Johnson/Prover/Link/FormFoldLaws.lean). That the folded
words are code words: foldWords_enc (FoldEnc.lean). The claim in front is read with the stage's own
numbers of rows (stmG); a stage without a row variable has no fold. Nothing on how W, the free
columns or a tail are chosen. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FoldEnc
import Johnson.Prover.Link.FormFoldLaws
import Johnson.Desc.Own.FoldAgree
import OnBytes.Slice.BlkProxFold
import OnBytes.Slice.BlkFold
import OnBytes.Slice.BlkFoldOut
import Cb.Ld.LdSumHon
import Cb.Ld.LdSumPackProofs
import OnBytes.Slice.FullRecSz

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-! ## 1 The running claim, where two of three coefficients are sent -/

/-- **The verifier's running claim behind k rounds**, from the claim σ: in each round the round
polynomial has the constant and the quadratic coefficient of q's part; its linear coefficient is set
by the round equation (hFill, Cb/Ld/LdHideShort.lean); the next claim is its value at the drawn
element. -/
def runQ : (k : ℕ) → GE → (RIdx (sVars GE 2 k) → GE) → HPt (sVars GE 2 k) → GE
  | 0, σ, _, _ => σ
  | k + 1, σ, q, γ =>
    runQ k (hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) σ
      (fun t : Fin 2 => if t.val = 0 then q (Sum.inl (0 : Fin 3)) else q (Sum.inl (2 : Fin 3))))
      γ.1) (fun i => q (Sum.inr i)) γ.2

/-- **At the round polynomials of a summand the running claim ends in the summand's value at the
drawn point.** General in the summand. -/
theorem runQ_rounds : ∀ (k : ℕ) (f : HPt (sVars GE 2 k) → GE) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)), HRounds (sVars GE 2 k) f q γ →
    runQ k (hSumAll (sVars GE 2 k) f) q γ = f γ
  | 0, _, _, _, _ => rfl
  | k + 1, f, q, γ, h => by
      have e1 : (HVar.plain GE 2).phi (fun t => q (Sum.inl t)) = hSumAll (sVars GE 2 (k + 1)) f :=
        congrArg (HVar.plain GE 2).sum (funext h.1)
      have e2 := fill_drop (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) ((one_mul _).trans mon_one)
        (fun t => q (Sum.inl t))
      have e3 : (fun t : Fin 2 => if t.val = 0 then q (Sum.inl (0 : Fin 3))
          else q (Sum.inl (2 : Fin 3))) =
          fun t : Fin 2 => (fun t => q (Sum.inl t)) ((1 : Fin 3).succAbove t) := by
        funext t
        fin_cases t <;> rfl
      have e4 : hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE))
          ((HVar.plain GE 2).phi fun t => q (Sum.inl t))
          (fun t : Fin 2 => if t.val = 0 then q (Sum.inl (0 : Fin 3))
            else q (Sum.inl (2 : Fin 3))) = fun t => q (Sum.inl t) := by
        rw [e3]
        exact e2
      show runQ k (hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE))
        (hSumAll (sVars GE 2 (k + 1)) f) _) γ.1) (fun i => q (Sum.inr i)) γ.2 = f γ
      rw [← e1, e4, h.1 γ.1]
      exact runQ_rounds k _ _ _ h.2

/-- One round's next claim, with the claim in front set apart. -/
theorem hev_fill (σ : GE) (q' : Fin 2 → GE) (y : GE) :
    hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) σ q') y =
      hev ((1 : Fin 3).insertNth (α := fun _ => GE) 0 q') y +
        y * (σ - (HVar.plain GE 2).phi ((1 : Fin 3).insertNth (α := fun _ => GE) 0 q')) := by
  unfold hFill
  rw [hev_split]
  show _ + y ^ ((1 : Fin 3) : ℕ) • ((1 : GE) • _) = _
  rw [one_smul, smul_eq_mul]
  norm_num
  rfl

/-- Where no drawn element is 0, the running claim behind the rounds tells the claim in front. -/
theorem runQ_inj : ∀ (k : ℕ) (σ σ' : GE) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)), (∀ i, sPt 2 k γ i ≠ 0) → runQ k σ q γ = runQ k σ' q γ → σ = σ'
  | 0, _, _, _, _, _, h => h
  | k + 1, σ, σ', q, γ, hγ, h => by
      have h1 := runQ_inj k _ _ _ γ.2 (fun i => hγ i.succ) h
      rw [hev_fill, hev_fill] at h1
      exact sub_left_injective (mul_left_cancel₀ (hγ 0) (add_left_cancel h1))

/-! ## 2 The fold in the field -/

section Field
variable (s : Sg)

/-- **The fresh table pairs with the polynomial of the coefficients W**: at every point the public
weights (hideW, OnBytes/Slice/FoldPeel.lean), cut at n0, applied to the table folded at the point's
first h coordinates give the polynomial's value (hU, Cb/Ld/LdHide.lean). The library's law of a
packing (PackLaw, Cb/Ld/LdSumPack.lean), said of one table. -/
def Pairs (n0 : ℕ) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (φ : s.cFr.J → GE) : Prop :=
  ∀ γ : HPt (sVars GE 2 (s.h + s.g)), hU (sVars GE 2 (s.h + s.g)) W γ =
    ∑ j : s.cZ.J, hideW s.h s.g n0 (sPt 2 (s.h + s.g) γ) j.val *
      foldV (preP s (sPt 2 (s.h + s.g) γ)) φ j

/-- **The honest round polynomials**, all three coefficients, in closed form: the library's honQ
(Cb/Ld/LdSum.lean) at the stage: v: the claim's coefficients; μ: the stage's message; W: the
polynomial's coefficients; ε: the drawn coefficient. -/
def foldQ (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) : RIdx (sVars GE 2 (s.h + s.g)) → GE :=
  (s.par 0).honQ (μ, fun _ => 0) (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε γ

/-- A round's part does not hang on later draws. -/
theorem foldQ_causal (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE) :
    SCausal 2 (s.h + s.g) (foldQ s v μ W ε) :=
  (s.par 0).honQ_causal (μ, fun _ => 0) (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε

variable (n0 : ℕ) (t0 : GE) (v μ : s.cIn.J → GE) (φ : s.cFr.J → GE)
  (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE) (γ : HPt (sVars GE 2 (s.h + s.g)))

/-- The coefficients behind the fold, applied to the three folded messages, give the summand at the
drawn point. -/
theorem mid_at (hP : Pairs s n0 W φ) :
    ∑ j, midVec s n0 v ε (sPt 2 (s.h + s.g) γ) j * foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j =
      (s.par 0).summand (μ, fun _ => 0) (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε γ := by
  refine (Fintype.sum_sum_type _).trans ?_
  refine (congrArg₂ (· + ·) rfl (Fintype.sum_sum_type _)).trans ?_
  unfold SumPar.summand
  rw [hP γ]
  generalize sPt 2 (s.h + s.g) γ = z
  have b1 : ∑ c : s.cM.J, (∑ b, v (.inl (b, c)) * Alg.eqk z b) * ε *
        foldV z (fun x => μ (.inl x)) c =
      ε * ∑ c : s.cM.J, (∑ b, v (.inl (b, c)) * Alg.eqk z b) * foldV z (fun x => μ (.inl x)) c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have b2 : ∑ c : s.cZ.J, (∑ b, v (.inr (b, c)) * Alg.eqk (preP s z) b) *
        (ε * ∏ t : Fin s.g, z (Fin.natAdd s.h t)) * foldV (preP s z) (fun x => μ (.inr x)) c =
      ε * ((∑ c : s.cZ.J, (∑ b, v (.inr (b, c)) * Alg.eqk (preP s z) b) *
        foldV (preP s z) (fun x => μ (.inr x)) c) * ∏ t : Fin s.g, z (Fin.natAdd s.h t)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have b3 : ∑ c : s.cZ.J, midVec s n0 v ε z (.inr (.inr c)) * foldMsg s μ φ z (.inr (.inr c)) =
      ∑ j : s.cZ.J, hideW s.h s.g n0 z j.val * foldV (preP s z) φ j := rfl
  refine (congrArg₂ (· + ·) b1 (congrArg₂ (· + ·) b2 b3)).trans ?_
  show _ = (∑ j : s.cZ.J, hideW s.h s.g n0 z j.val * foldV (preP s z) φ j) +
    ε * ((∑ c : s.cM.J, (∑ b, v (.inl (b, c)) * Alg.eqk z b) * foldV z (fun x => μ (.inl x)) c) +
      (∑ c : s.cZ.J, (∑ b, v (.inr (b, c)) * Alg.eqk (preP s z) b) *
        foldV (preP s z) (fun x => μ (.inr x)) c) * ∏ t : Fin s.g, z (Fin.natAdd s.h t))
  ring

/-- The running claim at the honest rounds, from the polynomial's sum and the claim in front, ends
in the summand at the drawn point: honQ_rounds, summand_sum (Cb/Ld/LdSumHon.lean). -/
theorem fold_claim (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (t0, v) μ) :
    runQ (s.h + s.g) (hMu (sVars GE 2 (s.h + s.g)) W + ε * t0) (foldQ s v μ W ε γ) γ =
      (s.par 0).summand (μ, fun _ => 0) (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε γ := by
  have h1 := (s.par 0).honQ_rounds (le_refl 2) (μ, fun _ => 0)
    (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε γ
  have h2 := (s.par 0).summand_sum (le_refl 2) (μ, fun _ => 0)
    (0, (fun x => v (.inl x), fun x => v (.inr x))) W ε
  have h3 : ∑ j, (s.par 0).slIn (fun x => v (.inl x), fun x => v (.inr x)) j * μ j = t0 := by
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hin
    rcases j with j | j <;> rfl
  have h4 := runQ_rounds _ _ _ _ h1
  rw [h2, h3, mul_comm t0 ε] at h4
  exact h4

/-- **THE CORE: BEHIND A FOLD THE CLAIM IS TRUE AT THE THREE FOLDED MESSAGES**: at every drawn
coefficient and every drawn point. -/
theorem fold_core (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (t0, v) μ)
    (hP : Pairs s n0 W φ) :
    (Slf.idf (E := GE) (J := s.cMid.J)).Holds
      (runQ (s.h + s.g) (hMu (sVars GE 2 (s.h + s.g)) W + ε * t0) (foldQ s v μ W ε γ) γ,
        midVec s n0 v ε (sPt 2 (s.h + s.g) γ)) (foldMsg s μ φ (sPt 2 (s.h + s.g) γ)) :=
  (mid_at s n0 v μ φ W ε γ hP).trans (fold_claim s t0 v μ W ε γ hin).symm

/-- **A test that can fail**: with another first scalar, and no drawn element 0, the claim behind is
false at the three folded messages. -/
theorem fold_turned (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (t0, v) μ)
    (hP : Pairs s n0 W φ) (σ' : GE) (hne : σ' ≠ hMu (sVars GE 2 (s.h + s.g)) W)
    (hγ : ∀ i, sPt 2 (s.h + s.g) γ i ≠ 0) :
    ¬ (Slf.idf (E := GE) (J := s.cMid.J)).Holds
      (runQ (s.h + s.g) (σ' + ε * t0) (foldQ s v μ W ε γ) γ,
        midVec s n0 v ε (sPt 2 (s.h + s.g) γ)) (foldMsg s μ φ (sPt 2 (s.h + s.g) γ)) := fun hbad =>
  hne (add_right_cancel (runQ_inj _ _ _ _ γ hγ
    (hbad.symm.trans (fold_core s n0 t0 v μ φ W ε γ hin hP))))

/-- From the column h + 2 g + 1 on the weights are 0. -/
theorem hideW_off (z : Fin (s.h + s.g) → GE) (j : ℕ) (hj : s.h + 2 * s.g + 1 ≤ j) :
    hideW s.h s.g n0 z j = 0 := by
  unfold hideW
  split
  · unfold QwAt placeV
    exact Finset.sum_eq_zero fun c _ =>
      if_neg (ne_of_lt (lt_of_lt_of_le (hidePlace_lt s.h s.g c) hj))
  · rfl

/-- **The columns from h + 2 g + 1 on are free**: the pairing is kept under adding a table that is 0
on the columns before. -/
theorem Pairs.add_free (hP : Pairs s n0 W φ) (fr : s.cFr.J → GE)
    (h0 : ∀ b (j : s.cZ.J), j.val < s.h + 2 * s.g + 1 → fr (b, j) = 0) :
    Pairs s n0 W fun x => φ x + fr x := fun γ => by
  rw [hP γ]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.val < s.h + 2 * s.g + 1
  · congr 1
    unfold foldV
    refine Finset.sum_congr rfl fun b _ => ?_
    show _ = _ * (φ (b, j) + fr (b, j))
    rw [h0 b j hj, add_zero]
  · rw [hideW_off s n0 _ _ (not_lt.1 hj), zero_mul, zero_mul]

end Field

/-! ## 3 The pairing at the library's packing -/

section Pack
variable (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)

/-- The place of a column of the library's packing among the coordinates of a row's message. -/
def placeF : PCol s.h s.g 1 → s.cZ.J := fun c =>
  ⟨hidePlace s.h s.g c, lt_of_lt_of_le (hidePlace_lt s.h s.g c) hl⟩

/-- **The library's packing of the coefficients W** (pkC, Cb/Ld/LdSumPack.lean), laid at these
places; 0 elsewhere. -/
def packed (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) : s.cFr.J → GE :=
  pkAt (placeF s hl) (pkC s.h s.g 1) W

theorem placeF_inj : Function.Injective (placeF s hl) := fun _ _ e =>
  hidePlace_inj s.h s.g (congrArg Fin.val e)

/-- The weights, at a coordinate of a row's message. -/
theorem hideW_place (z : Fin (s.h + s.g) → GE) (j : s.cZ.J) :
    hideW s.h s.g s.Z.l z j.val = QwAt (placeF s hl) (QwC s.h s.g 1) z j := by
  unfold hideW
  rw [if_pos j.isLt]
  unfold QwAt placeV
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases e : hidePlace s.h s.g c = j.val
  · rw [if_pos e, if_pos (Fin.ext e)]
  · rw [if_neg e, if_neg fun e' => e (congrArg Fin.val e')]

/-- **The packing pairs**: ld_pack_law, ld_pack_place (Cb/Ld/LdSumPackProofs.lean). -/
theorem pairs_packed (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) :
    Pairs s s.Z.l W (packed s hl W) := fun γ => by
  have h := ld_pack_place GE s.h s.g 2 (PCol s.h s.g 1) s.cZ.J (placeF s hl) (pkC s.h s.g 1)
    (QwC s.h s.g 1) (placeF_inj s hl) (ld_pack_law GE s.h s.g 1) W γ
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [hideW_place s hl]
  rfl

/-- **At the four folding stages of the full size there is room for the packing.** -/
theorem fr_room : (frSg1.h + 2 * frSg1.g + 1 ≤ frSg1.Z.l ∧ frSg2.h + 2 * frSg2.g + 1 ≤ frSg2.Z.l) ∧
    frSg3.h + 2 * frSg3.g + 1 ≤ frSg3.Z.l ∧ frSg4.h + 2 * frSg4.g + 1 ≤ frSg4.Z.l := by
  decide

end Pack

/-! ## 4 At the description's own letters -/

/-- **The rounds "FOLD round" show q's constant and quadratic coefficients and draw γ.** A list
whose length is not k: False. Inside a round nothing is refused: the two sent elements are read by
getD 0 | getD 1 at zeroE, the drawn one by drawnOf (headD at (0, 0, 0)): a round that sends or draws
too little reads as zeros. -/
def Shows : (k : ℕ) → List Fmt.RoundView → (RIdx (sVars GE 2 k) → GE) → HPt (sVars GE 2 k) → Prop
  | 0, [], _, _ => True
  | k + 1, r :: rs, q, γ =>
    readE ((sentOf r).getD 0 zeroE) = q (Sum.inl (0 : Fin 3)) ∧
      readE ((sentOf r).getD 1 zeroE) = q (Sum.inl (2 : Fin 3)) ∧
      readE (drawnOf r) = γ.1 ∧ Shows k rs (fun i => q (Sum.inr i)) γ.2
  | 0, _ :: _, _, _ => False
  | _ + 1, [], _, _ => False

/-- The description's running claim (claimOf, Johnson/Prover/Link/FormFold.lean), read in the field,
is runQ; the drawn elements are the point: readE_foldClaimRound (OnBytes/Slice/BlkFold.lean). -/
theorem claimOf_shows : ∀ (k : ℕ) (rs : List Fmt.RoundView) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)) (c : E), Shows k rs q γ →
    readE (claimOf rs c) = runQ k (readE c) q γ ∧ readP k (rs.map drawnOf) = sPt 2 k γ ∧
      rs.length = k
  | 0, [], _, _, _, _ => ⟨rfl, funext fun i => i.elim0, rfl⟩
  | k + 1, r :: rs, q, γ, c, h => by
      obtain ⟨h0, h2, hg, hr⟩ := h
      obtain ⟨i1, i2, i3⟩ := claimOf_shows k rs _ γ.2 (claimStep c r) hr
      refine ⟨?_, ?_, congrArg (· + 1) i3⟩
      · rw [claimOf_cons]
        unfold claimStep at i1
        rw [i1, readE_foldClaimRound, h0, h2, hg]
        rfl
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hg
        · exact congrFun i2 j
  | 0, _ :: _, _, _, _, h => h.elim
  | _ + 1, [], _, _, _, h => h.elim

/-- What a written round shows, read back. -/
theorem sent_written (r : Fmt.RoundView) (a b : GE) (h : r.vals = [.e (ofE a), .e (ofE b)]) :
    readE ((sentOf r).getD 0 zeroE) = a ∧ readE ((sentOf r).getD 1 zeroE) = b := by
  unfold sentOf
  rw [h]
  exact ⟨(readE_ofTriple _).trans (toE_ofE a), (readE_ofTriple _).trans (toE_ofE b)⟩

theorem sent_written_one (r : Fmt.RoundView) (a : GE) (h : r.vals = [.e (ofE a)]) :
    readE ((sentOf r).getD 0 zeroE) = a := by
  unfold sentOf
  rw [h]
  exact (readE_ofTriple _).trans (toE_ofE a)

section AtD
variable (s : Sg) (μ : s.cIn.J → GE) (φ : s.cFr.J → GE)
  (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (γ : HPt (sVars GE 2 (s.h + s.g)))

/-- **THE SINGLE ROWS THAT THE DESCRIPTION's FOLD RETURNS ARE TRUE AT THE THREE FOLDED MESSAGES.**
rE: the round "FOLD epsilon"; rR: the rounds "FOLD round". -/
theorem fold_holds (S : Statement) (F : FoldShape) (row : GroupRow) (id : ℕ) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hok : foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = s.Z.l)
    (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) μ) (hP : Pairs s s.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR (foldQ s (vecG s row) μ W (readE (drawnOf rE)) γ) γ) :
    (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s (foldOutAt S F row id (rE :: rR)))
      (foldMsg s μ φ (sPt 2 (s.h + s.g) γ)) := by
  obtain ⟨i1, i2, i3⟩ := claimOf_shows _ rR _ γ
    (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target) hR
  have hv := ProxRun.vecS_foldOutput_fits s (spent S id) F row id (drawnOf rE) (rR.map drawnOf)
    (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) hk hh
    (by rw [List.length_map, i3]) hok hZ
  have hc := fold_core s s.Z.l (readE row.target) (vecG s row) μ φ W (readE (drawnOf rE)) γ hin hP
  show ∑ j, vecS s (foldOutput (spent S id) F row id (drawnOf rE) (rR.map drawnOf)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))) j *
        foldMsg s μ φ (sPt 2 (s.h + s.g) γ) j =
    readE (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
  rw [hv, i2, i1, readE_maddE, hσ]
  exact hc

/-- **The same at the record behind the fold** (foldOut | foldT, Johnson/Prover/Link/FormFold.lean),
from the record in front (FoldFront). -/
theorem fold_V {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow} {L : GroupLayout}
    {c : IoppStage} {n : ℕ × ℕ} {id : ℕ} (H : FoldFront p j cur t row L c n id) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : c.k = s.h + s.g) (hh : c.h = s.h)
    (hZ : (t.st.codes.mask.getD c.maskCode default).ell = s.Z.l)
    (hin : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) μ) (hP : Pairs s s.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR (foldQ s (vecG s row) μ W (readE (drawnOf rE)) γ) γ) :
    (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s (foldOut t row L c id (rE :: rR)))
      (foldMsg s μ φ (sPt 2 (s.h + s.g) γ)) :=
  fold_holds s μ φ W γ t.st (ioppFoldShape c L) row id rE rR hk hh
    (by rw [Own.foldRowFits_agrees, foldRowFits_spent]; exact H.rowFits) hZ hin hP hσ hR

end AtD

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.runQ_rounds
#print axioms Johnson.Prover.Link.hev_fill
#print axioms Johnson.Prover.Link.runQ_inj
#print axioms Johnson.Prover.Link.foldQ_causal
#print axioms Johnson.Prover.Link.mid_at
#print axioms Johnson.Prover.Link.fold_claim
#print axioms Johnson.Prover.Link.fold_core
#print axioms Johnson.Prover.Link.fold_turned
#print axioms Johnson.Prover.Link.hideW_off
#print axioms Johnson.Prover.Link.Pairs.add_free
#print axioms Johnson.Prover.Link.placeF_inj
#print axioms Johnson.Prover.Link.hideW_place
#print axioms Johnson.Prover.Link.pairs_packed
#print axioms Johnson.Prover.Link.fr_room
#print axioms Johnson.Prover.Link.claimOf_shows
#print axioms Johnson.Prover.Link.sent_written
#print axioms Johnson.Prover.Link.sent_written_one
#print axioms Johnson.Prover.Link.fold_holds
#print axioms Johnson.Prover.Link.fold_V
