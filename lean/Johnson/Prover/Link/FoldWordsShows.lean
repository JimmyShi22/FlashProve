-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldWordsShows.lean: THE FOLD's PROVER ON WORDS, READ IN THE FIELD: SECOND PART:
THE LAW: the words of foldSigmaE and foldRoundE (Johnson/Prover/Link/FoldWordsE.lean) read as the
field's hMu and foldQK (FoldHolds.lean, FoldKept.lean): the two premises on what is sent of
fold_holds_kept.

Main names (namespace Johnson.Prover.Link).
  toE_sumPoly   the library's word summand reads as the library's field summand at a stage, UNDER
      THE NAMED PREMISE FoldSizes.
  roundPart_add_mul, roundPart_keptQ   the parts of a sum; the kept forms' term: the constant is the
      value times (1 - g) over the sampled elements in front; the quadratic coefficient is 0.
  round_words   one "FOLD round"'s two words, on the format's triples.
  shows_of_parts   from the rounds' parts to Shows.
  sigma_readsE   L1: readE (foldSigmaE k w) is hMu at w's coefficients.
  rounds_show   L2: rounds that send foldRoundE's words show foldQK, at the point that their sampled
      elements read as.
  fold_holds_words   THE LAW, SPENT: fold_holds_kept with its two premises on what is sent paid by
      L1 and L2.

THE LETTERS OF THE LAW. The coefficients: coefU k (uOfBook k w). The row's coefficients and the
tables: the library's vecIn (OnBytes/Slice/Stage.lean) at the arrays c, d and at m, mu: entry p of
row b at the index b + 2^n p. The kept forms' value: readE keptV.

By calls: honQ_rounds (Cb/Ld/LdSumHon.lean); roundPoly_reads, coeffs_read, toE_dot_fold,
toE_hidePoly, sigma_reads (FoldWordsLaw.lean); toE_tailProd_late (OnBytes/Slice/SimFold.lean);
lst_take (SimBasic.lean).

Limits. STILL THE CALLER's: that vecIn at c, d is the claim's own vector of coefficients (vecG) and
vecIn at m, mu the stage's message; that the table of the coefficients is made of uOfBook k w at the
same w (Pairs); FoldSizes; that the rounds send these words. No run of a prover is shown to send
them. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldWordsLaw
import Johnson.Prover.Link.FoldWordsE
import Johnson.Prover.Link.FoldKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Slice Cb
open Fmt.M1 (dot foldLow tailProd)
open Fmt.M1.FoldOwn (Hide Trial sumPoly roundAt coeffs hidePoly cube)

section Field
variable (s : Sg)

/-- The point of a list of words, coordinate by coordinate. -/
theorem sPt_lst (k : ℕ) (xs : List Fmt.M1.E) :
    sPt 2 k (ptK k (lst xs)) = fun t : Fin k => lst xs t.val :=
  funext fun t => sPt_ptK k (lst xs) t

/-- **THE WORD SUMMAND READS AS THE LIBRARY's**, under the named premise on the sizes. -/
theorem toE_sumPoly (c d m mu : Array Fmt.M1.E) (w : Fin (2 * (s.h + s.g) + 1) → Fmt.M1.E)
    (eps : Fmt.M1.E) (hs : FoldSizes (s.h + s.g) s.h s.C.l s.Z.l c d m mu) (xs : List Fmt.M1.E)
    (hx : xs.length = s.h + s.g) :
    toE (sumPoly .two (trialW (s.h + s.g) s.h c d m mu w eps) xs) =
      (s.par 0).summand (vecIn s ⟨m, mu, Fmt.Fld.zeroE⟩, fun _ => 0)
        (0, (fun x => vecIn s ⟨c, d, Fmt.Fld.zeroE⟩ (.inl x),
          fun x => vecIn s ⟨c, d, Fmt.Fld.zeroE⟩ (.inr x)))
        (coefU (s.h + s.g) (uOfBook (s.h + s.g) w)) (toE eps) (ptK (s.h + s.g) (lst xs)) := by
  have e1 : xs.take (s.h + s.g) = xs := by rw [← hx]; exact List.take_length
  have e2 : (xs.take s.h).length = s.h := by rw [List.length_take, hx]; omega
  unfold SumPar.summand
  rw [sPt_lst]
  show toE (Fmt.Fld.two.addE (hidePoly .two (s.h + s.g) (uOfBook (s.h + s.g) w) xs)
    (Fmt.Fld.two.mulE eps (Fmt.Fld.two.addE
      (dot .two (foldLow .two (xs.take (s.h + s.g)) c) (foldLow .two (xs.take (s.h + s.g)) m))
      (Fmt.Fld.two.mulE (dot .two (foldLow .two (xs.take s.h) d) (foldLow .two (xs.take s.h) mu))
        (tailProd .two (xs.take (s.h + s.g)) s.h))))) = _
  rw [e1, toE_addE, toE_mulE, toE_addE, toE_mulE, toE_hidePoly _ _ _ hx,
    toE_dot_fold (s.h + s.g) s.C.l xs hx c m hs.1,
    toE_dot_fold s.h s.Z.l (xs.take s.h) e2 d mu hs.2.2.1]
  have e3 := toE_tailProd_late s.h s.g xs hx 0
  rw [Nat.add_zero] at e3
  rw [e3]
  have e4 : (fun t : Fin s.h => lst (xs.take s.h) t.val) =
      preP s (fun t : Fin (s.h + s.g) => lst xs t.val) :=
    funext fun t => lst_take s.h xs t.val t.isLt
  rw [e4]
  simp only [Nat.zero_le, if_true]
  rfl

/-! ## 2 The parts of a sum; the kept term's parts -/

theorem roundPart_add_mul (ε : GE) : ∀ (k : ℕ) (a b : RIdx (sVars GE 2 k) → GE) (i : ℕ) (t : Fin 3),
    roundPart k (fun j => a j + ε * b j) i t = roundPart k a i t + ε * roundPart k b i t
  | 0, _, _, _, _ => by
      show (0 : GE) = 0 + ε * 0
      ring
  | _ + 1, _, _, 0, _ => rfl
  | k + 1, a, b, i + 1, t => roundPart_add_mul ε k (fun j => a (.inr j)) (fun j => b (.inr j)) i t

/-- The kept term's part in the round behind the sampled words gs: the constant is a times
(1 - g) over all g of gs; the quadratic coefficient is 0. -/
theorem roundPart_keptQ : ∀ (k : ℕ) (a : GE) (γ : HPt (sVars GE 2 k)) (gs : List Fmt.M1.E),
    gs.length < k → ReadsTo k gs γ →
    roundPart k (keptQ k a γ) gs.length 0 = gs.foldl (fun x g => x * (1 - toE g)) a ∧
      roundPart k (keptQ k a γ) gs.length 2 = 0
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, _, [], _, _ => ⟨rfl, rfl⟩
  | k + 1, a, γ, g :: gs, hl, hr => by
      have ih := roundPart_keptQ k (a * (1 - γ.1)) γ.2 gs (Nat.lt_of_succ_lt_succ hl) hr.2
      show roundPart k (keptQ k (a * (1 - γ.1)) γ.2) gs.length 0 =
          gs.foldl (fun x g => x * (1 - toE g)) (a * (1 - toE g)) ∧
        roundPart k (keptQ k (a * (1 - γ.1)) γ.2) gs.length 2 = 0
      rw [hr.1]
      exact ih

theorem toE_foldl_mul (gs : List Fmt.M1.E) : ∀ a : Fmt.M1.E,
    toE (gs.foldl (fun x g => Fmt.Fld.two.mulE x (Fmt.Fld.two.subE Fmt.Fld.oneE g)) a) =
      gs.foldl (fun x g => x * (1 - toE g)) (toE a) := by
  induction gs with
  | nil => intro a; rfl
  | cons g gs ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ih, toE_mulE, toE_subE, toE_oneE]

/-! ## 3 One round's two words -/

/-- **A "FOLD round"'s two words read as the constant and the quadratic coefficient of the field's
round polynomial**, the kept forms' term with them: in the round behind the sampled words gs. -/
theorem round_words (c d m mu : Array Fmt.M1.E) (keptV : Fmt.M1.E)
    (w : Fin (2 * (s.h + s.g) + 1) → Fmt.M1.E) (eps : Fmt.M1.E)
    (hs : FoldSizes (s.h + s.g) s.h s.C.l s.Z.l c d m mu) (γ : HPt (sVars GE 2 (s.h + s.g)))
    (gs : List Fmt.M1.E) (hl : gs.length < s.h + s.g) (hr : ReadsTo (s.h + s.g) gs γ) :
    toE (foldRoundW (s.h + s.g) s.h c d m mu keptV w eps gs).1 =
        roundPart (s.h + s.g) (foldQK s (vecIn s ⟨c, d, Fmt.Fld.zeroE⟩)
          (vecIn s ⟨m, mu, Fmt.Fld.zeroE⟩) (coefU (s.h + s.g) (uOfBook (s.h + s.g) w)) (toE eps)
          (toE keptV) γ) gs.length 0 ∧
      toE (foldRoundW (s.h + s.g) s.h c d m mu keptV w eps gs).2 =
        roundPart (s.h + s.g) (foldQK s (vecIn s ⟨c, d, Fmt.Fld.zeroE⟩)
          (vecIn s ⟨m, mu, Fmt.Fld.zeroE⟩) (coefU (s.h + s.g) (uOfBook (s.h + s.g) w)) (toE eps)
          (toE keptV) γ) gs.length 2 := by
  have H := (s.par 0).honQ_rounds (le_refl 2) (vecIn s ⟨m, mu, Fmt.Fld.zeroE⟩, fun _ => 0)
    (0, (fun x => vecIn s ⟨c, d, Fmt.Fld.zeroE⟩ (.inl x),
      fun x => vecIn s ⟨c, d, Fmt.Fld.zeroE⟩ (.inr x)))
    (coefU (s.h + s.g) (uOfBook (s.h + s.g) w)) (toE eps) γ
  have R := fun X => roundPoly_reads (s.h + s.g) _ _ γ H
    (sumPoly .two (trialW (s.h + s.g) s.h c d m mu w eps))
    (fun xs hx => toE_sumPoly s c d m mu w eps hs xs hx) gs X hl hr
  have C := coeffs_read _ _ _ _
    ((R Fmt.Fld.zeroE).trans (by rw [toE_zeroE]))
    ((R Fmt.Fld.oneE).trans (by rw [toE_oneE]))
    ((R (Fmt.Fld.two.negE Fmt.Fld.oneE)).trans (by rw [toE_negE, toE_oneE]))
  obtain ⟨K0, K2⟩ := roundPart_keptQ (s.h + s.g) (toE keptV) γ gs hl hr
  unfold foldQK
  rw [roundPart_add_mul, roundPart_add_mul, K0, K2, mul_zero, add_zero]
  constructor
  · show toE (Fmt.Fld.two.addE _ (Fmt.Fld.two.mulE eps _)) = _
    rw [toE_addE, toE_mulE, toE_foldl_mul]
    exact congrArg (· + _) C.1
  · exact C.2

end Field

/-! ## 4 From the rounds' parts to "Shows" -/

theorem readsTo_nil : ∀ (k : ℕ) (γ : HPt (sVars GE 2 k)), ReadsTo k [] γ
  | 0, _ => trivial
  | _ + 1, _ => trivial

theorem readsTo_take : ∀ (k : ℕ) (l : List Fmt.M1.E) (γ : HPt (sVars GE 2 k)) (i : ℕ),
    ReadsTo k l γ → ReadsTo k (l.take i) γ
  | k, [], γ, _, _ => by rw [List.take_nil]; exact readsTo_nil k γ
  | k, _ :: _, γ, 0, _ => readsTo_nil k γ
  | 0, _ :: _, _, _ + 1, h => h.elim
  | k + 1, _ :: l, γ, i + 1, h => ⟨h.1, readsTo_take k l γ.2 i h.2⟩

theorem readsTo_ptK : ∀ (k : ℕ) (l : List Fmt.M1.E), l.length ≤ k → ReadsTo k l (ptK k (lst l))
  | k, [], _ => readsTo_nil k _
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | k + 1, _ :: l, h => ⟨rfl, readsTo_ptK k l (Nat.le_of_succ_le_succ h)⟩

/-- **Rounds whose two sent elements read as the parts' constant and quadratic coefficients, and
whose sampled elements read as the point, show the round polynomials** (Shows,
Johnson/Prover/Link/FoldHolds.lean). -/
theorem shows_of_parts : ∀ (k : ℕ) (rR : List Fmt.RoundView) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)), rR.length = k →
    (∀ i (h : i < rR.length), readE ((sentOf rR[i]).getD 0 OnBytes.zeroE) = roundPart k q i 0 ∧
      readE ((sentOf rR[i]).getD 1 OnBytes.zeroE) = roundPart k q i 2) →
    ReadsTo k ((rR.map drawnOf).map (·.triple)) γ → Shows k rR q γ
  | 0, [], _, _, _, _, _ => trivial
  | k + 1, r :: rs, q, γ, hl, hp, hr =>
      ⟨(hp 0 (Nat.succ_pos _)).1, (hp 0 (Nat.succ_pos _)).2, hr.1,
        shows_of_parts k rs (fun j => q (.inr j)) γ.2 (Nat.succ.inj hl)
          (fun i h => hp (i + 1) (Nat.succ_lt_succ h)) hr.2⟩

/-! ## 5 The law, at the program's own elements -/

/-- **L1: WHAT "FOLD epsilon" SENDS READS AS THE FIELD's hMu.** -/
theorem sigma_readsE (k : ℕ) (w : Fin (2 * k + 1) → OnBytes.E) :
    readE (foldSigmaE k w) = hMu (sVars GE 2 k) (coefU k (uOfBook k fun i => (w i).triple)) :=
  sigma_reads k fun i => (w i).triple

/-- **L2: ROUNDS THAT SEND foldRoundE's WORDS SHOW THE FIELD's ROUND POLYNOMIALS foldQK**, under the
named premise on the sizes: at the point that the rounds' sampled elements read as. -/
theorem rounds_show (s : Sg) (c d m mu : Array OnBytes.E) (keptV : OnBytes.E)
    (w : Fin (2 * (s.h + s.g) + 1) → OnBytes.E) (eps : OnBytes.E)
    (hs : FoldSizes (s.h + s.g) s.h s.C.l s.Z.l (c.map (·.triple)) (d.map (·.triple))
      (m.map (·.triple)) (mu.map (·.triple)))
    (rR : List Fmt.RoundView) (hl : rR.length = s.h + s.g)
    (hq : ∀ i (h : i < rR.length),
      (sentOf rR[i]).getD 0 OnBytes.zeroE =
          (foldRoundE (s.h + s.g) s.h c d m mu keptV w eps ((rR.take i).map drawnOf)).1 ∧
        (sentOf rR[i]).getD 1 OnBytes.zeroE =
          (foldRoundE (s.h + s.g) s.h c d m mu keptV w eps ((rR.take i).map drawnOf)).2) :
    Shows (s.h + s.g) rR
      (foldQK s (vecIn s ⟨c.map (·.triple), d.map (·.triple), Fmt.Fld.zeroE⟩)
        (vecIn s ⟨m.map (·.triple), mu.map (·.triple), Fmt.Fld.zeroE⟩)
        (coefU (s.h + s.g) (uOfBook (s.h + s.g) fun i => (w i).triple)) (readE eps) (readE keptV)
        (ptK (s.h + s.g) (lst ((rR.map drawnOf).map (·.triple)))))
      (ptK (s.h + s.g) (lst ((rR.map drawnOf).map (·.triple)))) := by
  have hr := readsTo_ptK (s.h + s.g) ((rR.map drawnOf).map (·.triple))
    (by rw [List.length_map, List.length_map, hl])
  refine shows_of_parts _ rR _ _ hl (fun i h => ?_) hr
  have e : ((rR.take i).map drawnOf).map (·.triple) = ((rR.map drawnOf).map (·.triple)).take i := by
    rw [List.map_take, List.map_take]
  have hi : (((rR.map drawnOf).map (·.triple)).take i).length = i := by
    rw [List.length_take, List.length_map, List.length_map]
    omega
  have R := round_words s (c.map (·.triple)) (d.map (·.triple)) (m.map (·.triple))
    (mu.map (·.triple)) keptV.triple (fun i => (w i).triple) eps.triple hs _
    (((rR.map drawnOf).map (·.triple)).take i) (by rw [hi, ← hl]; exact h)
    (readsTo_take _ _ _ i hr)
  rw [hi] at R
  rw [(hq i h).1, (hq i h).2]
  unfold foldRoundE
  rw [e]
  exact R

/-! ## 6 The law, spent -/

/-- **THE SINGLE ROWS THAT THE DESCRIPTION's FOLD RETURNS ARE TRUE WHERE THE ROUNDS SEND THESE
WORDS**: fold_holds_kept (Johnson/Prover/Link/FoldKept.lean) with its two premises on what is sent
paid by sigma_readsE and rounds_show. The caller's ties stay premises: hv, hV, hin, hP, hs. -/
theorem fold_holds_words (s : Sg) (φ : s.cFr.J → GE) (N : ℕ → ℕ) (κ : ℕ → ℕ → GE)
    (S : OnBytes.Statement) (F : OnBytes.FoldShape) (row : OnBytes.GroupRow) (id : ℕ) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hok : OnBytes.foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = s.Z.l)
    (c d m mu : Array OnBytes.E) (keptV : OnBytes.E) (w : Fin (2 * (s.h + s.g) + 1) → OnBytes.E)
    (hs : FoldSizes (s.h + s.g) s.h s.C.l s.Z.l (c.map (·.triple)) (d.map (·.triple))
      (m.map (·.triple)) (mu.map (·.triple)))
    (hv : vecG s row = vecIn s ⟨c.map (·.triple), d.map (·.triple), Fmt.Fld.zeroE⟩)
    (hV : keptVal N κ row.kept = readE keptV)
    (hin : ∑ j, vecG s row j * vecIn s ⟨m.map (·.triple), mu.map (·.triple), Fmt.Fld.zeroE⟩ j +
      keptVal N κ row.kept = readE row.target)
    (hP : Pairs s s.Z.l (coefU (s.h + s.g) (uOfBook (s.h + s.g) fun i => (w i).triple)) φ)
    (hσ : (sentOf rE).getD 0 OnBytes.zeroE = foldSigmaE (s.h + s.g) w)
    (hl : rR.length = s.h + s.g)
    (hq : ∀ i (h : i < rR.length),
      (sentOf rR[i]).getD 0 OnBytes.zeroE = (foldRoundE (s.h + s.g) s.h c d m mu keptV w
          (drawnOf rE) ((rR.take i).map drawnOf)).1 ∧
        (sentOf rR[i]).getD 1 OnBytes.zeroE = (foldRoundE (s.h + s.g) s.h c d m mu keptV w
          (drawnOf rE) ((rR.take i).map drawnOf)).2) :
    ∑ j, vecS s (foldOutAt S F row id (rE :: rR)) j *
          foldMsg s (vecIn s ⟨m.map (·.triple), mu.map (·.triple), Fmt.Fld.zeroE⟩) φ
            (sPt 2 (s.h + s.g) (ptK (s.h + s.g) (lst ((rR.map drawnOf).map (·.triple))))) j +
        keptVal N κ (foldOutAt S F row id (rE :: rR)).kept =
      readE (foldOutAt S F row id (rE :: rR)).target := by
  refine fold_holds_kept s _ φ _ _ N κ S F row id rE rR hk hh hok hZ hin hP ?_ ?_
  · rw [hσ]
    exact sigma_readsE _ w
  · rw [hv, hV]
    exact rounds_show s c d m mu keptV w (drawnOf rE) hs rR hl hq

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.sPt_lst
#print axioms Johnson.Prover.Link.toE_sumPoly
#print axioms Johnson.Prover.Link.roundPart_add_mul
#print axioms Johnson.Prover.Link.roundPart_keptQ
#print axioms Johnson.Prover.Link.toE_foldl_mul
#print axioms Johnson.Prover.Link.round_words
#print axioms Johnson.Prover.Link.readsTo_nil
#print axioms Johnson.Prover.Link.readsTo_take
#print axioms Johnson.Prover.Link.readsTo_ptK
#print axioms Johnson.Prover.Link.shows_of_parts
#print axioms Johnson.Prover.Link.sigma_readsE
#print axioms Johnson.Prover.Link.rounds_show
#print axioms Johnson.Prover.Link.fold_holds_words
