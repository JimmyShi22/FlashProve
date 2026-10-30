-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByFold.lean: proof of `Spec.fold_eq` (RunBySpec.lean). The
rounds of a fold computed on words (`Trial.sigma`, `FoldOwn.honest`, Fmt/M1Fold.lean) are the rounds
defined over the field (`foldShown`, Johnson/Desc/K12/Honest/Fold.lean).

  `foldBy_eq`    the proof of `Spec.fold_eq`
  `fold_core`    the same for a stage given as `Sg`, with the four array sizes as one hypothesis
  `toE_headE`    the first element that a round sampled (`headE`, RunBy.lean) decodes to `drawnE`

By what. Each round sends two elements. Their words are below the prime (`ok_foldl_add`,
HalveLaw.lean; `okE_subE`, RunByTab.lean), and they decode to the field's coefficients
(`roundPoly_reads`, `coeffs_read`, Johnson/Prover/Link/FoldWordsLaw.lean). So they are these,
encoded (`eq_ofE`, RunByTab.lean).

Limits. Two definitions give the same words. Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import Johnson.Desc.ProofFile.Honest.K12.HalveLaw
import Johnson.Prover.Link.FoldWordsShows
import Johnson.Prover.Link.BodyCausal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice Cb
open Johnson.Prover.Link
open Fmt.M1 (Stage GRow dot foldLow tailProd)
open Fmt.M1.FoldOwn (Hide Trial sumPoly roundAt coeffs hidePoly cube honest)
open Fmt.M1.Own (PSt tabOf)
open H2K.Pub (sgOf)

/-! ## 1 What a round's elements decode to -/

section Field
variable (σ : Sg)

/-- `sumPoly` on words decodes to the sumcheck's summand over the field, for any structure U
(`Hide`) of the hiding polynomial's coefficients. `toE_sumPoly`
(Johnson/Prover/Link/FoldWordsShows.lean) states the same for those made by `uOfBook`. -/
theorem toE_sumPolyU (c d m mu : Array Fmt.M1.E) (t : Fmt.M1.E) (U : Hide) (eps : Fmt.M1.E)
    (g : List Fmt.M1.E) (lzk : ℕ) (hs : FoldSizes (σ.h + σ.g) σ.h σ.C.l σ.Z.l c d m mu)
    (xs : List Fmt.M1.E) (hx : xs.length = σ.h + σ.g) :
    toE (sumPoly .two
        { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U, eps := eps, g := g
          lzk := lzk } xs) =
      (σ.par 0).summand (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩, fun _ => 0)
        (0, (fun x => vecIn σ ⟨c, d, t⟩ (.inl x), fun x => vecIn σ ⟨c, d, t⟩ (.inr x)))
        (coefU (σ.h + σ.g) U) (toE eps) (ptK (σ.h + σ.g) (lst xs)) := by
  have e1 : xs.take (σ.h + σ.g) = xs := by rw [← hx]; exact List.take_length
  have e2 : (xs.take σ.h).length = σ.h := by rw [List.length_take, hx]; omega
  unfold SumPar.summand
  rw [sPt_lst]
  show toE (Fmt.Fld.two.addE (hidePoly .two (σ.h + σ.g) U xs)
    (Fmt.Fld.two.mulE eps (Fmt.Fld.two.addE
      (dot .two (foldLow .two (xs.take (σ.h + σ.g)) c) (foldLow .two (xs.take (σ.h + σ.g)) m))
      (Fmt.Fld.two.mulE (dot .two (foldLow .two (xs.take σ.h) d) (foldLow .two (xs.take σ.h) mu))
        (tailProd .two (xs.take (σ.h + σ.g)) σ.h))))) = _
  rw [e1, toE_addE, toE_mulE, toE_addE, toE_mulE, toE_hidePoly _ _ _ hx,
    toE_dot_fold (σ.h + σ.g) σ.C.l xs hx c m hs.1,
    toE_dot_fold σ.h σ.Z.l (xs.take σ.h) e2 d mu hs.2.2.1]
  have e3 := toE_tailProd_late σ.h σ.g xs hx 0
  rw [Nat.add_zero] at e3
  rw [e3]
  have e4 : (fun t : Fin σ.h => lst (xs.take σ.h) t.val) =
      preP σ (fun t : Fin (σ.h + σ.g) => lst xs t.val) :=
    funext fun t => lst_take σ.h xs t.val t.isLt
  rw [e4]
  simp only [Nat.zero_le, if_true]
  rfl

/-- The two elements that a round sends: the constant and the quadratic coefficient. -/
def roundW (T : Trial) (before : List Fmt.M1.E) : Fmt.M1.E × Fmt.M1.E :=
  ((coeffs .two (roundAt .two T before Fmt.Fld.zeroE) (roundAt .two T before Fmt.Fld.oneE)
      (roundAt .two T before (Fmt.Fld.two.negE Fmt.Fld.oneE))).1,
    (coeffs .two (roundAt .two T before Fmt.Fld.zeroE) (roundAt .two T before Fmt.Fld.oneE)
      (roundAt .two T before (Fmt.Fld.two.negE Fmt.Fld.oneE))).2.2)

/-- The two elements of `roundW` are the constant and the quadratic coefficient of the field's round
polynomial, encoded. -/
theorem round_wordsU (c d m mu : Array Fmt.M1.E) (t : Fmt.M1.E) (U : Hide) (eps : Fmt.M1.E)
    (g : List Fmt.M1.E) (lzk : ℕ) (hs : FoldSizes (σ.h + σ.g) σ.h σ.C.l σ.Z.l c d m mu)
    (γ : HPt (sVars GE 2 (σ.h + σ.g))) (gs : List Fmt.M1.E) (hl : gs.length < σ.h + σ.g)
    (hr : ReadsTo (σ.h + σ.g) gs γ) :
    roundW
        { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U, eps := eps, g := g
          lzk := lzk } gs =
      (ofE (roundPart (σ.h + σ.g) (foldQ σ (vecIn σ ⟨c, d, t⟩) (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩)
          (coefU (σ.h + σ.g) U) (toE eps) γ) gs.length 0),
        ofE (roundPart (σ.h + σ.g) (foldQ σ (vecIn σ ⟨c, d, t⟩) (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩)
          (coefU (σ.h + σ.g) U) (toE eps) γ) gs.length 2)) := by
  have H := (σ.par 0).honQ_rounds (le_refl 2) (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩, fun _ => 0)
    (0, (fun x => vecIn σ ⟨c, d, t⟩ (.inl x), fun x => vecIn σ ⟨c, d, t⟩ (.inr x)))
    (coefU (σ.h + σ.g) U) (toE eps) γ
  have R := fun X => roundPoly_reads (σ.h + σ.g) _ _ γ H
    (sumPoly .two
      { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U, eps := eps, g := g
        lzk := lzk })
    (fun xs hx => toE_sumPolyU σ c d m mu t U eps g lzk hs xs hx) gs X hl hr
  have C := coeffs_read _ _ _ _
    ((R Fmt.Fld.zeroE).trans (by rw [toE_zeroE]))
    ((R Fmt.Fld.oneE).trans (by rw [toE_oneE]))
    ((R (Fmt.Fld.two.negE Fmt.Fld.oneE)).trans (by rw [toE_negE, toE_oneE]))
  refine Prod.ext (eq_ofE ?_ C.1) (eq_ofE ?_ C.2)
  · exact ok_foldl_add _ _ _ (by decide)
  · exact okE_subE _ _

end Field

/-! ## 2 The list of rounds -/

theorem honest_cons (T : Trial) (before : List Fmt.M1.E) (g : Fmt.M1.E) (gs : List Fmt.M1.E) :
    (honest .two T before (g :: gs)).map (·.1) =
      roundW T before :: (honest .two T (before ++ [g]) gs).map (·.1) := rfl

/-- If each round's two elements are coefficients 0 and 2 of q's matching round polynomial, encoded,
the list of rounds is `showRV` of q. off: round i of the list has the challenges D (off + i + 1). -/
theorem rounds_walk (T : Trial) (D : ℕ → Fmt.Drawn) : ∀ (n : ℕ) (q : RIdx (sVars GE 2 n) → GE)
    (gs before : List Fmt.M1.E) (off : ℕ), gs.length = n →
    (∀ i, i < n → roundW T (before ++ gs.take i) =
      (ofE (roundPart n q i 0), ofE (roundPart n q i 2))) →
    (((honest .two T before gs).map (·.1)).zipIdx off).map
        (fun x => (⟨[.e x.1.1, .e x.1.2], D (1 + x.2)⟩ : Fmt.RoundView)) =
      showRV n q fun m => D (off + m + 1)
  | 0, _, [], _, _, _, _ => rfl
  | n + 1, q, g :: gs, before, off, hl, hq => by
    have h0 := hq 0 (Nat.succ_pos n)
    rw [List.take_zero, List.append_nil] at h0
    have ih := rounds_walk T D n (fun j => q (.inr j)) gs (before ++ [g]) (off + 1)
      (Nat.succ.inj hl) (fun i hi => by
        have h := hq (i + 1) (Nat.succ_lt_succ hi)
        rw [List.take_succ_cons] at h
        rw [List.append_assoc, List.cons_append, List.nil_append]
        exact h)
    have eD : (fun m => D (off + 1 + m + 1)) = fun m => D (off + (m + 1) + 1) := by
      funext m
      congr 1
      omega
    rw [honest_cons, List.zipIdx_cons, List.map_cons, ih, h0, eD]
    show _ = (⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))],
      D (off + 0 + 1)⟩ : Fmt.RoundView) :: showRV n (fun j => q (Sum.inr j)) fun m => D (off + (m + 1) + 1)
    rw [show 1 + off = off + 0 + 1 by omega]
    rfl

/-! ## 3 The sampled point -/

theorem toE_headE (d : Fmt.Drawn) : toE (headE d) = drawnE d := (readE_ofTriple _).symm

/-- The list of the sampled elements decodes to the point that `foldShown` uses. -/
theorem point_reads (k : ℕ) (D : ℕ → Fmt.Drawn) :
    ptK k (lst ((List.range k).map fun n => headE (D (1 + n)))) =
      ptK k fun n => drawnE (D (n + 1)) :=
  ptK_congr k _ _ fun i hi => by
    rw [lst_range k _ i hi, toE_headE, Nat.add_comm]

/-! ## 4 The equation -/

/-- `Spec.fold_eq` for a stage given as `Sg`, with the four array sizes as one hypothesis. -/
theorem fold_core (σ : Sg) (c d m mu : Array Fmt.M1.E) (t : Fmt.M1.E) (U : Hide) (lzk : ℕ)
    (D : ℕ → Fmt.Drawn) (hs : FoldSizes (σ.h + σ.g) σ.h σ.C.l σ.Z.l c d m mu) :
    (⟨[.e (Trial.sigma .two
          { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U
            eps := headE (D 0), g := (List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))
            lzk := lzk })], D 0⟩ ::
      ((honest .two
          { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U
            eps := headE (D 0), g := (List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))
            lzk := lzk } []
          ((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n)))).map (·.1)).zipIdx.map
        fun q => ⟨[.e q.1.1, .e q.1.2], D (1 + q.2)⟩ : List Fmt.RoundView) =
      foldShown σ (vecIn σ ⟨c, d, t⟩) (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩) (coefU (σ.h + σ.g) U) D := by
  have hlen : ((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))).length = σ.h + σ.g := by
    rw [List.length_map, List.length_range]
  have hR : ReadsTo (σ.h + σ.g) ((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n)))
      (ptK (σ.h + σ.g) fun n => drawnE (D (n + 1))) := by
    rw [← point_reads]
    exact readsTo_ptK _ _ (Nat.le_of_eq hlen)
  have W := rounds_walk
    { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U, eps := headE (D 0),
      g := (List.range (σ.h + σ.g)).map fun n => headE (D (1 + n)), lzk := lzk } D (σ.h + σ.g)
    (foldQ σ (vecIn σ ⟨c, d, t⟩) (vecIn σ ⟨m, mu, Fmt.Fld.zeroE⟩) (coefU (σ.h + σ.g) U)
      (toE (headE (D 0))) (ptK (σ.h + σ.g) fun n => drawnE (D (n + 1))))
    ((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))) [] 0 hlen (fun i hi => by
      have hl : (((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))).take i).length = i := by
        rw [List.length_take, hlen]
        omega
      have e := round_wordsU σ c d m mu t U (headE (D 0))
        ((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))) lzk hs
        (ptK (σ.h + σ.g) fun n => drawnE (D (n + 1)))
        (((List.range (σ.h + σ.g)).map fun n => headE (D (1 + n))).take i) (by rw [hl]; exact hi)
        (readsTo_take _ _ _ i hR)
      rw [hl] at e
      rw [List.nil_append]
      exact e)
  have S : Trial.sigma .two
      { k := σ.h + σ.g, h := σ.h, G := ⟨c, d, t⟩, m := m, mu := mu, U := U, eps := headE (D 0),
        g := (List.range (σ.h + σ.g)).map fun n => headE (D (1 + n)), lzk := lzk } =
      ofE (hMu (sVars GE 2 (σ.h + σ.g)) (coefU (σ.h + σ.g) U)) :=
    eq_ofE (ok_foldl_add _ _ _ (by decide)) (toE_sigma _)
  have eD : (fun m => D (0 + m + 1)) = fun m => D (m + 1) := by
    funext m
    rw [Nat.zero_add]
  rw [W, S, eD, toE_headE]
  rfl

theorem foldBy_eq : Spec.fold_eq := by
  intro s G last P p U D h hc hd T
  have hk := sg_k h
  have hs : FoldSizes ((sgOf s).h + (sgOf s).g) (sgOf s).h (sgOf s).C.l (sgOf s).Z.l G.c G.d
      (tabOf p.M s.C.l) (tabOf p.W s.Z.l) := by
    rw [hk]
    exact ⟨hc, T.size_main, hd, T.size_mask⟩
  have e := fold_core (sgOf s) G.c G.d (tabOf p.M s.C.l) (tabOf p.W s.Z.l) G.t U s.Z.l D hs
  rw [T.reads h] at e
  rw [← e, hk]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.toE_sumPolyU
#print axioms ProofFile.Honest.K12.Light.round_wordsU
#print axioms ProofFile.Honest.K12.Light.honest_cons
#print axioms ProofFile.Honest.K12.Light.rounds_walk
#print axioms ProofFile.Honest.K12.Light.toE_headE
#print axioms ProofFile.Honest.K12.Light.point_reads
#print axioms ProofFile.Honest.K12.Light.fold_core
#print axioms ProofFile.Honest.K12.Light.foldBy_eq
#print axioms ProofFile.Honest.K12.Light.roundW
