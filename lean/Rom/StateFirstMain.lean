-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstMain.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), for its main lemma (`Spec.mixClose`, Rom/StateFirstMix.lean), the induction:
proves `Spec.mainLe` (stated in Rom/StateFirstHitDef.lean).

Chain oracles, states, dr: `Link`, `stSpec` (Rom/StateFirst.lean); mixed programs, `real`, `ideal`,
`Book`: Rom/StateFirstMix.lean; hidden queries, `Psi`, `Ghost`: Rom/StateFirstHitDef.lean.

`mainLe`: let the lazily sampled tables Tp, T and a table bT of all chain answers, which exists only
in the proof, be consistent (`Rel`, Rom/StateFirstColl.lean), and let T, bT, the reduction's table
bF and the hidden queries H be related by `Ghost`. Then, under `MixBound`, Pr[real' ∈ E] ≤ Pr[the
reduction's interpretation ∈ E] + n (m + n) / 2^(2 lam) + Psi, where n = t + r for
`MixBound C c t r` (the queries still to come that can write into bT), m bounds the entries of bT,
and `Psi` is the expected number of raw expansion queries at states of hidden queries.

The proof is the induction of `coll_le` (Rom/StateFirstColl2.lean), with `ideal C false c bF` in
place of `shadow`, bT a parameter of the induction, and Psi in place of the flag. At a raw expansion
query where bT and bF differ the state of a hidden query is queried (`ghost_hit`), so Psi is at
least 1.

Limits: Psi is not bounded here (`Spec.psiLe`). Nothing on `Pr`: the statement is on lazy sampling
from given tables.
-/
import Rom.StateFirstGhost

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {C : ∀ o, Link lam (S.Rng o)} {α : Type}

/-- Under `Rel`, a query that was made before returns the old answer and leaves the table of the
second family unchanged. -/
theorem runLazy_st_old {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam}
    (hRel : Rel C Tp T b) {o : S.ι} {q : S.Dom o} {r : S.Rng o} (hT : T o q = some r)
    (KR : (C o).Ans → S.Rng o → OComp (stSpec S lam C) α) :
    (OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
        (expand C (C o) a).bind (KR a)).runLazy Tp =
      (KR ((C o).toAns r) r).runLazy Tp := by
  have hTp : Tp (.inl o) q = some ((C o).toAns r) := by rw [hRel.st, hT]; rfl
  simp only [OComp.runLazy, hTp]
  rw [OComp.runLazy_bind,
    expand_old C (C o) r Tp fun σ hs j v hv => by rw [hRel.dr]; exact hRel.blk o q r hT σ hs j v hv,
    PMF.pure_bind]

/-- Under `Rel`, hIH, a new query: the error term is averaged, and the probability of an answer that
is not fine (Rom/StateFirstGhost.lean) is added. -/
theorem st_new {Tp : Table (stSpec S lam C)} {T : Table S} {b : Book S lam} (hRel : Rel C Tp T b)
    {o : S.ι} {q : S.Dom o} (hT : T o q = none)
    (KR : (C o).Ans → S.Rng o → OComp (stSpec S lam C) α) {γ : Type} (KI : S.Rng o → OComp S γ)
    (E : Set α) (EI : Set (γ × Table S)) (βf : S.Rng o → ℝ≥0∞)
    (hIH : ∀ r, (C o).fine (stL C b) r →
      ∀ Tp', Rel C Tp' (T.set o q r) (b.note C o q r) →
        pr ((KR ((C o).toAns r) r).runLazy Tp') {x | x.1 ∈ E} ≤
          pr ((KI r).runLazy (T.set o q r)) EI + βf r) :
    pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
          (expand C (C o) a).bind (KR a)).runLazy Tp) {x | x.1 ∈ E} ≤
      pr ((OComp.query o q KI).runLazy T) EI + expect (unif (S.Rng o)) βf +
        pr (unif (S.Rng o)) {r | ¬ (C o).fine (stL C b) r} := by
  classical
  have hTp : Tp (.inl o) q = none := by rw [hRel.st, hT]; rfl
  have e1 : pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
          (expand C (C o) a).bind (KR a)).runLazy Tp) {x | x.1 ∈ E} =
      expect (unif (C o).Ans) fun a =>
        expect ((expand C (C o) a).runLazy (Tp.set (S := stSpec S lam C) (.inl o) q a))
            fun x => pr ((KR a x.1).runLazy x.2) {x | x.1 ∈ E} := by
    simp only [OComp.runLazy, hTp]
    rw [pr_bind]
    refine expect_congr _ fun a => ?_
    rw [OComp.runLazy_bind, pr_bind]
  have e2 : pr ((OComp.query o q KI).runLazy T) EI =
      expect (unif (S.Rng o)) fun r => pr ((KI r).runLazy (T.set o q r)) EI := by
    simp only [OComp.runLazy, hT]
    rw [pr_bind]
  rw [e1, e2]
  refine le_trans (new_step C (C o) (fun a => Tp.set (S := stSpec S lam C) (.inl o) q a) (drVal C b) (fun a p => by
    show (Tp.set (S := stSpec S lam C) (.inl o) q a) (.inr ()) p = _
    rw [Table.set_ne_oracle (S := stSpec S lam C) Tp
        (show (Sum.inr () : S.ι ⊕ Unit) ≠ Sum.inl o from fun e => by cases e)]
    exact hRel.dr p) (fun a x => pr ((KR a x.1).runLazy x.2) {x | x.1 ∈ E}) fun a x => pr_le_one _ _) ?_
  refine le_trans
    (expect_mono _
      (G := fun r =>
          if (C o).fine (stL C b) r then pr ((KI r).runLazy (T.set o q r)) EI + βf r else 1)
      fun r => ?_) ?_
  · beta_reduce
    by_cases hf : (C o).fine (stL C b) r
    · rw [if_pos (good_of_fine C hf), if_pos hf]
      exact hIH r hf _ (rel_new hRel hT r (good_of_fine C hf))
    · rw [if_neg hf]
      split
      · exact pr_le_one _ _
      · exact le_rfl
  · refine le_trans (expect_ite_le _ _ _) ?_
    rw [expect_add]

theorem add_shuffle {A B P F B' : ℝ≥0∞} (h : B + F ≤ B') : A + (B + P) + F ≤ A + B' + P := by
  calc A + (B + P) + F = A + (B + F) + P := by ring
    _ ≤ A + B' + P := by gcongr

/-- `Spec.mainLe` (Rom/StateFirstHitDef.lean). -/
theorem mainLe : Spec.mainLe := by
  intro S lam C α c
  induction c with
  | pure a =>
    intro t r m Tp T bT bF H _ _ _ _ E
    simp only [real', ideal, OComp.runLazy]
    rw [pr_pure, pr_pure]
    refine le_trans ?_ (le_trans le_self_add le_self_add)
    by_cases h : a ∈ E
    · rw [if_pos (show ((a, Tp) : α × Table (stSpec S lam C)) ∈ {x | x.1 ∈ E} from h),
        if_pos (show (((a, bF), T) : (α × Book S lam) × Table S) ∈ {x | x.1.1 ∈ E} from h)]
    · rw [if_neg (show ((a, Tp) : α × Table (stSpec S lam C)) ∉ {x | x.1 ∈ E} from h)]
      exact zero_le _
  | sample n k ih =>
    intro t r m Tp T bT bF H hB hRel hG hm E
    simp only [real', ideal, Psi, OComp.runLazy]
    rw [pr_bind, pr_bind]
    refine le_trans (expect_mono _ fun x => ih x t r m Tp T bT bF H (hB x) hRel hG hm E) ?_
    rw [expect_add, expect_add, expect_const]
  | query x q k ih =>
    intro t r m Tp T bT bF H hB hRel hG hm E
    have hFine : ∀ o : S.ι,
        pr (unif (S.Rng o)) {r | ¬ (C o).fine (stL C bT) r} ≤ (m : ℝ≥0∞) * wSt lam := fun o => by
      refine le_trans (pr_not_fine (C o) _) ?_
      gcongr
      exact le_trans (length_stL_le C bT) hm
    match x, q, k, ih, hB with
    | .inl o, q, k, ih, hB =>
      have hB' : if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t r else ∃ t', t = t' + 1 ∧ ∀ x, MixBound C (k x) t' r := hB
      show pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
            (expand C (C o) a).bind fun r => real' C (k r)).runLazy Tp) {x | x.1 ∈ E} ≤
        pr ((OComp.query o q fun r => ideal C false (k r) bF).runLazy T) {x | x.1.1 ∈ E} + _ + _
      cases hT : T o q with
      | some r0 =>
        have hBm : MixBound C (k r0) t r := by
          by_cases hp : (C o).isPlain = true
          · rw [if_pos hp] at hB'
            exact hB' r0
          · rw [if_neg hp] at hB'
            obtain ⟨t', rfl, h⟩ := hB'
            exact (h r0).mono (Nat.le_succ _) le_rfl
        have e2 : (OComp.query o q fun r => ideal C false (k r) bF).runLazy T =
            (ideal C false (k r0) bF).runLazy T := by
          simp only [OComp.runLazy, hT]
        have eP : Psi C (OComp.query (S := mixSpec C) (.inl o) q k) T bF H =
            Psi C (k r0) T bF H := by
          simp only [Psi, hT]
        rw [runLazy_st_old hRel hT (fun _ r => real' C (k r)), e2, eP]
        exact ih r0 t r m Tp T bT bF H hBm hRel hG hm E
      | none =>
        have hR : (C o).isPlain = false → findMade bT.made o q = none := fun hp =>
          (hRel.made o q hp).trans hT
        have eP : Psi C (OComp.query (S := mixSpec C) (.inl o) q k) T bF H =
            expect (unif (S.Rng o)) fun r =>
              Psi C (k r) (T.set o q r) bF (if (C o).isPlain = true then H else ⟨o, q⟩ :: H) := by
          simp only [Psi, hT]
        rw [eP]
        by_cases hp : (C o).isPlain = true
        · rw [if_pos hp] at hB'
          have h1 := st_new hRel hT (fun _ r => real' C (k r))
            (fun r => ideal C false (k r) bF) E {x | x.1.1 ∈ E}
            (fun r' =>
              bnd lam (t + r) m +
                Psi C (k r') (T.set o q r') bF (if (C o).isPlain = true then H else ⟨o, q⟩ :: H))
            fun r' hf Tp' hR' =>
              (ih r' t r m Tp' _ _ bF _ (hB' r') hR' (ghost_typed_new hG hR hT hf)
                  (by rw [note_plain C bT o q r' hp]; exact hm) E).trans_eq
                (add_assoc _ _ _)
          rw [pr_not_fine_plain (C o) hp, add_zero, expect_add, expect_const, ← add_assoc] at h1
          exact h1
        · rw [if_neg hp] at hB'
          obtain ⟨t', rfl, hB''⟩ := hB'
          have h1 := st_new hRel hT (fun _ r => real' C (k r))
            (fun r => ideal C false (k r) bF) E {x | x.1.1 ∈ E}
            (fun r' =>
              bnd lam (t' + r) (m + 1) +
                Psi C (k r') (T.set o q r') bF (if (C o).isPlain = true then H else ⟨o, q⟩ :: H))
            fun r' hf Tp' hR' =>
              (ih r' t' r (m + 1) Tp' _ _ bF _ (hB'' r') hR' (ghost_typed_new hG hR hT hf)
                  (le_trans (size_note C bT o q r') (Nat.add_le_add_right hm 1)) E).trans_eq
                (add_assoc _ _ _)
          refine le_trans h1 ?_
          rw [expect_add, expect_const]
          refine add_shuffle (le_trans (add_le_add le_rfl (hFine o)) ?_)
          rw [show t' + 1 + r = t' + r + 1 by omega]
          exact bnd_step lam (t' + r) m
    | .inr (.inl o), q, k, ih, hB =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        show pr ((OComp.query (S := stSpec S lam C) (.inl o) q fun a =>
              (expand C (C o) a).bind fun _ => real' C (k a)).runLazy Tp) {x | x.1 ∈ E} ≤
          pr ((OComp.query o q fun r =>
                ideal C false (k ((C o).toAns r)) (bF.note C o q r)).runLazy T)
              {x | x.1.1 ∈ E} +
            _ + _
        cases hT : T o q with
        | some r0 =>
          have hR : (C o).isPlain = false → findMade bT.made o q = some r0 := fun hp =>
            (hRel.made o q hp).trans hT
          have e2 : (OComp.query o q fun r =>
                ideal C false (k ((C o).toAns r)) (bF.note C o q r)).runLazy T =
              (ideal C false (k ((C o).toAns r0)) (bF.note C o q r0)).runLazy T := by
            simp only [OComp.runLazy, hT]
          rw [runLazy_st_old hRel hT (fun a _ => real' C (k a)), e2]
          simp only [Psi, hT]
          exact le_trans (ih _ t r' m Tp T bT _ _ (hB' _) hRel (ghost_raw_old hG hT hR) hm E)
            (add_le_add (add_le_add le_rfl (bnd_mono (by omega) le_rfl)) le_rfl)
        | none =>
          have hR : (C o).isPlain = false → findMade bT.made o q = none := fun hp =>
            (hRel.made o q hp).trans hT
          have eP : Psi C (OComp.query (S := mixSpec C) (.inr (.inl o)) q k) T bF H =
              expect (unif (S.Rng o)) fun r =>
                Psi C (k ((C o).toAns r)) (T.set o q r) (bF.note C o q r) H := by
            simp only [Psi, hT]
          rw [eP]
          have h1 := st_new hRel hT (fun a _ => real' C (k a))
            (fun r => ideal C false (k ((C o).toAns r)) (bF.note C o q r)) E {x | x.1.1 ∈ E}
            (fun r'' =>
              bnd lam (t + r') (m + 1) +
                Psi C (k ((C o).toAns r'')) (T.set o q r'') (bF.note C o q r'') H)
            fun r'' hf Tp' hR' =>
              (ih _ t r' (m + 1) Tp' _ _ _ _ (hB' _) hR' (ghost_raw_new hG hR hT hf)
                  (le_trans (size_note C bT o q r'') (Nat.add_le_add_right hm 1)) E).trans_eq
                (add_assoc _ _ _)
          refine le_trans h1 ?_
          rw [expect_add, expect_const]
          refine add_shuffle (le_trans (add_le_add le_rfl (hFine o)) ?_)
          rw [show t + (r' + 1) = t + r' + 1 by omega]
          exact bnd_step lam (t + r') m
    | .inr (.inr ()), p, k, ih, hB =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        have hdr : Tp (.inr ()) p = drVal C bT p := hRel.dr p
        by_cases hd : drVal C bT p = drVal C bF p
        · cases hv : drVal C bF p with
          | some v =>
            have e1 : (real' C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k)).runLazy Tp =
                (real' C (k v)).runLazy Tp := by
              rw [hd, hv] at hdr
              simp only [real', OComp.runLazy, hdr]
            have e2 : ideal C false (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) bF =
                ideal C false (k v) bF := by
              simp only [ideal, hv]
            have eP : Psi C (k v) T bF H ≤
                Psi C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) T bF H := by
              simp only [Psi, hv]
              exact le_add_self
            rw [e1, e2]
            exact le_trans (ih v t r' m Tp T bT bF H (hB' v) hRel hG hm E)
              (add_le_add (add_le_add le_rfl (bnd_mono (by omega) le_rfl)) eP)
          | none =>
            have e1 : pr ((real' C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k)).runLazy Tp)
                  {x | x.1 ∈ E} =
                expect (unif (Fin (nDg lam + 1))) fun x =>
                  pr ((real' C (k (digE lam x))).runLazy
                        (Tp.set (S := stSpec S lam C) (.inr ()) p (digE lam x)))
                      {x | x.1 ∈ E} := by
              rw [hd, hv] at hdr
              simp only [real', OComp.runLazy, hdr]
              rw [pr_bind]
              have hu : (PMF.uniformOfFintype (Dg lam)) =
                  (unif (Fin (nDg lam + 1))).map (digE lam) :=
                (map_unif_equiv (digE lam)).symm
              show expect (PMF.uniformOfFintype (Dg lam)) _ = _
              rw [hu, expect_map]
            have e2 : pr
                  ((ideal C false (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) bF).runLazy T)
                  {x | x.1.1 ∈ E} =
                expect (unif (Fin (nDg lam + 1))) fun x =>
                  pr ((ideal C false (k (digE lam x))
                        { bF with loose := (p, digE lam x) :: bF.loose }).runLazy T)
                      {x | x.1.1 ∈ E} := by
              simp only [ideal, hv, OComp.runLazy]
              rw [pr_bind]
            have eP : (expect (unif (Fin (nDg lam + 1))) fun x =>
                  Psi C (k (digE lam x)) T { bF with loose := (p, digE lam x) :: bF.loose } H) ≤
                Psi C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) T bF H := by
              simp only [Psi, hv]
              exact le_add_self
            rw [e1, e2]
            refine le_trans
              (expect_mono _ fun x =>
                ih (digE lam x) t r' (m + 1) _ T { bT with loose := (p, digE lam x) :: bT.loose }
                  { bF with loose := (p, digE lam x) :: bF.loose } H
              (hB' _) (rel_loose hRel (hd.trans hv) (digE lam x)) (ghost_loose hG _) (by
              show bT.made.length + (bT.loose.length + 1) ≤ m + 1
              omega) E) ?_
            rw [expect_add, expect_add, expect_const]
            refine add_le_add
              (add_le_add le_rfl
                (le_trans le_self_add (le_trans (bnd_step lam (t + r') m) (le_of_eq ?_)))) eP
            rw [show t + (r' + 1) = t + r' + 1 by omega]
        · -- bT and bF differ: a hidden query's state is queried
          have eP : 1 ≤ Psi C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) T bF H := by
            simp only [Psi]
            rw [if_pos (ghost_hit hG p hd)]
            exact le_self_add
          exact le_trans (pr_le_one _ _) (le_trans eP le_add_self)

end Rom
