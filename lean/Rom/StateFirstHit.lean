-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstHit.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): proof of `Spec.psiLe` (Rom/StateFirstHitDef.lean), the bound on the average
of `Psi`, for the main lemma `Spec.mixClose`.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

After the step a chain oracle returns only a state: the chaining value and the last block, hid, of
its old answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) hid is the second block of a state. `Psi` is the
expected number of raw expansion queries at states of hidden queries (Rom/StateFirstHitDef.lean).

`psiLe`: for a mixed program (typed and raw queries; `real`, `ideal`, `Book`:
Rom/StateFirstMix.lean) with at most t typed queries at chain oracles and r raw queries
(`MixBound`), whose typed continuations do not depend on hid (`HidFreeM`), and a list H of distinct
hidden queries at which the table has entries: the average of `Psi` over fresh uniform hids at H
(`avgH`) is at most (|H| + t) · r / 2^lam.

The proof is by induction on the program (`psi_le`). A typed query that is hidden returns an answer
whose hid the continuation does not read; a new typed query to a chain oracle makes a hidden query
whose hid is fresh; a raw query for the state of a hidden query takes its hid out of the average; a
raw expansion query is answered from the reduction's table or by a coin, neither of which depends on
a hid under the average.

Limits: the bound is on the average of Psi over fresh hids at the hidden queries; for given hids Psi
can be larger. At H = [] the average is Psi itself. Nothing on the real interpretation
(Rom/StateFirstMain.lean).
-/
import Rom.StateFirstAvg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {C : ∀ o, Link lam (S.Rng o)} {α : Type}

def wH (lam : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ lam)⁻¹
def hb (lam n r : ℕ) : ℝ≥0∞ := ((n * r : ℕ) : ℝ≥0∞) * wH lam

theorem hb_mono {lam n n' r r' : ℕ} (hn : n ≤ n') (hr : r ≤ r') : hb lam n r ≤ hb lam n' r' := by
  unfold hb
  gcongr

theorem Table.set_set {S : OSpec} (T : Table S) (o : S.ι) (q : S.Dom o) (r r' : S.Rng o) :
    (T.set o q r).set o q r' = T.set o q r' := by
  funext o' q'
  by_cases a : (⟨o', q'⟩ : PtS S) = ⟨o, q⟩
  · cases a
    rw [Table.set_self, Table.set_self]
  · rw [Table.set_ne _ a, Table.set_ne _ a, Table.set_ne _ a]

theorem expect_eq_hid (v : Dg lam) :
    (expect (unif (Dg lam)) fun u => if u = v then (1 : ℝ≥0∞) else 0) = wH lam := by
  have h := expect_ite_eq (unif (Dg lam)) v 1
  rw [mul_one] at h
  refine Eq.trans (expect_congr _ fun u => ?_) (h.trans ?_)
  · by_cases hu : u = v
    · rw [if_pos hu, if_pos hu]
    · rw [if_neg hu, if_neg hu]
  · show PMF.uniformOfFintype (Dg lam) v = _
    rw [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    unfold wH
    push_cast
    rfl

open Classical in
/-- Averaged over fresh hids at the distinct queries H, a given state is the state of one given
hidden query h of H with probability at most 2^-lam. -/
theorem hit_one (H : List (PtS S)) (hN : H.Nodup) (T : Table S) (h : PtS S)
    (hm : h ∈ H) (σ : Dg lam × Dg lam) :
    avgH C H (fun T' => if ∃ r, T' h.1 h.2 = some r ∧ (C h.1).stateOf r = some σ then 1 else 0) T ≤
      wH lam := by
  rw [avgH_extract C H _ T h hm, ← expect_eq_hid σ.2]
  refine expect_mono _ fun u => ?_
  have hne : h ∉ H.erase h := fun hh => (List.Nodup.not_mem_erase hN) hh
  rw [avgH_congr C (H.erase h)
        (G := fun _ =>
            if ∃ r,
              (Table.reHid C T h u) h.1 h.2 = some r ∧ (C h.1).stateOf r = some σ then 1 else 0)
        _ fun T' hs => by rw [(hs h.1 h.2).1 hne], avgH_const]
  by_cases hu : u = σ.2
  · rw [if_pos hu]
    split_ifs <;> simp
  · rw [if_neg hu, if_neg]
    rintro ⟨r, hr, hs⟩
    rw [reHid_at] at hr
    cases hT : T h.1 h.2 with
    | none => rw [hT] at hr; cases hr
    | some r0 =>
      rw [hT] at hr
      have e : (C h.1).setHid r0 u = r := Option.some.inj hr
      rw [← e] at hs
      exact hu ((C h.1).stateOf_setHid hs)

open Classical in
/-- Averaged over fresh hids at the distinct queries H, a given state is the state of some hidden
query of a list H0 of queries of H with probability at most |H0| / 2^lam. -/
theorem hit_le (H : List (PtS S)) (hN : H.Nodup) (T : Table S) (σ : Dg lam × Dg lam) :
    ∀ H0 : List (PtS S), (∀ h ∈ H0, h ∈ H) →
      avgH C H (fun T' => if hitAt C T' H0 σ then 1 else 0) T ≤ (H0.length : ℝ≥0∞) * wH lam
  | [], _ => by
    rw [avgH_congr C H (G := fun _ => 0) T fun T' _ => if_neg (by rintro ⟨h, hh, -⟩; cases hh),
      avgH_const]
    exact zero_le _
  | h :: H0, hsub => by
    refine le_trans
      (avgH_mono C H
        (G := fun T' =>
            (if ∃ r, T' h.1 h.2 = some r ∧ (C h.1).stateOf r = some σ then 1 else 0) +
              if hitAt C T' H0 σ then 1 else 0)
        T fun T' _ => ?_) ?_
    · beta_reduce
      by_cases hh : hitAt C T' (h :: H0) σ
      · rw [if_pos hh]
        obtain ⟨h', hm, r, hr, hs⟩ := hh
        rcases List.mem_cons.mp hm with rfl | hm'
        · rw [if_pos ⟨r, hr, hs⟩]
          exact le_self_add
        · rw [if_pos (show hitAt C T' H0 σ from ⟨h', hm', r, hr, hs⟩)]
          exact le_add_self
      · rw [if_neg hh]
        exact zero_le _
    · rw [avgH_add]
      refine le_trans
        (add_le_add (hit_one H hN T h (hsub h List.mem_cons_self) σ)
          (hit_le H hN T σ H0 fun h' hm => hsub h' (List.mem_cons_of_mem _ hm))) (le_of_eq ?_)
      rw [List.length_cons]
      push_cast
      ring

theorem hb_step (lam L t r : ℕ) :
    (L : ℝ≥0∞) * wH lam + hb lam (L + t) r ≤ hb lam (L + t) (r + 1) := by
  unfold hb
  rw [← add_mul]
  gcongr
  have : L + (L + t) * r ≤ (L + t) * (r + 1) := by nlinarith
  exact_mod_cast this

open Classical in
/-- The induction. Under `MixBound`, `HidFreeM`, for distinct hidden queries H at which T has
entries: the average of `Psi` over fresh hids at H is at most (|H| + t) r / 2^lam. -/
theorem psi_le (c : OComp (mixSpec C) α) :
    ∀ (t r : ℕ) (T : Table S) (b : Book S lam) (H : List (PtS S)), MixBound C c t r → HidFreeM C c →
      H.Nodup → (∀ h ∈ H, T h.1 h.2 ≠ none) →
      avgH C H (fun T' => Psi C c T' b H) T ≤ hb lam (H.length + t) r := by
  induction c with
  | pure a =>
    intro t r T b H _ _ _ _
    have e : avgH C H (fun T' => Psi C (OComp.pure a : OComp (mixSpec C) α) T' b H) T =
        avgH C H (fun _ => 0) T :=
      avgH_congr C H T fun T' _ => by simp only [Psi]
    rw [e, avgH_const]
    exact zero_le _
  | sample n k ih =>
    intro t r T b H hB hF hN hL
    have e : avgH C H (fun T' => Psi C (OComp.sample n k) T' b H) T =
        avgH C H (fun T' => expect (unif (Fin (n + 1))) fun x => Psi C (k x) T' b H) T :=
      avgH_congr C H T fun T' _ => by simp only [Psi]
    rw [e, avgH_expect]
    exact expect_le_of_forall_le _ fun x _ => ih x t r T b H (hB x) (hF x) hN hL
  | query x q k ih =>
    intro t r T b H hB hF hN hL
    match x, q, k, ih, hB, hF with
    | .inl o, q, k, ih, hB, hF =>
      have hB' : if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t r else ∃ t', t = t' + 1 ∧ ∀ x, MixBound C (k x) t' r := hB
      have hF' : (∀ r r', (C o).agH r r' → k r = k r') ∧ ∀ r, HidFreeM C (k r) := hF
      cases hT : T o q with
      | some r0 =>
        have hBm : MixBound C (k r0) t r := by
          by_cases hp : (C o).isPlain = true
          · rw [if_pos hp] at hB'
            exact hB' r0
          · rw [if_neg hp] at hB'
            obtain ⟨t', rfl, h⟩ := hB'
            exact (h r0).mono (Nat.le_succ _) le_rfl
        have e : avgH C H (fun T' => Psi C (OComp.query (S := mixSpec C) (.inl o) q k) T' b H) T =
            avgH C H (fun T' => Psi C (k r0) T' b H) T :=
          avgH_congr C H T fun T' hs => by
            obtain ⟨r', hr', ha⟩ := hs.some hT
            simp only [Psi, hr']
            rw [hF'.1 r0 r' ha]
        rw [e]
        exact ih r0 t r T b H hBm (hF'.2 r0) hN hL
      | none =>
        have hnH : (⟨o, q⟩ : PtS S) ∉ H := fun h => hL _ h hT
        have hL' : ∀ r', ∀ h ∈ H, (T.set o q r') h.1 h.2 ≠ none := fun r' h hh => by
          rw [Table.set_ne T (fun e => hnH (e ▸ hh)) r']
          exact hL h hh
        have e : avgH C H (fun T' => Psi C (OComp.query (S := mixSpec C) (.inl o) q k) T' b H) T =
            avgH C H (fun T' =>
                expect (unif (S.Rng o)) fun r' =>
                  Psi C (k r') (T'.set o q r') b (if (C o).isPlain = true then H else ⟨o, q⟩ :: H))
              T :=
          avgH_congr C H T fun T' hs => by simp only [Psi, hs.none hT]
        rw [e, avgH_expect]
        refine le_trans
          (le_of_eq (expect_congr _ fun r' =>
              avgH_set C H
                (fun T'' => Psi C (k r') T'' b (if (C o).isPlain = true then H else ⟨o, q⟩ :: H))
                T hnH r')) ?_
        by_cases hp : (C o).isPlain = true
        · rw [if_pos hp] at hB'
          simp only [if_pos hp]
          exact expect_le_of_forall_le _ fun r' _ => ih r' t r _ b H (hB' r') (hF'.2 r') hN (hL' r')
        · rw [if_neg hp] at hB'
          simp only [if_neg hp]
          obtain ⟨t', rfl, hB''⟩ := hB'
          rw [← unif_setHid (C o) fun r' =>
              avgH C H (fun T'' => Psi C (k r') T'' b (⟨o, q⟩ :: H)) (T.set o q r')]
          refine expect_le_of_forall_le _ fun r' _ => ?_
          have e2 : (expect (unif (Dg lam)) fun u =>
                avgH C H (fun T'' => Psi C (k ((C o).setHid r' u)) T'' b (⟨o, q⟩ :: H))
                  (T.set o q ((C o).setHid r' u))) =
              avgH C (⟨o, q⟩ :: H) (fun T'' => Psi C (k r') T'' b (⟨o, q⟩ :: H))
                (T.set o q r') := by
            show _ = expect (unif (Dg lam)) fun u =>
                avgH C H (fun T'' => Psi C (k r') T'' b (⟨o, q⟩ :: H))
                  (Table.reHid C (T.set o q r') ⟨o, q⟩ u)
            refine expect_congr _ fun u => ?_
            rw [← hF'.1 r' _ ((C o).agH_setHid r' u),
              reHid_some C (h := ⟨o, q⟩) (Table.set_self T o q r') u, Table.set_set]
          refine le_trans (le_of_eq e2)
            (le_trans (ih r' t' r _ b (⟨o, q⟩ :: H) (hB'' r') (hF'.2 r')
                (List.nodup_cons.2 ⟨hnH, hN⟩) fun h hh => ?_) (le_of_eq ?_))
          · rcases List.mem_cons.1 hh with rfl | hh
            · rw [Table.set_self]
              exact Option.some_ne_none _
            · exact hL' r' h hh
          · rw [List.length_cons, show H.length + 1 + t' = H.length + (t' + 1) by omega]
    | .inr (.inl o), q, k, ih, hB, hF =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        have hF' : ∀ x, HidFreeM C (k x) := hF
        cases hT : T o q with
        | none =>
          have hnH : (⟨o, q⟩ : PtS S) ∉ H := fun h => hL _ h hT
          have hL' : ∀ r', ∀ h ∈ H, (T.set o q r') h.1 h.2 ≠ none := fun r' h hh => by
            rw [Table.set_ne T (fun e => hnH (e ▸ hh)) r']
            exact hL h hh
          have e : avgH C H
                (fun T' => Psi C (OComp.query (S := mixSpec C) (.inr (.inl o)) q k) T' b H) T =
              avgH C H (fun T' =>
                  expect (unif (S.Rng o)) fun r'' =>
                    Psi C (k ((C o).toAns r'')) (T'.set o q r'') (b.note C o q r'') H) T :=
            avgH_congr C H T fun T' hs => by simp only [Psi, hs.none hT]
          rw [e, avgH_expect,
            expect_congr _ fun r'' =>
              avgH_set C H (fun T'' => Psi C (k ((C o).toAns r'')) T'' (b.note C o q r'') H)
                T hnH r'']
          exact expect_le_of_forall_le _ fun r'' _ =>
            le_trans (ih _ t r' _ _ H (hB' _) (hF' _) hN (hL' r'')) (hb_mono le_rfl (Nat.le_succ _))
        | some r0 =>
          by_cases hH : (⟨o, q⟩ : PtS S) ∈ H
          · rw [avgH_extract C H _ T ⟨o, q⟩ hH]
            refine expect_le_of_forall_le _ fun u _ => ?_
            have hne : (⟨o, q⟩ : PtS S) ∉ H.erase ⟨o, q⟩ := List.Nodup.not_mem_erase hN
            have hTu : (Table.reHid C T ⟨o, q⟩ u) o q = some ((C o).setHid r0 u) := by
              have h3 := reHid_at C T ⟨o, q⟩ u
              simp only at h3
              rw [h3, hT]
              rfl
            have e : avgH C (H.erase ⟨o, q⟩)
                  (fun T' => Psi C (OComp.query (S := mixSpec C) (.inr (.inl o)) q k) T' b H)
                  (Table.reHid C T ⟨o, q⟩ u) =
                avgH C (H.erase ⟨o, q⟩)
                  (fun T' =>
                    Psi C (k ((C o).toAns ((C o).setHid r0 u))) T'
                      (b.note C o q ((C o).setHid r0 u)) (H.erase ⟨o, q⟩))
                  (Table.reHid C T ⟨o, q⟩ u) :=
              avgH_congr C _ _ fun T' hs => by
                have h1 : T' o q = some ((C o).setHid r0 u) := ((hs o q).1 hne).trans hTu
                simp only [Psi, h1]
            rw [e]
            refine le_trans
              (ih _ t r' _ _ (H.erase ⟨o, q⟩) (hB' _) (hF' _) (hN.erase _) fun h hh => ?_)
              (hb_mono (Nat.add_le_add_right (List.length_erase_le) _) (Nat.le_succ _))
            rw [reHid_ne C T ⟨o, q⟩ u (fun e' => (hN.mem_erase_iff.1 hh).1 e')]
            exact hL h (List.mem_of_mem_erase hh)
          · have e : avgH C H
              (fun T' => Psi C (OComp.query (S := mixSpec C) (.inr (.inl o)) q k) T' b H) T
                = avgH C H (fun T' => Psi C (k ((C o).toAns r0)) T' (b.note C o q r0) H) T :=
              avgH_congr C H T fun T' hs => by
                have h1 : T' o q = some r0 := ((hs o q).1 hH).trans hT
                simp only [Psi, h1]
                rw [List.erase_of_not_mem hH]
            rw [e]
            exact le_trans (ih _ t r' T _ H (hB' _) (hF' _) hN hL) (hb_mono le_rfl (Nat.le_succ _))
    | .inr (.inr ()), p, k, ih, hB, hF =>
      cases r with
      | zero => exact absurd hB (by simp [MixBound])
      | succ r' =>
        have hB' : ∀ x, MixBound C (k x) t r' := hB
        have hF' : ∀ x, HidFreeM C (k x) := hF
        cases hv : drVal C b p with
        | some v =>
          have e : avgH C H
                (fun T' => Psi C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) T' b H) T =
              avgH C H (fun T' => (if hitAt C T' H p.1 then 1 else 0) + Psi C (k v) T' b H) T :=
            avgH_congr C H T fun T' _ => by simp only [Psi, hv]
          rw [e, avgH_add]
          exact le_trans
            (add_le_add (hit_le H hN T p.1 H fun _ h => h) (ih v t r' T b H (hB' v) (hF' v) hN hL))
            (hb_step lam H.length t r')
        | none =>
          have e : avgH C H
                (fun T' => Psi C (OComp.query (S := mixSpec C) (.inr (.inr ())) p k) T' b H) T =
              avgH C H (fun T' =>
                  (if hitAt C T' H p.1 then 1 else 0) +
                    expect (unif (Fin (nDg lam + 1))) fun x =>
                      Psi C (k (digE lam x)) T' { b with loose := (p, digE lam x) :: b.loose } H)
                T :=
            avgH_congr C H T fun T' _ => by simp only [Psi, hv]
          rw [e, avgH_add, avgH_expect]
          exact le_trans
            (add_le_add (hit_le H hN T p.1 H fun _ h => h)
              (expect_le_of_forall_le _ fun x _ => ih _ t r' T _ H (hB' _) (hF' _) hN hL))
            (hb_step lam H.length t r')

/-- `Spec.psiLe` (Rom/StateFirstHitDef.lean). -/
theorem psiLe : Spec.psiLe := fun _ _ _ _ c t r T b H hB hF hN hL => psi_le c t r T b H hB hF hN hL

end Rom
