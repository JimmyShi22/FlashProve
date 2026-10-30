-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNmOfProofs.lean: the proofs of Cb/Part/LdPartNmOf.lean: the naming of a body's matrix
at a partition.

Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Many statements of this library are written
twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same name
outside that namespace proves it (lean/GLOSSARY.md).

Limits: what the head of Cb/Part/LdPartNmOf.lean lists as not said is not said here either.
-/
import Cb.Part.LdPartNmOf
import Cb.Part.LdPartReadProofs
import Cb.Part.LdPartCellsProofs

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

/-- For 0 < P, (n + P - 1) / P packed rows hold all n rows. -/
theorem ldPartNmOf_ceil (n P : ℕ) (hP : 0 < P) : n ≤ (n + P - 1) / P * P := by
  have h := Nat.div_add_mod (n + P - 1) P
  have h2 := Nat.mod_lt (n + P - 1) hP
  rw [Nat.mul_comm] at h
  generalize (n + P - 1) / P * P = t at h ⊢
  omega

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

omit [Fintype F] in
theorem ldPartNmOf_rows {on : ℕ → Bool} {s r : ℕ} (h : r < P.rowsS on s) :
    on s = true ∧ r < 2 ^ (P.seg s).rowsLog := by
  unfold LdPartD.rowsS at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact absurd h (Nat.not_lt_zero _)

omit [Fintype F] in
theorem ldPartNmOf_cols {on : ℕ → Bool} {s c : ℕ} (h : c < P.colsS on s) :
    on s = true ∧ c < (P.seg s).cols := by
  unfold LdPartD.colsS at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact absurd h (Nat.not_lt_zero _)

omit [Fintype F] in
/-- Under the hypotheses below, a row of a matrix at hand has its place: the test in `nmS` holds. -/
theorem ldPartNmOf_in {on : ℕ → Bool} {s r : ℕ} (hP : 0 < K.P) (hs : s < P.n)
    (hon : on s = true) (hr : r < 2 ^ (P.seg s).rowsLog) :
    s < P.n ∧ r / K.P < P.rpS K on s ∧ r % K.P < K.P := by
  refine ⟨hs, ?_, Nat.mod_lt _ hP⟩
  unfold LdPartD.rpS LdPartD.rp
  rw [if_pos hon, Nat.div_lt_iff_lt_mul hP]
  exact lt_of_lt_of_le hr (ldPartNmOf_ceil _ _ hP)

end

theorem ldPartNmOf_ok : Spec.ldPartNmOf_ok := by
  intro F E _ _ _ _ Cf P K on Rd U _ _ _ _ wd nd d0 hP hOn
  constructor
  · intro s r s' r' hr hr' e
    obtain ⟨o1, g1⟩ := ldPartNmOf_rows P hr
    obtain ⟨o2, g2⟩ := ldPartNmOf_rows P hr'
    have h1 := ldPartNmOf_in P K hP (hOn s o1).1 o1 g1
    have h2 := ldPartNmOf_in P K hP (hOn s' o2).1 o2 g2
    have e' : (if h : s < P.n ∧ r / K.P < P.rpS K on s ∧ r % K.P < K.P then
            ((⟨⟨s, h.1⟩, ⟨r / K.P, h.2.1⟩⟩, ⟨r % K.P, h.2.2⟩) : (P.parS K on Rd U wd nd).one.Row)
          else d0) =
        (if h : s' < P.n ∧ r' / K.P < P.rpS K on s' ∧ r' % K.P < K.P then
            ((⟨⟨s', h.1⟩, ⟨r' / K.P, h.2.1⟩⟩, ⟨r' % K.P, h.2.2⟩) : (P.parS K on Rd U wd nd).one.Row)
          else d0) := e
    rw [dif_pos h1, dif_pos h2] at e'
    have e1 : s = s' := congrArg (fun z : (P.parS K on Rd U wd nd).one.Row => (z.1.1 : ℕ)) e'
    have e2 : r / K.P = r' / K.P :=
      congrArg (fun z : (P.parS K on Rd U wd nd).one.Row => (z.1.2 : ℕ)) e'
    have e3 : r % K.P = r' % K.P :=
      congrArg (fun z : (P.parS K on Rd U wd nd).one.Row => (z.2 : ℕ)) e'
    refine ⟨e1, ?_⟩
    rw [← Nat.div_add_mod r K.P, ← Nat.div_add_mod r' K.P, e2, e3]
  · intro s c c' hc hc' e
    obtain ⟨o1, g1⟩ := ldPartNmOf_cols P hc
    obtain ⟨-, g2⟩ := ldPartNmOf_cols P hc'
    have hw := (hOn s o1).2
    have e1 : c % K.Cw = c' % K.Cw := congrArg (fun z : Fin K.Cw => (z : ℕ)) e
    rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le g1 hw), Nat.mod_eq_of_lt (lt_of_lt_of_le g2 hw)] at e1

theorem ldPartNmOf_on : Spec.ldPartNmOf_on := by
  intro F E _ _ _ _ Cf P p k hPr hk
  refine ⟨fun s h => ?_, fun s h => ?_, fun s h => ?_⟩
  · unfold LdPartD.onBody at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · exact hk
    · cases k with
      | zero => exact absurd hq (Finset.notMem_empty _)
      | succ k => exact (hPr.keptIn k q hq).2.1
  · unfold LdPartD.onKept at h
    rw [decide_eq_true_eq] at h
    obtain ⟨q, hq, rfl⟩ := h
    exact (hPr.keptIn k q hq).2.1
  · unfold LdPartD.onKept at h
    unfold LdPartD.onBody
    rw [decide_eq_true_eq] at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact Or.inr h

theorem ldPartNmOf_shape : Spec.ldPartNmOf_shape := by
  intro F E _ _ _ _ Cf P p k hPr hk q hq
  obtain ⟨hle, h1, h2, h3⟩ := hPr.reads k hk q hq
  have hon : P.onBody k q.1 = true := by
    unfold LdPartD.onBody
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      cases k with
      | zero => exact absurd h (Nat.not_lt_zero _)
      | succ k =>
        exact ⟨(q.1, q.2.1),
          hPr.keeps (k + 1) hk q hq k (Nat.lt_succ_iff.1 h) (Nat.lt_succ_self k),
          rfl⟩
  refine ⟨h1, ?_, ?_⟩
  · unfold LdPartD.rowsS
    rw [if_pos hon]
    exact h2
  · unfold LdPartD.colsS
    rw [if_pos hon]
    exact h3

theorem ldPartNmOf_reading : Spec.ldPartNmOf_reading := fun F E _ _ _ _ Cf P p k hPr hk v g h =>
  ldPartRead_byCol E P.n _ _ v g fun b hb t ht =>
    ldPartNmOf_shape F E Cf P p k hPr hk t.2 (h b hb t ht)

theorem ldPartNmOf_ties :
    Spec.ldPartNmOf_ties := fun _ E _ _ _ _ _ P K on _ _ v f U _ _ _ wd nd St J pt β val cAt d0 =>
  ldPartCells_stdW _ E St J (P.nmS K on (P.ReadsS on v f) U wd nd d0)
    (P.clS K on v f U wd nd pt β val cAt) id fun _ _ => rfl

end Cb
