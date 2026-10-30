-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartNmTieProofs.lean: the proofs of the statements of Cb/Part/LdPartNmTie.lean. Under the
hypotheses of the statements, the namings of a partition's bodies and kept messages (`P.nmS`,
Cb/Part/LdPartNmOf.lean) meet the clauses on namings of the ties between stages (which clauses: the
head of Cb/Part/LdPartNmTie.lean).

By unfolding the standard order (row r in the packed row (s, r / K.P), lane r mod K.P); the
partition's laws `keptIn`, `keptStep`. Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs. Many statements of this library are written twice: a
definition in the namespace `Spec` states a proposition, and a theorem of the same name outside that
namespace proves it (lean/GLOSSARY.md).

Limits: what the head of Cb/Part/LdPartNmTie.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartNmTie
import Cb.Part.LdPartNmOfProofs

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

omit [Fintype F] in
/-- Where a row of a matrix at hand is: under the hypotheses below, `rowAt s r` of the naming
`P.nmS K on ..` is ((s, r / K.P), r mod K.P). -/
theorem ldPartNmTie_rowAt [NeZero K.Cw] (on : ℕ → Bool) (Rd U : Type) [Fintype Rd] [Fintype U]
    [DecidableEq U] (wd nd : ℕ) (d0 : (P.parS K on Rd U wd nd).one.Row) {s r : ℕ}
    (h : s < P.n ∧ r / K.P < P.rpS K on s ∧ r % K.P < K.P) :
    (P.nmS K on Rd U wd nd d0).rowAt s r = (⟨⟨s, h.1⟩, ⟨r / K.P, h.2.1⟩⟩, ⟨r % K.P, h.2.2⟩) :=
  dif_pos h

omit [Fintype F] in
/-- A segment with a packed row is at hand (`on s = true`). -/
theorem ldPartNmTie_pos {on : ℕ → Bool} {s : ℕ} (i : Fin (P.rpS K on s)) : on s = true := by
  by_contra hn
  have h0 : P.rpS K on s = 0 := by
    unfold LdPartD.rpS
    rw [if_neg hn]
  have h1 : (i : ℕ) < 0 := lt_of_lt_of_le i.2 (le_of_eq h0)
  exact absurd h1 (Nat.not_lt_zero _)

end

theorem ldPartNmTie_part : Spec.ldPartNmTie_part := by
  intro F E _ _ _ _ Cf P K _ on₀ on₁ Rd₀ U₀ Rd₁ U₁ _ _ _ _ _ _ wd₀ nd₀ wd₁ nd₁ d₀ d₁ h hP hOn
  refine ⟨?_, fun _ _ e => e, ?_, ?_, ?_⟩
  · rintro ⟨s, i⟩ ⟨s', i'⟩ e
    have e1 : s = s' := congrArg Sigma.fst e
    subst e1
    have e2 : Fin.castLE (P.rpS_mono K h s) i = Fin.castLE (P.rpS_mono K h s) i' :=
      eq_of_heq (Sigma.mk.inj e).2
    rw [show i = i' from Fin.ext (congrArg (fun z : Fin (P.rpS K on₁ s) => (z : ℕ)) e2)]
  · intro s r hr
    obtain ⟨o0, g⟩ := ldPartNmOf_rows P hr
    have i0 := ldPartNmOf_in P K hP (hOn s (h s o0)) o0 g
    have i1 := ldPartNmOf_in P K hP (hOn s (h s o0)) (h s o0) g
    refine ⟨?_, ?_, ?_⟩
    · show r < P.rowsS on₁ s
      unfold LdPartD.rowsS
      rw [if_pos (h s o0)]
      exact g
    · rw [ldPartNmTie_rowAt P K on₁ Rd₁ U₁ wd₁ nd₁ d₁ i1,
        ldPartNmTie_rowAt P K on₀ Rd₀ U₀ wd₀ nd₀ d₀ i0]
      rfl
    · rw [ldPartNmTie_rowAt P K on₁ Rd₁ U₁ wd₁ nd₁ d₁ i1,
        ldPartNmTie_rowAt P K on₀ Rd₀ U₀ wd₀ nd₀ d₀ i0]
  · intro s hs
    obtain ⟨o0, -⟩ := ldPartNmOf_rows P hs
    refine ⟨?_, fun _ _ => rfl⟩
    show P.colsS on₀ s = P.colsS on₁ s
    unfold LdPartD.colsS
    rw [if_pos o0, if_pos (h s o0)]
  · intro s r i hr e
    obtain ⟨o1, g⟩ := ldPartNmOf_rows P hr
    have i1 := ldPartNmOf_in P K hP (hOn s o1) o1 g
    rw [ldPartNmTie_rowAt P K on₁ Rd₁ U₁ wd₁ nd₁ d₁ i1] at e
    have e1 : s = (i.1 : ℕ) := congrArg (fun z : Σ s : Fin P.n, Fin (P.rpS K on₁ s) => (z.1 : ℕ)) e
    have o0 : on₀ s = true := by
      rw [e1]
      exact ldPartNmTie_pos P K i.2
    show r < P.rowsS on₀ s
    unfold LdPartD.rowsS
    rw [if_pos o0]
    exact g

theorem ldPartNmTie_own : Spec.ldPartNmTie_own := by
  intro F E _ _ _ _ Cf P K _ on Rd U _ _ _ wd nd d0 j hj hon hP hOn hw
  refine ⟨?_, fun _ _ e => e, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b e
    have e2 : Fin.cast (P.rpS_on K hon) a = Fin.cast (P.rpS_on K hon) b :=
      eq_of_heq (Sigma.mk.inj e).2
    exact Fin.ext (congrArg (fun z : Fin (P.rpS K on j) => (z : ℕ)) e2)
  · show P.rowsS on j = _
    unfold LdPartD.rowsS
    rw [if_pos hon]
  · show P.colsS on j = _
    unfold LdPartD.colsS
    rw [if_pos hon]
  · intro r hr
    have i1 := ldPartNmOf_in P K hP hj hon hr
    refine ⟨⟨r / K.P, by rw [P.rpS_on K hon]; exact i1.2.1⟩, rfl, ?_, ?_⟩
    · rw [ldPartNmTie_rowAt P K on Rd U wd nd d0 i1]
      rfl
    · rw [ldPartNmTie_rowAt P K on Rd U wd nd d0 i1]
  · intro c hc
    exact ⟨⟨c, lt_of_lt_of_le hc hw⟩, rfl, Fin.ext (Nat.mod_eq_of_lt (lt_of_lt_of_le hc hw))⟩
  · intro s r i hr e
    obtain ⟨o1, g⟩ := ldPartNmOf_rows P hr
    have i1 := ldPartNmOf_in P K hP (hOn s o1) o1 g
    rw [ldPartNmTie_rowAt P K on Rd U wd nd d0 i1] at e
    exact congrArg (fun z : Σ s : Fin P.n, Fin (P.rpS K on s) => (z.1 : ℕ)) e

theorem ldPartNmTie_cover : Spec.ldPartNmTie_cover := by
  intro F E _ _ _ _ Cf P K on₀ on₁ h j hj hon hc i c
  obtain ⟨⟨s, hs⟩, i⟩ := i
  have o1 : on₁ s = true := ldPartNmTie_pos P K i
  rcases hc s o1 with e | o0
  · subst e
    exact Or.inr ⟨Fin.cast (P.rpS_on K hon).symm i, c, rfl, rfl⟩
  · have e0 : P.rpS K on₁ s = P.rpS K on₀ s := by
      unfold LdPartD.rpS
      rw [if_pos o1, if_pos o0]
    exact Or.inl ⟨⟨⟨s, hs⟩, Fin.cast e0 i⟩, c, rfl, rfl⟩

theorem ldPartNmTie_alone : Spec.ldPartNmTie_alone := by
  intro F E _ _ _ _ Cf P K on j hj hon hc i c
  obtain ⟨⟨s, hs⟩, i⟩ := i
  have e := hc s (ldPartNmTie_pos P K i)
  subst e
  exact ⟨Fin.cast (P.rpS_on K hon).symm i, c, rfl, rfl⟩

theorem ldPartNmTie_sets : Spec.ldPartNmTie_sets := by
  intro F E _ _ _ _ Cf P p hPr
  refine ⟨fun k s h => ?_, fun k s h => ?_, fun s h => ?_, fun k => ?_⟩
  · unfold LdPartD.onKept at h
    unfold LdPartD.onBody
    rw [decide_eq_true_eq] at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    obtain ⟨q, hq, rfl⟩ := h
    cases k with
    | zero => exact Or.inl (Nat.le_zero.1 (hPr.keptIn 0 q hq).1)
    | succ k =>
      rcases hPr.keptStep k q hq with e | hq'
      · exact Or.inl e
      · exact Or.inr ⟨q, hq', rfl⟩
  · unfold LdPartD.onBody at h
    unfold LdPartD.onKept
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rw [decide_eq_true_eq]
    exact h
  · unfold LdPartD.onBody at h
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    rcases h with e | ⟨q, hq, -⟩
    · exact e
    · exact absurd hq (Finset.notMem_empty _)
  · unfold LdPartD.onBody
    rw [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl rfl

theorem ldPartNmTie_named : Spec.ldPartNmTie_named := by
  intro F E _ _ _ _ Cf P p k hPr q hq
  have o : P.onKept k q.1 = true := by
    unfold LdPartD.onKept
    rw [decide_eq_true_eq]
    exact ⟨q, hq, rfl⟩
  unfold LdPartD.rowsS LdPartD.colsS
  rw [if_pos o, if_pos o]
  exact ⟨(hPr.keptIn k q hq).2.2, rfl⟩

end Cb
