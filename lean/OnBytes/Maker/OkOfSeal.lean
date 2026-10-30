-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfSeal.lean: a sealed round in a description that passes the format's own test;
and the makers' test `runFit` (OnBytes/Maker/WholeOf.lean) from the openings of the three lists of
rounds.

Main names:
  `seal_of_roundsOk`, `partsFrom_le`: steps.
  `seal_fields`: a round of the kind "sealed" of a description that passes `Fmt.SpecX.ok`
    (Fmt/Rules8X.lean) opens nothing, sends no root, has no stored table, and draws no element,
    position or matrix entry: seven of the ten fields that the sixth clause of `Three.Whole.fits`
    (OnBytes/Three/Data.lean) asks of a chain's last round.
  `trees_plain`, `runFit_of_opens`: no tree of the data bears the mark "stored", if no opening of
    the three lists does.

Limits: that a round is of the kind "sealed" and that its message has no item do not follow from the
format's test, as far as the writer sees: they are not shown. That a sealed round asks for no work
does follow from that test (`Fmt.Round.ok_sealed_work`, Fmt/Rules8Ok.lean; the format page's rule
R5.3); it is not among the fields shown here. Nothing on which rounds a chain has. Nothing on
soundness.
-/
import OnBytes.Maker.OkOfNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-! ### A sealed round in a description that passes the format's test -/

theorem seal_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true →
      ∀ r ∈ rs, r.kind = .sealed → r.entry.roots = 0 ∧ (r.opens = [] ∨ 0 < r.entry.poss)
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · intro hk
      have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        decide_eq_true_eq, List.isEmpty_iff] at h1
      refine ⟨?_, by tauto⟩
      have h2 : x.entry.roots = 0 ∨ ((¬ x.kind = .nothing ∧ ¬ x.kind = .sealed) ∧
          (!noRand) = true) := by tauto
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd hk h2.1.2
    · exact seal_of_roundsOk P noRand firstTree rs _ _ h.2 x hx'

/-- The number behind the last part is not below the number from which the parts are counted. -/
theorem partsFrom_le : ∀ (ts : List Fmt.Stored) (i k : ℕ), Fmt.partsFrom i ts = some k → i ≤ k
  | [], i, k, h => by
    have e : some i = some k := h
    exact le_of_eq (Option.some.inj e)
  | t :: ts, i, k, h => by
    unfold Fmt.partsFrom at h
    split at h
    · exact le_trans (Nat.le_add_right _ _) (partsFrom_le ts _ k h)
    · cases h

/-- **A sealed round of a description that passes the format's test** opens nothing, sends no root,
has no stored table and draws no element, position or matrix entry. -/
theorem seal_fields {S : Fmt.SpecX} (h : S.ok = true) (x : Fmt.Round × List Fmt.Stored)
    (hx : x ∈ S.base.rounds.zip S.stored) (hk : x.1.kind = .sealed) :
    x.1.opens = [] ∧ x.1.entry.roots = 0 ∧ x.2 = [] ∧ x.1.entry.drawE = 0 ∧
      x.1.entry.drawNZ = 0 ∧ x.1.entry.poss = 0 ∧ x.1.entry.trits = 0 := by
  have hb := base_ok h
  have hm : x.1 ∈ S.base.rounds := (List.of_mem_zip hx).1
  have hf : x.1.entry.fits x.1.kind S.base.plan.samples = true := by
    have h0 := hb
    unfold Fmt.Spec.ok at h0
    simp only [Bool.and_eq_true] at h0
    have h1 : (S.base.rounds.all fun r => r.entry.fits r.kind S.base.plan.samples) = true := by
      tauto
    exact List.all_eq_true.1 h1 x.1 hm
  rw [hk] at hf
  simp only [Fmt.Entry.fits, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := hf
  have hr : x.1.entry.roots = 0 ∧ (x.1.opens = [] ∨ 0 < x.1.entry.poss) := by
    have h0 := hb
    unfold Fmt.Spec.ok at h0
    simp only [Bool.and_eq_true] at h0
    exact seal_of_roundsOk _ _ _ S.base.rounds _ _ h0.1.1.2 x.1 hm hk
  have hs : x.2 = [] := by
    have h0 := h
    unfold Fmt.SpecX.ok at h0
    simp only [Bool.and_eq_true, List.all_eq_true] at h0
    have h1 := h0.2 x hx
    unfold Fmt.storedOk at h1
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq,
      List.all_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · cases hx2 : x.2 with
      | nil => rfl
      | cons t ts =>
        exfalso
        have hp : Fmt.partsFrom 0 x.2 = some x.1.entry.poss := h1.1.2
        have hc : 1 ≤ t.count := (h1.2 t (by rw [hx2]; exact List.mem_cons_self ..)).2
        rw [hx2, f1] at hp
        unfold Fmt.partsFrom at hp
        split at hp
        · have := partsFrom_le ts _ _ hp
          omega
        · cases hp
  exact ⟨hr.2.resolve_right (by omega), hr.1, hs, f3, f4, f1, f2⟩

/-! ### `runFit` from the openings -/

section Data
variable (a : ℕ) (R₁ R₂ R₃ : Rounds)

/-- Every tree of a chain's data is unmarked, if all openings of the file are. -/
theorem trees_plain (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (hall : ∀ x ∈ all, x.2.1.stored = false)
    (t₁ t₂ here base first : ℕ) (R : Rounds) :
    ∀ d ∈ Three.rdsFromL all t₁ t₂ here base first R, ∀ s ∈ d.trees, s.stored = false := by
  intro d hd s hs
  unfold Three.rdsFromL at hd
  obtain ⟨r, k, rfl⟩ := mem_zipWith' _ _ _ _ hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
  rcases shapeAt_mem all (base + k + i) (Three.bareShape first (k + i)) with e | ⟨x, hx, e⟩
  · rw [e]
    rfl
  · rw [e]
    exact hall x hx

/-- **`runFit` from the openings of the three lists.** -/
theorem runFit_of_opens (h₁ : ∀ r ∈ R₁, ∀ o ∈ r.1.opens, o.1.stored = false)
    (h₂ : ∀ r ∈ R₂, ∀ o ∈ r.1.opens, o.1.stored = false)
    (h₃ : ∀ r ∈ R₃, ∀ o ∈ r.1.opens, o.1.stored = false) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).runFit = true := by
  have hall : ∀ x ∈ (Three.Whole.of R₁ R₂ R₃).opens, x.2.1.stored = false := by
    intro x hx
    have hx' : x ∈ Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 0 R₁ ++
        (Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 1 R₂ ++
          Three.opensOf (Three.rootsIn R₁) (Three.rootsIn R₂) 2 R₃) := hx
    rcases List.mem_append.1 hx' with h | h
    · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
      exact e ▸ h₁ r hr o ho
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
        exact e ▸ h₂ r hr o ho
      · obtain ⟨r, hr, o, ho, e⟩ := opensOf_mem _ _ _ _ x h
        exact e ▸ h₃ r hr o ho
  unfold WholeD.runFit
  simp only [List.all_eq_true, Bool.not_eq_true', List.mem_append]
  rintro d (hd | hd | hd) s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_plain _ hall _ _ _ _ _ R₁ x (List.mem_of_mem_dropLast hx) s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_plain _ hall _ _ _ _ _ R₂ x hx s hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    exact trees_plain _ hall _ _ _ _ _ R₃ x hx s hs

end Data

end OnBytes.Maker

#print axioms OnBytes.Maker.seal_fields
#print axioms OnBytes.Maker.runFit_of_opens
