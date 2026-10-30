-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfFormat.lean: some of the makers' tests on three lists of rounds (`okAt`,
OnBytes/Maker/Files.lean) follow from the format's own test on a chain's description (`Fmt.Spec.ok`,
Fmt/Rules8.lean), or from each other.

Why. Where `okAt` says no, a file's reduction stands at three empty chains and accepts nothing. So
a statement "the program's yes gives the typed verifier's yes" needs `okAt`'s yes. The program's
reader of a chain returns nothing unless the chain's description passes the format's own test
(`readChain_read`, OnBytes/Maker/ReadFacts.lean). So where the program has said yes, that test has
passed at the three descriptions, whose rounds are the three lists.

Main names:
  `roots_of_roundsOk`, `roots_of_ok`: in a description that passes the format's test every round's
    message has as many items "root" as its entry says.
  `sum_dropLast`: a list of numbers whose last is 0 has the sum of the list without it.
  `seal_of_fits`: under `Three.Whole.fits` the first list has a last round, and it has no item.
  `countsFit_of_fits`: `countsFit` follows from `Three.Whole.fits`.

Limits: two of the tests' clauses alone. Nothing on the other tests. No list of rounds is shown to
pass any test. Nothing on soundness.
-/
import OnBytes.Maker.Files
import OnBytes.Maker.ReadData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Params (Rounds)

/-- Every round of a list that passes the format's test on rounds has as many items "root" as its
entry says. -/
theorem roots_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true →
      ∀ r ∈ rs, r.items.countP (· == .root) = r.entry.roots
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      have h2 : Fmt.countItem .root x.items = x.entry.roots := by tauto
      rw [← h2, Fmt.countItem, List.countP_eq_length_filter]
    · exact roots_of_roundsOk P noRand firstTree rs _ _ h.2 x hx'

/-- The same of a description that passes the format's test. -/
theorem roots_of_ok {S : Fmt.Spec} (h : S.ok = true) :
    ∀ r ∈ S.rounds, r.items.countP (· == .root) = r.entry.roots := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  exact roots_of_roundsOk _ _ _ S.rounds _ _ h.1.1.2

/-- A list of numbers whose last is 0 has the sum of the list without it. -/
theorem sum_dropLast (l : List ℕ) (h : l.getLast? = some 0) : l.dropLast.sum = l.sum := by
  have e : l = l.dropLast ++ [0] := (List.dropLast_append_getLast? 0 h).symm
  conv_rhs => rw [e]
  simp

/-- Under the test on the limits of the map the first list has a last round, which has no item. -/
theorem seal_of_fits {R₁ R₂ R₃ : Rounds} {n : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ n = true) :
    ∃ r, R₁.getLast? = some r ∧ r.1.items = [] := by
  simp only [Three.Whole.fits, Bool.and_eq_true] at h
  obtain ⟨⟨_, h5⟩, _⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h5
  have h1 := h5.1
  cases hr : R₁.getLast? with
  | none => rw [hr] at h1; cases h1
  | some r =>
    rw [hr] at h1
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h1
    exact ⟨r, rfl, by tauto⟩

/-- **`countsFit` follows from `Three.Whole.fits`**: the data's first list is the rounds' without
the last, which sends no root. -/
theorem countsFit_of_fits (a : ℕ) {R₁ R₂ R₃ : Rounds} {n : ℕ}
    (h : Three.Whole.fits R₁ R₂ R₃ n = true) :
    countsFit a (Three.Whole.of R₁ R₂ R₃) = true := by
  obtain ⟨r, hr, hi⟩ := seal_of_fits h
  have len : ∀ (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) (R : Rounds),
      (Three.rdsFromL all t₁ t₂ here base first R).map (·.trees.length) =
        R.map fun r => r.1.items.countP (· == .root) := fun all t₁ t₂ here base first R =>
    rdsFromL_map all t₁ t₂ here base first _ _ (fun r n => by
      show ((List.range (r.1.items.countP (· == .root))).map _).length = _
      rw [List.length_map, List.length_range]) R
  have e₂ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₂ = Three.rootsIn R₂ := by
    show (((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf).map (·.trees.length)).sum = _
    rw [List.map_map]
    exact congrArg List.sum (len _ _ _ _ _ _ R₂)
  have e₁ : (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).t₁ = Three.rootsIn R₁ := by
    show (((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf).map (·.trees.length)).sum = _
    rw [List.map_map, List.map_dropLast]
    have e := len (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁) (Three.rootsIn R₂) 0 0 0 R₁
    have e' : (Three.Whole.of R₁ R₂ R₃).ds₁.map ((·.trees.length) ∘ rdtOf) =
        R₁.map fun r => r.1.items.countP (· == .root) := e
    rw [e']
    refine sum_dropLast _ ?_
    rw [List.getLast?_map, hr]
    show some (r.1.items.countP (· == .root)) = some 0
    rw [hi]
    rfl
  unfold countsFit
  rw [e₁, e₂]
  show (Three.rootsIn R₁ == Three.rootsIn R₁ && Three.rootsIn R₂ == Three.rootsIn R₂) = true
  simp

end OnBytes.Maker

#print axioms OnBytes.Maker.roots_of_ok
#print axioms OnBytes.Maker.countsFit_of_fits
