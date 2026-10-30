-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/PartLaw.lean: what a stretch of rounds that `play` has played
adds to what has been produced (Honest/Law/Rule/Session.lean: `Laid.add`), in the form in which a
session produces a stretch; and small lemmas on `Laid`.

  1  `fits_len`, `play_shape`   a round as played has as many tables as its `Step` declares oracle
     messages, and the challenge that `play` was given for it
  2  `pairsBy`, `shownBy_pairs`, `pairsBy_append`, `pairs_zip`, `shows_pairs`   what rounds as
     played show, each with its challenge; `shownOf` at the positions of `asksFrom`, zipped with the
     challenges
  3  `Laid.add_nil`, `Laid.add_add`, `Laid.of_add`, `Laid.seen_add`   what has been produced, over
     two stretches

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Faith
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place Oracle)

variable {W X : Type}

/-! ## 1 A round as played -/

theorem fits_len {x : Sending} {d : Fmt.DeclaredRound} {os : List Oracle} (h : x.fits d os = true) :
    x.tables.length = os.length := by
  unfold Sending.fits at h
  rw [Bool.and_eq_true] at h
  have := congrArg List.length (beq_iff_eq.1 h.2)
  simpa using this

/-- At `Step`s each of which declares as many oracle messages as its entry counts roots. -/
theorem play_shape : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y →
    (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    y.1.map (·.tables.length) = ss.map (·.oracles.length) ∧ y.1.map (·.drawn) = ds
  | [], [], _, m, y, h, _ => by
    simp only [play] at h
    cases h
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, h, _ => by simp [play] at h
  | _ :: _, [], _, _, _, h, _ => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h, hs => by
    obtain ⟨x, m', z, hx, -, hz, rfl⟩ := play_cons_ok h
    obtain ⟨e1, e2⟩ := play_shape ss ds back.tail m' z hz fun t ht =>
      hs t (List.mem_cons_of_mem _ ht)
    obtain ⟨-, t2, t3⟩ := tell_yields hx
    have hl : x.tables.length = s.oracles.length := by
      cases hm : s.move.isSome with
      | true =>
        obtain ⟨w, hf, -, ht⟩ := t2 hm
        rw [ht, List.length_map, fits_len hf]
      | false =>
        rw [(t3 hm).2, List.length_replicate, hs s (List.mem_cons.2 (Or.inl rfl))]
    refine ⟨?_, ?_⟩
    · show x.tables.length :: z.1.map (·.tables.length) =
        s.oracles.length :: ss.map (·.oracles.length)
      rw [hl, e1]
    · show d :: z.1.map (·.drawn) = d :: ds
      rw [e2]

/-! ## 2 What rounds as played show, each with its challenge -/

/- What rounds as played show, each with its challenge. `tree`: the positions read of a tree, by its
number in the chain. The `Nat`: the number of the first round's first tree. -/
def pairsBy (tree : Nat → List Nat) : List Played → Nat → List (Shown × Fmt.Drawn)
  | [], _ => []
  | p :: ps, n => (p.shownBy tree n, p.drawn) :: pairsBy tree ps (n + p.tables.length)

theorem shownBy_pairs (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    shownBy ch tree l n = (pairsBy tree l n).map fun z => (ch, z.1, z.2)
  | [], _ => rfl
  | p :: l, n => congrArg ((ch, p.shownBy tree n, p.drawn) :: ·)
    (shownBy_pairs ch tree l (n + p.tables.length))

theorem pairsBy_append (tree : Nat → List Nat) (l₂ : List Played) :
    ∀ (l₁ : List Played) (n : Nat), pairsBy tree (l₁ ++ l₂) n =
      pairsBy tree l₁ n ++ pairsBy tree l₂ (n + (l₁.map (·.tables.length)).sum)
  | [], n => by simp [pairsBy]
  | p :: l₁, n => by
    have ih := pairsBy_append tree l₂ l₁ (n + p.tables.length)
    simp only [List.cons_append, pairsBy, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem pairs_zip (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    ((shownBy ch tree l n).map (·.2.1)).zip (l.map (·.drawn)) = pairsBy tree l n
  | [], _ => rfl
  | p :: l, n => congrArg ((p.shownBy tree n, p.drawn) :: ·)
    (pairs_zip ch tree l (n + p.tables.length))

/-- **`shownOf` at the positions of `asksFrom`, zipped with the challenges.** `roots`: each round's
number of tables. -/
theorem shows_pairs (tree : Nat → List Nat) (l : List Played) (n : Nat) (roots : List Nat)
    (ds : List Fmt.Drawn) (h1 : l.map (·.tables.length) = roots) (h2 : l.map (·.drawn) = ds) :
    (shownOf l (asksFrom tree roots n)).zip ds = pairsBy tree l n := by
  subst h1
  subst h2
  rw [← shownOf_by 0 tree l n]
  exact pairs_zip 0 tree l n

/-! ## 3 What has been produced -/

theorem Laid.add_nil (L : Laid) (ch : Nat) : L.add ch [] = L := by
  unfold Laid.add
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

theorem Laid.add_add (L : Laid) (ch : Nat) (a b : List (Shown × Fmt.Drawn)) :
    (L.add ch a).add ch b = L.add ch (a ++ b) := by
  unfold Laid.add
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

theorem Laid.of_add (L : Laid) (ch : Nat) (a : List (Shown × Fmt.Drawn)) :
    (L.add ch a).of ch = L.of ch ++ a.map fun z => (ch, z.1, z.2) := by
  unfold Laid.add Laid.of
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

/-- What a part of the chain is given as shown, after one more stretch. -/
theorem Laid.seen_add (L : Laid) (ch : Nat) (st : List (Nat × Nat × List UInt64))
    (a : List (Shown × Fmt.Drawn)) :
    ((L.add ch a).front ch st).seen =
      (L.front ch st).seen ++ a.map fun z => (⟨z.1.vals, z.2⟩ : Fmt.RoundView) := by
  unfold Laid.add Laid.front Before.seen
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

end ProofFile.Honest

#print axioms ProofFile.Honest.fits_len
#print axioms ProofFile.Honest.play_shape
#print axioms ProofFile.Honest.shownBy_pairs
#print axioms ProofFile.Honest.pairsBy_append
#print axioms ProofFile.Honest.pairs_zip
#print axioms ProofFile.Honest.shows_pairs
#print axioms ProofFile.Honest.Laid.add_nil
#print axioms ProofFile.Honest.Laid.add_add
#print axioms ProofFile.Honest.Laid.of_add
#print axioms ProofFile.Honest.Laid.seen_add
