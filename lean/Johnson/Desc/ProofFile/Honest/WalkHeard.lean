-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/WalkHeard.lean: what the walk's state has heard: where the prover's
run is still played, the challenges that its state has heard are those that the chain's start state
had heard, and then the challenges of the rounds produced so far, in their order. There are two ways
of naming a round's challenges: `FieldAt` (Field.lean) takes them off the state (`m.st.heard.drop
skip`), the laws on a walk's columns off the rounds produced (`z.laid.map (·.drawn)`).
`walk_heard_drop` says that the two lists are one, where `skip` is the number of challenges that the
start had heard; no statement of this file names `FieldAt`.

  `ChainProgress.Hears`   the invariant
  `settle_hears`, `start_hears`, `heard_hears`, `walk_hears`   it holds from a chain's start on
  `walk_heard_drop`   so, behind the start's challenges, the state has heard just those of the
     rounds produced
  `start_laid`, `walk_laid_length`   a walk from a chain's start has produced as many rounds as it
     has taken steps (by `settle_laid` and `heard_laid`, Law/WalkOn.lean)
  `walk_laid_drawn`   the challenges of the rounds that a walk produces are the walk's challenges
     (`walk_shows`, Honest/Law/CoverLocal.lean, which stands above this file, is the same statement)

The four proofs follow those of `settle_inv`, `start_inv`, `heard_inv`, `walk_inv`
(WalkOpened.lean).

Limits.
  * It says nothing after a rejection: there the walk has no state.
  * Nothing on whether a walk returns.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.WalkOpened
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.WalkOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl W Y : Type}

/-- Where the run is still played, its state has heard `h₀` and then the challenges of the rounds
produced so far. -/
def ChainProgress.Hears (h₀ : List Fmt.Drawn) (z : ChainProgress S Cl W Y) : Prop :=
  ∀ m, z.mid = some m → m.st.heard = h₀ ++ z.laid.map (·.drawn)

theorem settle_hears (L : Lay) (h₀ : List Fmt.Drawn) : ∀ (bs : List (Block S Cl))
    (z z' : ChainProgress S Cl W Y), z.Hears h₀ → ChainProgress.settle L bs z = .ok z' → z'.Hears h₀
  | [], z, z', hz, h => by
    rw [ChainProgress.settle] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | b :: bs, z, z', hz, h => by
    rw [ChainProgress.settle] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hz
    · obtain ⟨cols, -, h⟩ := of_bind_ok h
      refine settle_hears L h₀ bs _ z' ?_ h
      intro m hm
      cases hzm : z.mid with
      | none =>
        simp [hzm] at hm
      | some m₀ =>
        have h0 := hz m₀ hzm
        split at hm
        · rw [hzm] at hm
          obtain rfl : m₀.took cols = m := Option.some.inj hm
          exact h0
        · cases hm

theorem start_hears {L : Lay} {bs : List (Block S Cl)} {m₀ : Mid W Y} {v : Option S}
    {front : List OpenedColumn} {z : ChainProgress S Cl W Y} (h : ChainProgress.start L bs (some m₀) v front = .ok z) :
    z.Hears m₀.st.heard := by
  refine settle_hears L _ bs _ z ?_ h
  intro m' hm
  split at hm
  · obtain rfl := Option.some.inj hm
    exact (List.append_nil _).symm
  · cases hm

theorem heard_hears {L : Lay} {h₀ : List Fmt.Drawn} {z z' : ChainProgress S Cl W Y} {s : Step W Y}
    {x : Told} {d : Fmt.Drawn} (hz : z.Hears h₀) (h : z.heard L s x d = .ok z') :
    z'.Hears h₀ := by
  unfold ChainProgress.heard at h
  obtain ⟨m', hm', h⟩ := of_bind_ok h
  refine settle_hears L h₀ _ _ z' ?_ h
  intro m hm
  have hm2 : m' = some m := hm
  subst hm2
  cases hzm : z.mid with
  | none =>
    rw [hzm] at hm'
    cases hm'
  | some m₀ =>
    rw [hzm] at hm'
    obtain ⟨m₁, h1, e⟩ := map_ok hm'
    obtain rfl := Option.some.inj e
    show m₁.st.heard = h₀ ++ List.map Played.drawn (z.laid ++ [_])
    rw [hear_heard h1, hz m₀ hzm, List.map_append, List.append_assoc]
    rfl

theorem walk_hears (L : Lay) (h₀ : List Fmt.Drawn) : ∀ (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), z.Hears h₀ → walk L ss ds z = .ok z' →
    z'.Hears h₀
  | [], [], z, z', hz, h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | s :: ss, d :: ds, z, z', hz, h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    exact walk_hears L h₀ ss ds z₁ z' (heard_hears hz h1) h
  | [], _ :: _, _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, _, h => by simp [walk] at h

/-- **Behind the start's challenges, the walk's state has heard just those of the rounds
produced.** -/
theorem walk_heard_drop {L : Lay} {bs : List (Block S Cl)} {m₀ m : Mid W Y} {v : Option S}
    {front : List OpenedColumn} {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    (ha : ChainProgress.start L bs (some m₀) v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hm : z.mid = some m) :
    m₀.st.heard.length ≤ m.st.heard.length ∧
      m.st.heard.drop m₀.st.heard.length = z.laid.map (·.drawn) := by
  have h := walk_hears L _ ss ds a z (start_hears ha) hz m hm
  rw [h]
  exact ⟨by rw [List.length_append]; omega, List.drop_left⟩

/-! ## How many rounds have been produced -/

theorem start_laid {L : Lay} {bs : List (Block S Cl)} {m : Option (Mid W Y)} {v : Option S}
    {front : List OpenedColumn} {z : ChainProgress S Cl W Y} (h : ChainProgress.start L bs m v front = .ok z) :
    z.laid = [] :=
  settle_laid L bs _ z h

theorem walk_laid_length (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' → z'.laid.length = z.laid.length + ss.length
  | [], [], z, z', h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    rfl
  | s :: ss, d :: ds, z, z', h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    rw [walk_laid_length L ss ds z₁ z' h, heard_laid h1]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h

/-- The challenges of the rounds that a walk produces are the walk's challenges. -/
theorem walk_laid_drawn (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' →
    z'.laid.map (·.drawn) = z.laid.map (·.drawn) ++ ds
  | [], [], z, z', h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    simp
  | s :: ss, d :: ds, z, z', h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    rw [walk_laid_drawn L ss ds z₁ z' h, heard_laid h1, List.map_append, List.append_assoc]
    rfl
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h

end ProofFile.Honest

#print axioms ProofFile.Honest.settle_hears
#print axioms ProofFile.Honest.start_hears
#print axioms ProofFile.Honest.heard_hears
#print axioms ProofFile.Honest.walk_hears
#print axioms ProofFile.Honest.walk_heard_drop
#print axioms ProofFile.Honest.start_laid
#print axioms ProofFile.Honest.walk_laid_length
#print axioms ProofFile.Honest.walk_laid_drawn
#print axioms ProofFile.Honest.ChainProgress.Hears
