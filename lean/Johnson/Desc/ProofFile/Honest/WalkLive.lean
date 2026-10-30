-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/WalkLive.lean: where a walk has a state of the prover's run, it had
one before: after a round, after a walk, and at a chain's start: there both the state and the
verifier's state that `ChainProgress.start` (Walk.lean) was handed were present. The second chain's start
takes two optional states.

  `heard_live`, `walk_live`   a state after a round, after a walk: a state before it
  `start_live`   a state at a chain's start: both optional arguments were `some`

By what, of others: `settle_same` (GapSame.lean).

Limits.
  * Nothing on which state.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.GapSame
import Johnson.Desc.ProofFile.Honest.WalkOpened
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl W Y : Type}

theorem heard_live {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    {m' : Mid W Y} (h : z.heard L s x d = .ok z') (hm : z'.mid = some m') :
    z.mid.isSome = true := by
  unfold ChainProgress.heard at h
  obtain ⟨o, ho, h⟩ := of_bind_ok h
  obtain ⟨m, _, e, -⟩ := settle_same L _ _ z' m' h hm
  have e' : o = some m := e
  cases hz : z.mid with
  | some _ => rfl
  | none =>
    rw [hz] at ho
    have ho' : (none : Option (Mid W Y)) = o := Except.ok.inj ho
    rw [e'] at ho'
    cases ho'

theorem walk_live (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (m' : Mid W Y), walk L ss ds z = .ok z' → z'.mid = some m' →
    z.mid.isSome = true
  | [], [], z, z', m', h, hm => by
    obtain rfl := walk_nil_ok h
    rw [hm]
    rfl
  | s :: ss, d :: ds, z, z', m', h, hm => by
    obtain ⟨x, z₁, -, h1, h2⟩ := walk_cons_ok h
    obtain ⟨m₁, e₁⟩ := Option.isSome_iff_exists.1 (walk_live L ss ds z₁ z' m' h2 hm)
    exact heard_live h1 e₁
  | [], _ :: _, _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, h, _ => by simp [walk] at h

/-- A state at a chain's start: both optional arguments were present. -/
theorem start_live {L : Lay} {bs : List (Block S Cl)} {m : Option (Mid W Y)} {v : Option S}
    {front : List OpenedColumn} {a : ChainProgress S Cl W Y} (h : ChainProgress.start L bs m v front = .ok a)
    (hm : a.mid.isSome = true) : ∃ m₀ v₀, m = some m₀ ∧ v = some v₀ := by
  obtain ⟨m', e'⟩ := Option.isSome_iff_exists.1 hm
  unfold ChainProgress.start at h
  obtain ⟨m₁, _, e, -⟩ := settle_same L _ _ a m' h e'
  cases v with
  | none => cases e
  | some v₀ =>
    cases m with
    | none => cases e
    | some m₀ => exact ⟨m₀, v₀, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.heard_live
#print axioms ProofFile.Honest.walk_live
#print axioms ProofFile.Honest.start_live
