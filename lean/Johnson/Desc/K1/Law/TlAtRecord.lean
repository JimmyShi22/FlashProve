-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TlAtRecord.lean: a yes of each of the kind's three blocks at the first chain's
carried record leaves the smallness test's record of the open link (S.tl?) as it was, and behind it
no row is owed.

Main names: putLink_tl, putFork_tl; commitAtS_tl, firstAtS_tl, sendAtS_tl; laterAt_tl.
So every reading of the carried record that reads S.tl? alone is left by these blocks.

What is not claimed. Nothing on what the record holds in front of a block. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

theorem putLink_tl (s : S) (L : LinkCtx) :
    (s.putLink L).tl? = s.tl? ∧ (s.putLink L).rowsOwed = s.rowsOwed := by
  unfold S.putLink
  split <;> (try split) <;> simp_all [S.tl?]

theorem putFork_tl (s : S) (F : Fork) :
    (s.putFork F).tl? = s.tl? ∧ (s.putFork F).rowsOwed = s.rowsOwed := by
  unfold S.putFork
  split <;> (try split) <;> simp_all [S.tl?]

/-- **A segment's later moment.** -/
theorem commitAtS_tl (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.tl? = s.tl? ∧ s'.rowsOwed = none := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · cases hb : (commitOwn P link moment arrays : Block _ Cl).decide
        { owed := owedOf s, held := { L := _, F := _, tl := _, w := stateOf s () } } rs gs with
    | error e => rw [hb] at h; cases h
    | ok y =>
      rw [hb] at h
      obtain rfl := Except.ok.inj h
      exact ⟨((putFork_tl _ _).1.trans (putLink_tl _ _).1).trans rfl,
        ((putFork_tl _ _).2.trans (putLink_tl _ _).2).trans rfl⟩
  · cases h

theorem laterAt_tl (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (laterAt q gp link piece moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.tl? = s.tl? ∧ s'.rowsOwed = none :=
  commitAtS_tl _ _ _ _ s s' rs gs h

/-- **The first segment's opening.** -/
theorem firstAtS_tl (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') :
    s'.tl? = s.tl? ∧ s'.rowsOwed = none := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, _, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨rfl, rfl⟩

/-- **W's sending.** -/
theorem sendAtS_tl (P : Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') : s'.rowsOwed = none := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · cases hb : (sendOwn P : Block _ Cl).decide
          { owed := owedOf s, held := stateOf s #[] } rs gs with
      | error e => rw [hb] at h; cases h
      | ok y =>
        rw [hb] at h
        obtain rfl := Except.ok.inj h
        rfl
    · cases h
  · cases h

end VerifiableInference.Desc.K1
