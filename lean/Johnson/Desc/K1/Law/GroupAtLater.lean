-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/GroupAtLater.lean: WHAT A LATER MOMENT's SENDING OF KIND K1 (commitAtS: a link's reads, its digits) DOES TO THE STATEMENT's GROUPS: the frame's own group gains the new
messages as members; its rows and its mark "in a test" stay; every other group is as it was. The twin, for a later moment, of Johnson/Desc/K1/Law/GroupAtRecord.lean's
firstAtS_group. Statements with their proofs. It names no table of joints.
  Joins.of_groups      Joins reads the statement in front by its groups alone
  commitOwn_group      the kind's block
  st_put               laying a link's part of the state and a ledger leaves the statement
  commitAtS_group      **the block at the state**
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.FrameAtLater
import Johnson.Desc.K1.Law.HeldAtOpening

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

theorem Joins.of_groups {a b c : Statement} {g : Nat} {l : List Nat} (e : a.groups = b.groups)
    (h : Joins a c g l) : Joins b c g l :=
  ⟨by rw [← e]; exact h.size, fun j hj => by rw [← e]; exact h.other j hj,
    fun G hG => h.here G (by rw [e]; exact hG)⟩

/-- **The kind's block**: the groups behind. -/
theorem commitOwn_group (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s') :
    Joins s.held.w.st s'.held.w.st s.held.L.check.frame.group
      (idsOf P s.held.w.st.oracles.size).toList := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', a1, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      obtain ⟨_, hids, _⟩ := (decideSend_iff P s.owed _ d₁ r₁ r₂ ids).1 a1
      have hk : d₁.st.groups = s.held.w.st.groups := (decideSend_kept P s.owed _ d₁ _ ids a1).2.1
      have hj := (joinOwnP_joins _ _ _ _ _ _ a2).1
      rw [← e]
      rw [hids] at hj
      exact Joins.of_groups hk hj
  · cases h

/-- Laying a link's part of the state and then a ledger leaves the statement. -/
theorem st_put (s : S) (w : DState Unit) (L' : LinkCtx) (F' : Fork) :
    (((laid s w).putLink L').putFork F').st = w.st := by
  cases hs : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [S.putFork, S.putLink, laid, hs, ho]
  | _ => simp [S.putFork, S.putLink, laid, hs]

/-- **THE BLOCK AT THE STATE.** -/
theorem commitAtS_group (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ L, s.link? = some L ∧
      Joins s.st s'.st L.check.frame.group (idsOf P s.st.oracles.size).toList := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    have hj := commitOwn_group P link moment arrays _ y r₁ r₂ gs hy
    refine ⟨L, hL, ?_⟩
    rw [st_put]
    exact hj
  · cases h

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.commitAtS_group
