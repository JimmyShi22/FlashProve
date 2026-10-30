-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/QuietTellsNothing.lean:
the first section of an earlier TellsAtFifty.lean, CUT OFF BY PROGRAM so that it stands on a
light import: the quiet step behind a segment's commitment before the approximate range proof
declares no oracle (where none could be made, the sub-protocol that rejects declares none either).
  oracles_blockAt, oracles_readsQuietAt, oracles_k1Quiet
No statement and no proof has turned against that earlier file.
What is not claimed. Nothing on soundness.

-/
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Oracle)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

/-! ## The quiet block tells nothing -/

theorem oracles_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : q.oracles = [] := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h

theorem oracles_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) : q.oracles = [] := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      unfold First.Att.readsAtO at h
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact oracles_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem oracles_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : (k1Quiet G l X).oracles = [] := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => rfl
  | some q => exact oracles_readsQuietAt l X _ q hq

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.oracles_k1Quiet
