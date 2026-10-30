-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CarriesAtLot.lean: EVERY BLOCK OF K1's OWN LOT, AS
Johnson/Desc/ProofFile/Lots/PureLots.lean's k1Pure LAYS IT (Johnson/Desc/ProofFile/Lot/K1.lean's
blocks, with the quiet step behind the reads), STEPS:
b ∈ (ProofFile.k1Pure Z).own G → b.Steps (CarriesFo S.fork? S.lookHeard?): the first segment's opening,
every link's reads' place's joined block, every link's digits' commitment: at any ground G, any
size. WITHOUT planOk.
  firstAtS_stepsFo     the opening stands between two links: in front no link's part is there:
    nothing was heard, no ledger is held
  same_refuser · same_readsQuietAt · same_orLoud      the quiet step behind the reads leaves both
    readers (where no block could be made the refuser never says yes)
  k1Pure_steps       **the lot**
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.CarriesAtLater
import Johnson.Desc.ProofFile.Lots.PureLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)

/-- **The first segment's opening's decision steps.** -/
theorem firstAtS_stepsFo {Cl : Type} (q : Params.First) (gp : GPar) :
    (firstSegmentOpening (Cl := Cl) q gp).Steps (CarriesFo S.fork? S.lookHeard?) := by
  intro s rs gs s' h
  refine carriesFoOfLater _ _ s s' (fun g hg => ?_) (firstAtS_later q gp s rs gs s' h)
  simp only [firstSegmentOpening] at h
  obtain ⟨_, h0, _⟩ := (bind_ok _ _ _).1 h
  have hb := (need_ok _ _ _).1 h0
  unfold S.atBetween at hb
  unfold S.lookHeard? at hg
  split at hb
  · rename_i hh
    simp [hh] at hg
  · cases hb

theorem same_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : SameReaders q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact same_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact same_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem same_orLoud {G : ProofFile.Ground} (name : String) (a : Place) (what : String) (l : Nat)
    (X : LinkH) (piece : Nat) :
    SameReaders (ProofFile.orLoud name a what (ProofFile.readsQuietAt G l X piece)) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact same_readsQuietAt l X piece q hq

/-- **EVERY BLOCK OF K1's OWN LOT STEPS.** -/
theorem k1Pure_steps (Z : ProofFile.Pub) (G : ProofFile.Ground) (b : Block S Unit)
    (hb : b ∈ (ProofFile.k1Pure Z).own G) : b.Steps (CarriesFo S.fork? S.lookHeard?) := by
  have hb' : b ∈ blocks (gpOf Z) (fun (G : ProofFile.Ground) (l : Nat) (X : LinkH) =>
      some (ProofFile.orLoud s!"link {l}: the step after the commitment before the smallness test"
        ⟨1, some l, if X.kind == 0 || X.kind == 1 then 4 else 5, .K1⟩
        "the step after the commitment that comes before the smallness test"
        (ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5)))) G := hb
  unfold blocks at hb'
  dsimp only at hb'
  rcases List.mem_append.1 hb' with h | h
  · obtain rfl := List.mem_singleton.1 h
    exact firstAtS_stepsFo _ _
  · obtain ⟨⟨X, l⟩, _, h⟩ := List.mem_flatMap.1 h
    dsimp only at h
    cases hn : linkNumbers G X with
    | none =>
      rw [hn] at h
      cases h
    | some y =>
      obtain ⟨pr, pd, reads, digits⟩ := y
      rw [hn] at h
      dsimp only at h
      rcases List.mem_cons.1 h with rfl | h
      · exact andThen_stepsFo _ _ _ _ _ _ (same_orLoud _ _ _ l X _)
      · obtain rfl := List.mem_singleton.1 h
        exact laterAt_stepsFo _ _ _ _ _ _

end VerifiableInference.Desc.K1
