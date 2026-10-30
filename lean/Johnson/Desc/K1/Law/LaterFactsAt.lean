-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/LaterFactsAt.lean: K01_law: LaterFacts (Johnson/Desc/K1/Law/MgK1.lean: a yes keeps every sampled message; the book grows at its end alone) AT K1's TWO SORTS OF LATER BLOCK.
  laterFacts_commit   by K1.Rel.commitAtS_keeps (Johnson/Desc/K1/KeepsAtS.lean) at groundKeeps_smpStay; the book: commitAtS_booked
  laterFacts_k1Reads  the quiet step leaves the statement and the book (QuietL)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.KeepsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

theorem laterFacts_commit (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterFacts (commitAtS P link moment arrays : Block S Unit) where
  rounds := rfl
  smpStay s s' r₁ r₂ gs h :=
    Rel.commitAtS_keeps groundKeeps_smpStay P link moment arrays s _ gs s' h
  grows s s' r₁ r₂ gs h := ⟨_, (commitAtS_booked P link moment arrays s s' r₁ r₂ gs h).place⟩

theorem laterFacts_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : LaterFacts (k1Reads Z G l X pr reads) := by
  have key : ∀ s s' r₁ r₂ gs, (k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s' →
      ∃ s₁ gs₁ rs₂ gs₂,
        (commitAtS (parLater G.first (gpOf Z) l pr 1) l 1 reads : Block S Unit).decide s [r₁, r₂]
          gs₁ = .ok s₁ ∧ (k1Quiet G l X).decide s₁ rs₂ gs₂ = .ok s' := by
    intro s s' r₁ r₂ gs h
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        ([r₁, r₂].take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          ([r₁, r₂].drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    exact ⟨s₁, _, _, _, h1, h2⟩
  refine ⟨rounds_k1Reads _ _ _ _ _ _, fun s s' r₁ r₂ gs h => ?_, fun s s' r₁ r₂ gs h => ?_⟩
  · obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h2⟩ := key s s' r₁ r₂ gs h
    rw [(quietL_k1Quiet G l X _ _ _ _ h2).1]
    exact (laterFacts_commit _ _ _ _).smpStay _ _ _ _ _ h1
  · obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h2⟩ := key s s' r₁ r₂ gs h
    rw [(quietL_k1Quiet G l X _ _ _ _ h2).2.1]
    exact (laterFacts_commit _ _ _ _).grows _ _ _ _ _ h1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laterFacts_commit
#print axioms VerifiableInference.Desc.K1.laterFacts_k1Reads
