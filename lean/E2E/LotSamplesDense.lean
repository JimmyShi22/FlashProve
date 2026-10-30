-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotSamplesDense.lean.

`lotSamplesDense`: wherever the verifier's fold over the key file's first chain, or over its shared
chain, returns from that chain's first state, every sample row of the statement is dense.

How. The stronger mark `stSamplesB` (no sample row has a written-out factor) is carried. In front of
the ranges' test it comes from `marks_of_pre` (E2E/KeyMarksThr.lean); behind it, and along the shared
chain, from E2E/LotSamplesDenseKeeps.lean.

Limits. It says nothing on whether a fold returns. Of rows it speaks of form alone. The open rows are
not touched, nor is the last chain. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnMarks
import E2E.KeyMarksThr
import E2E.LotSamplesDenseKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc (foldBlocks OpenedColumn)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.AtFiles (KeySourced)
open VerifierAndGoals (PublicFiles InScope)

/-- **Where the fold returns, every sample row is dense.** -/
def LotSamplesDense (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → ∀ (x : Xi) (seen : List Fmt.RoundView) (cols : List OpenedColumn),
    (∀ s r c, foldBlocks 0 (descriptionFromSource Xs N Pl).first.blocksInOrder ((descriptionFromSource Xs N Pl).start₁ x) seen cols = .ok (s, r, c) →
      SamplesDense s.d.st) ∧
    (∀ s r c, foldBlocks 0 (descriptionFromSource Xs N Pl).shared.blocksInOrder ((descriptionFromSource Xs N Pl).start₂ x) seen cols = .ok (s, r, c) →
      SamplesDense s.st)


/-- A statement whose sample rows have no written-out factor has dense ones. -/
theorem dense_of_sam {S : Statement} (h : VerifiableInference.Desc.Ground.Sh.stSamplesB S = true) :
    SamplesDense S :=
  fun _ _ hx r hr => OnBytes.Slice.ProxRun.denseRow_of_plain
    (VerifiableInference.Desc.Ground.Sh.samples_rows h hx r hr)

/-- **Where the fold returns, every sample row is dense.** -/
theorem lotSamplesDense (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) :
    LotSamplesDense Xs N Pl := by
  intro Z hs scope x seen cols
  have hplan := hs.named.plan
  have hmem : H2K.JointK.rngEntry Xs.Y.k.oneTime N ∈ (descriptionFromSource Xs N Pl).first.blocksInOrder := by
    show _ ∈ (VerifiableInference.Desc.Key.firstChain Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).blocksInOrder
    rw [H2K.JointK.keyFirst_cut]
    simp
  have h1 := (VerifiableInference.Desc.Keeps.planOk_blocks _ hplan).1 _ hmem
  obtain ⟨he, ha⟩ := AtPublicFiles.AtFiles.ranges_place (Cl := VerifiableInference.Desc.Key.Claim)
    Xs.Y.k.oneTime N (Bool.and_eq_true_iff.1 h1).1
  obtain ⟨hU, hO⟩ := AtPublicFiles.AtFiles.shared_places_in_scope hs scope
  constructor
  · intro s r c h
    have h' : foldBlocks 0 (VerifiableInference.Desc.Key.firstChain Xs.Y.k.oneTime Xs.Y.D.1
        Xs.Y.told.1 Xs.set N).blocksInOrder
        (VerifiableInference.Desc.Key.chainStart Xs.Y.k.oneTime.codes {}) seen cols =
        .ok (s, r, c) := h
    rw [H2K.JointK.keyFirst_cut] at h'
    obtain ⟨s₁, rs₁, c₁, f1, f2⟩ := (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h'
    have m := AtPublicFiles.AtFiles.marks_of_pre _ _ _ _ _ 0 f1 (AtPublicFiles.AtFiles.plainAll_start _)
    have p0 := VerifiableInference.Desc.Ground.Sh.samples_of_plain m.1
    exact dense_of_sam (Walk.first_back_fold _ _ _ _ _ he ha 0 s₁ rs₁ c₁ _ f2 p0)
  · intro s r c h
    exact dense_of_sam (Walk.shared_fold Xs.chains Pl hU hO 0 _ seen cols (s, r, c) h
      (VerifiableInference.Desc.Ground.Sh.start_samples _))

end AtPublicFiles.KeyLastChain.Lots

#print axioms AtPublicFiles.KeyLastChain.Lots.dense_of_sam
#print axioms AtPublicFiles.KeyLastChain.Lots.lotSamplesDense
