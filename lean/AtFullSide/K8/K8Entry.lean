-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/K8Entry.lean: the smallness test's entry in the kinds' rows of record, and its share at the rows
of record. One definition, one theorem.

  `k8Entry`                the lot with its simulators, that the filling bears its name, that it has its sides
  `k8Share_at_record`      **KindShare at the rows of record, where the record's entry k8 is this one**

Limits. What the share says and what it leaves out: AtFullSide/K8/ShareAtTheG.lean. Nothing is claimed on
completeness, soundness or hiding.
-/
import AtFullSide.K8.ShareAtTheG
import E2E.TheKOfRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open ProofFile.Honest.Term (baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheSides (LotEntry TheThirteen LaterRows theK mem_theK)
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.AtFiles

/-- **The kind's entry.** -/
noncomputable def k8Entry (files : VerifierAndGoals.PublicFiles) (Z : Pub) (G : Ground) :
    LotEntry (baseFilling files) Z G :=
  ⟨k8LotAtBase, k8_named files, k8_lots_fit files Z G⟩

/-- **The kind's three shares at the rows of record.** -/
theorem k8Share_at_record {Wt : Type} {files : VerifierAndGoals.PublicFiles}
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (E : TheThirteen (baseFilling files) returned.Z returned.G)
    (hE : E.k8 = k8Entry files returned.Z returned.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows (baseFilling files) returned.Z returned.G)
    (H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit) (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R',
      ready returned.F returned.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k =
        .ok R' →
      ThreadsP returned.F returned.B ((theGOfReturn made h T (theK E apart R)).prover H) w₀ rc x k R') :
    KindShare returned (theGOfReturn made h T (theK E apart R)) H Rel Th .K8 ∧
      K8Stands (theGOfReturn made h T (theK E apart R)) (k8LotAtBase.rows returned.Z returned.G) := by
  have laid : k8LotAtBase ∈ (theK E apart R).lots := by
    have he : E.k8 ∈ E.entries := by simp [TheThirteen.entries]
    have := mem_theK he apart R
    rw [hE] at this
    exact this
  exact ⟨k8Share_at_theGOfReturn made h T _ laid H Rel Th, k8Stands_at_theGOfReturn made h T _ laid⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Entry
#print axioms ProofFile.Honest.K8.k8Share_at_record
