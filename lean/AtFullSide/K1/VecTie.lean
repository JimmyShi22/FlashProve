-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/VecTie.lean: the clause of VecPlanS that each sort of segment pays by itself: behind the
reads' member the maker of the segment's values returns at what was heard, and its vector is the
reading at the state's own tables.

  VecTie   a premise's form. No member, no negative test. It may hold emptily

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsVecS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes OnBytes.Params
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (parOfMats)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.FirstThread (Letters)

/-- **THE ONE CLAUSE OF VecPlanS THAT IS NO SHAPE, AT A STAND BEHIND THE READS**: what the maker
returns at what was heard, and that its vector is the reading at the state's own tables. A premise's
form, paid sort by sort. -/
def VecTie {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
    (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b₁ : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Z : ProofFile.Pub) (G : ProofFile.Ground) (sg nR : ℕ)
    (A : MsgAddr) : Prop :=
  ∀ blk, L.bs[b₁]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b₁ k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl →
    ∃ (SV : SegVals) (vec : Cells → ℕ → OnBytes.E),
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) sg = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      SV.n = nR ∧
      ∀ (C : Cells) (j : ℕ), j < nR → vec C j =
        First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf C (matsOwn G.W sg)) j

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.VecTie
