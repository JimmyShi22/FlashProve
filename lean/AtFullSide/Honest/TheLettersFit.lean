-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLettersFit.lean: laws on TheLetters.lean's values that need files of laws: later
is IOP's laterTerm; at a run ends is what lastAtRun gives; the last chain's members 0, 1 and 3 send no
tree.
-/
import AtFullSide.Honest.TheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes (TableKey)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-- later is IOP's laterTerm. -/
theorem later_is_laterTerm (O : OpenShared A) :
    later (h := h) O = ProofFile.Honest.Term.laterTerm h (sharedBlocks h)
      ((ProofFile.Honest.K12.AtProof.fourOf h.places).O.getD (ProofFile.Honest.K12.AtProof.fourOf h.places).U)
      O.rest keepsOff := rfl

/-- At a run, ends is what the two threads of that run give. So thread₃ and the second chain's
thread with lastAtRun read the same two states at the run's own input. -/
theorem endsAt_at_run {O : OpenShared A} (P : OpenLast h O)
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} (hc : R.common = toCommon (A := A) R.own)
    (k : Coins A.B) (hd : List Fmt.Drawn) :
    (last h P).ends k R.own hd =
      (lastAtRun h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R).ends k
        R.own hd := by
  have h₁ : standOne (A := A) R.own = firstStand A.H R := rfl
  have h₂ : standTwo (A := A) (toCommon (A := A) R.own) = sharedStand A.H R := by
    funext c
    show { startShared A.H (toCommon (A := A) R.own) with opened := some [] } =
      { startShared A.H R.common with opened := some [] }
    rw [hc]
  show endsAt h O k R.own hd = _
  unfold endsAt lastAtRun
  simp only [threadTwo, saidTwo, saidOne, threadOne]
  rw [h₁, h₂, hc]

/-- The front of the own test is the second thread's. -/
theorem lastFront_is_front {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    lastFront h = (thread₃ h P R).front := by
  show _ = (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
    declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length
  rw [List.length_append]

theorem treesTo_behind_quiet {S Cl : Type} {bs : List (VerifiableInference.Desc.Block S Cl)} {b : Nat}
    {blk : VerifiableInference.Desc.Block S Cl} (hb : bs[b]? = some blk)
    (hq : blk.oracles.flatMap id = []) : treesTo bs (b + 1) = treesTo bs b := by
  unfold treesTo
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 hb
  rw [List.take_succ_eq_append_getElem hlt, List.flatMap_append, e]
  have hn : ([blk].flatMap fun x => x.oracles.flatMap id) = [] := by
    show blk.oracles.flatMap id ++ [] = []
    rw [hq]
    rfl
  rw [hn, List.append_nil]

/-- **At the last chain members 0, 1 and 3 send no tree.** So the socket on members that send one
asks at member 2 alone. -/
theorem last_fresh {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    (thread₃ h P R).fresh 0 = [] ∧ (thread₃ h P R).fresh 1 = [] ∧ (thread₃ h P R).fresh 3 = [] := by
  refine ⟨rfl, rfl, ?_⟩
  have e := treesTo_behind_quiet (bs := (thread₃ h P R).bs) (b := 3) rfl rfl
  unfold Thread.fresh Thread.hand
  rw [e]
  exact List.filter_eq_nil_iff.2 fun σ hσ => by simp [hσ]

end AtFullSide.Honest.TheLetters
