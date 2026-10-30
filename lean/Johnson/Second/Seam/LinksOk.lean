-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/LinksOk.lean: THE PREMISE «linksOk links = true» (Johnson/Desc/First/Driver/Chain.lean: the list of the first chain's segments ends with the head and has no other head): two payers. Statements and proofs.
  linksOk_of_bare · linksOk_of_first   WHEREVER THE DRIVER HAS MADE A FIRST CHAIN OF THE LIST, THE TEST SAYS YES: firstChainWithoutReplyGuard H links several = some c → linksOk links = true, and the like for firstChain: the driver's own first line refuses otherwise. General in the sub-protocols H, the list and the flag.
  linksOk_of_chainC   the like for ProofFile.chainC (Johnson/Desc/ProofFile/FillCore.lean), by which the proof file's written IOP makes its first chain of subsOf Z (Frames1.lean:194): ProofFile.chainC bs links fr = .ok c → linksOk links = true.
  linksOk_full · linksOk_small   the test at the library's two pairs of written lists of segments (Johnson/Desc/First/Look/K3RowIndex.lean: fullSubs | smallSubs · K3LiveIs.lean: liveFull | liveSmall): by Lean's kernel; with it: the two full lists are one list; 25 segments.
  linksOk_not       three negative tests: no head at the end · a second head · the empty list.
Limits. That the list at a seat IS one of the written lists is not said here; the first payer does not need it. No soundness is claimed.

-/
import Johnson.Desc.First.Driver.Chain
import Johnson.Desc.First.Look.K3RowIndex
import Johnson.Desc.First.Look.K3LiveIs
import Johnson.Desc.ProofFile.FillCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open VerifiableInference.Desc VerifiableInference.Desc.First


theorem linksOk_of_bare {S Cl : Type} {H : Blocks S Cl} {links : List ModelPart} {several : Bool}
    {c : Chain S Cl} (h : firstChainWithoutReplyGuard H links several = some c) : linksOk links = true := by
  unfold firstChainWithoutReplyGuard at h
  cases hl : linksOk links with
  | true => rfl
  | false =>
    rw [hl] at h
    cases h


theorem linksOk_of_first {S Cl : Type} {H : Blocks S Cl} {links : List ModelPart} {several : Bool}
    {c : Chain S Cl} (h : firstChain H links several = some c) : linksOk links = true := by
  unfold firstChain at h
  obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 h
  exact linksOk_of_bare hb


theorem linksOk_of_chainC {σ Cl : Type} {bs : List (Block σ Cl)} {links : List ModelPart}
    {fr : ProofFile.Frames σ Cl} {c : Chain σ Cl} (h : ProofFile.chainC bs links fr = .ok c) :
    linksOk links = true := by
  unfold ProofFile.chainC at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i c' hc'
      exact linksOk_of_first hc'

theorem linksOk_full : linksOk VerifiableInference.OnPublicFiles.fullSubs = true ∧ linksOk Look.liveFull = true ∧
    VerifiableInference.OnPublicFiles.fullSubs = Look.liveFull ∧ VerifiableInference.OnPublicFiles.fullSubs.length = 25 := by decide +kernel

theorem linksOk_small : linksOk VerifiableInference.OnPublicFiles.smallSubs = true ∧ linksOk Look.liveSmall = true := by
  decide +kernel

theorem linksOk_not : linksOk [.layers, .attention] = false ∧
    linksOk [.layers, .head, .attention, .head] = false ∧ linksOk [] = false := by decide +kernel

end Second.Seam

#print axioms Second.Seam.linksOk_of_bare
#print axioms Second.Seam.linksOk_of_first
#print axioms Second.Seam.linksOk_of_chainC
#print axioms Second.Seam.linksOk_full
#print axioms Second.Seam.linksOk_small
#print axioms Second.Seam.linksOk_not
