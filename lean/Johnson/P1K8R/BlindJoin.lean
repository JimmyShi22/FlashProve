-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BlindJoin.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
FIELD `blind` OF WHAT IS LEFT (`K8LeftT`, P1K8R/TightAt.lean) AT THE CLOSED CONSTANT, FROM THE
RULE `drawBlind_mg`. NO SOUNDNESS.

`DrawBlind` says that whatever the table's promise and open items say beside the draw's own row has
one value in front of a yes of the draw and behind it. It is proved at the composed
meaning as a rule under seven premises on the parameters (`drawBlind_mg`, `MgOwes`:
P1K8R/BlindAtMg.lean) and three of the seven at the closed constant (`mgOwes_const`:
P1K8R/OwesAtConst.lean). Here:
  `smp_tlBlind`: a fourth: the constant's reader of OOD samples is blind to the draw (`smp_stays`).
  `BlindOwes`: WHAT IS LEFT OF IT: the item on the weights goes back over the draw; the readers of
    the segment's earlier runs are blind to it; THE FENCE: every tenant of a pin that is open in
    front of the draw sits in a tree below the piece's first; the plan's counts of trees and of
    messages do not move across the draw.
  `blind_at_const`: **`BlindOwes` gives `K8LeftT.blind`'s sentence, to the letter.**
Limits. `BlindOwes` is shown nowhere. Nothing on soundness.

-/
import Johnson.P1K8R.TightAt
import Johnson.P1K8R.OwesAtConst

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf sampledIn openSets start)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

theorem pcOf_eq (l : ℕ) : pcOf l - 1 = 4 + oOf l := by
  unfold pcOf oOf
  split <;> rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The constant's reader of OOD samples is blind to the draw. -/
theorem smp_tlBlind (z : ProofFile.InstPub) : TlBlind fun s => P5J.At.smp Zp (z, s) := by
  rintro s t ⟨tl, mm, f, -, rfl⟩
  exact smp_stays z s tl mm f

/-- **What is left of the field `blind` at link l.** -/
structure BlindOwes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (l base : ℕ) : Prop where
  wt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt l (z, t) y' w →
    h.𝔇.wt l (z, s) y w
  readers : ∀ k r, k < pcOf l → ∀ p ∈ h.𝔇.runs l k r, TlBlind ((h.𝔇.Rd l).forms p.1 p.2)
  fence : ∀ y ∈ sampledIn (P5J.At.N Zp cF)
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[ixOf l]?.getD []),
    y.1 < base
  trees : (P5J.At.N Zp cF).treesAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
    (P5J.At.N Zp cF).treesAt (flatPlacesOf linksFull true)[ixOf l]?
  msgs : (P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
    (P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[ixOf l]?

/-- **THE FIELD `blind`, AT THE CLOSED CONSTANT.** -/
theorem blind_at_const (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l base : ℕ} (hl : l ≤ 24)
    (H : BlindOwes h l base) :
    DrawBlind (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true) (drawAt l) base
      (oSAt (P5J.At.N Zp cF) (h.𝔇.Rd l) (4 + oOf l) l) := by
  have O : MgOwes h.𝔇 l base :=
    mgOwes_const _ _ _ _ _ _ _ _ _ _ _ _ _ _ l base (fun z => smp_tlBlind z) H.wt H.readers H.fence
  have g := drawBlind_mg (𝔇 := h.𝔇) hl (const_links _ _ _ _ _ _ _ _ _ _ _ _ _ _) O H.trees H.msgs
  have e : oSMg h.𝔇 l = oSAt (P5J.At.N Zp cF) (h.𝔇.Rd l) (4 + oOf l) l := by
    unfold oSMg
    rw [pcOf_eq]
    rfl
  rw [e] at g
  exact g

end

end P1K8T

#print axioms P1K8T.smp_tlBlind
#print axioms P1K8T.blind_at_const
