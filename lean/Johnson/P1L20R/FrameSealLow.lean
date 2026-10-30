-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameSealLow.lean:
the two bounds that the tie of the seal at number 357 still asks
(seal_tie_atAll, Johnson/Desc/AtSeats/Seal357AtAll.lean: hI, hV): the trees of the index-mask
message and of the message W, which the chain's last sending commits, lie below the base of the
piece at 357: FROM fenceFit's YES at the numbers of the bundle of hypotheses P5J.AtMgA.

  pinsAt357_full    the pins of these two messages are open at border 357 of the written list: by
                    Lean's kernel
  seal_low_atAll    so, by low_atAll (FrameLowAll.lean): (dmOf h).N.index.1 < q.base and
                    (dmOf h).N.w.1 < q.base at the piece q at 357

Limits. fenceFit's yes is a premise. No soundness statement.

-/
import Johnson.P1L20R.FrameLowAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item flatPlacesOf fenceFit sampledIn)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

/-- A test with code: the two pins are open at border 357, and the written list has at least 357
places. -/
def pinsAt357B : Bool :=
  (openL9 357).contains Item.pinI && (openL9 357).contains Item.pinV &&
    decide (357 ≤ (flatPlacesOf linksFull true).length)

set_option maxRecDepth 1000000 in
theorem pinsAt357_full : pinsAt357B = true := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The two bounds at the seal.** -/
theorem seal_low_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hf : fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true) :
    ∀ q, (h.toAtMg.row L)[357]? = some q →
      (dmOf h).N.index.1 < Piece.base q ∧ (dmOf h).N.w.1 < Piece.base q := by
  intro q hq
  have hp := pinsAt357_full
  unfold pinsAt357B at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hp
  obtain ⟨⟨hI, hV⟩, hk⟩ := hp
  have hl := low_atAll h L q₁ q₂ q₃ hf 357 hk q hq
  refine ⟨hl _ ?_, hl _ ?_⟩
  · unfold sampledIn
    exact List.mem_flatMap.2 ⟨_, hI, List.mem_singleton.2 rfl⟩
  · unfold sampledIn
    exact List.mem_flatMap.2 ⟨_, hV, List.mem_singleton.2 rfl⟩

end

end P1L20

#print axioms P1L20.pinsAt357_full
#print axioms P1L20.seal_low_atAll
