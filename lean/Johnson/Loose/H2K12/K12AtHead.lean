-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12RestOfPins
import Johnson.Loose.H2K12.K12RestOfHead
import Johnson.Loose.H2K12.ReachedOfPins
/-
Johnson/Loose/H2K12/K12AtHead.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN,
sub-protocol number 354 of the table's written list: THE TOP: the kind's law in its counted
form FROM THE COMPOSED MEANING's HEAD AND ONE EQUATION ON A LETTER. Two theorems: calls.
  k12Left_at_head  from the head (AtMgA, Johnson/P5J/MgAtAll.lean), heads and LastTypedAt: there is
                   a list L of places and shapes at which K12's files' named condition K12Left
                   (H2K12/Owed354AtMg.lean) holds, at the closed term At.foldD
                   Zp cF L
  k12_kind_at_head the head and heads: then LastTypedAt → h.Kind 𝔏 K12
WHOSE THEOREM PROVES WHAT, AND WHAT ITS FILE WANTS OF THE LIBRARY. (1) K12Left → the kind's law:
k12_kind_of_left (H2K12/Owed354AtMg.lean): K12's files': the four ties at 354 over the game at the
IOP as written. (2) Six → K12Left: k12Left_of_rest (H2K12/K12LeftOfRest.lean): K12's files' closed
facts, off the head and the two pins. (3) radius and clear fall to the pin madeRow: k12Rest_of_pins
(H2K12/K12RestOfPins.lean): clear is K12's files'; radius is a call of rad_in_scope
(Johnson/HB/LLHARD/RadiiInScope.lean): its file must lie. (4) The two pins from the head:
pins_of_head (H2K12/K12RestOfHead.lean): a call of LPFD.asks_pins
(Johnson/Desc/Laid/ProofAsksLaw2.lean): the list of the proof file's entry tests must be a list
that asks them. (5) The head with the facts on every reached state, from the head and the two pins:
reached_some (H2K12/ReachedOfPins.lean): a call of P5J.atMgR_madeRow
(Johnson/P5J/FoldJ3Whole.lean): THE INDUCTION ALONG THE RUN IS OTHER FILES' WORK: its files must
lie. (3), (4) and (5) stand side by side, each over its own imports; they are joined here.
WHAT IS LEFT BEHIND THIS FILE, BY NAME: heads (an equation on the letter 𝔏: its first two
sub-protocols' letters are the first flat list's head and rest), and LastTypedAt (the premise of the
counted form itself).
WHAT IT ALL RESTS ON IN THE END. (a) THE HEAD: that it can be met is shown nowhere here: NO EXAMPLE.
(b) THE TWO PINS COMPARE WITH WRITTEN VALUES: where the entry tests accept, the made sizes, the
sendings and the cut ARE the written ones at these files; that the written values are what the
makers give is no theorem: the written cut rests on prints of Lean's evaluator
(Johnson/Desc/First/CutWritten.lean, by its own head). A wrong written value would make the entry
test refuse honest files: there is then no head at those files, and the theorems here say nothing of
them; at whatever files of the full size's key (which the head's scope gives; at every other key
these two tests accept and say nothing) the tests do accept, the values are the written ones, at
which the closed facts are decided (an argument, not proved here, from the head's laid.asks,
LPFD.asks_pins, made_of_pinned and cut_of_row: Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean,
CutTestLaws.lean). (c) This file stands above Cb/Bridge/CodeListRSProved.lean through its imports,
and so above the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15). (d) The game's bound at one
round and the condition on the rounds are the files' named in H2K12/TieAt354.lean.
WHAT IT IS NOT. A JOINING. The kind's law is one premise of a statement on the whole verifier, not
that statement. The full size alone.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (KindName)
open P5J (AtMgA AtMgR F0T TS Free)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **K12's FILES' NAMED CONDITION, FROM THE HEAD AND ONE EQUATION ON A LETTER.** -/
theorem k12Left_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (hT : LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) :
    ∃ L, K12Left h 𝔏 (P5J.At.foldD Zp cF L) := by
  obtain ⟨hm, hc⟩ := pins_of_head h
  have W : Written354 Zp := written354_of_pins h.scope h.laid.pub hm
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)
  obtain ⟨L, R⟩ := reached_some h W hm hc
  exact ⟨L, k12Left_of_rest (k12Rest_of_pins h 𝔏 R heads hm hc) hT⟩

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE HEAD AND ONE EQUATION ON A LETTER.** -/
theorem k12_kind_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 := fun hT => by
  obtain ⟨L, K⟩ := k12Left_at_head h 𝔏 heads hT
  exact k12_kind_of_left K hT

end H2K12

#print axioms H2K12.k12Left_at_head
#print axioms H2K12.k12_kind_at_head
