-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12AtHead
import Johnson.Loose.H2K12.LastTypedOfLaid
import Johnson.P5J.FreeAll
/-
H2K12/K12AtFree.lean: THE LAW OF THE PROXIMITY TEST (the kind K12) ON
THE PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the table's written list: THE TOP OF
H2K12/K12AtHead.lean AT THE OTHER TEAM's OWN CLOSED FILLING h.free (Johnson/P5J/FreeAll.lean), AND
WITH THE PREMISE OF THE COUNTED FORM DRAWN OFF THE HEAD. Five theorems: calls.
  lastTypedAt_at_head
                   from the head (AtMgA, Johnson/P5J/MgAtAll.lean) alone: LastTypedAt secondHashFunction Z.pol
                   Z.lay Z.KL. The road: "the value is laid" comes off the head's own fields
                   (LPFD.Full.laidPOf_of, Johnson/Desc/Laid/ProofFullLaw.lean); in scope, where the
                   value is laid, the sized stages of the last proximity test are the typed list
                   (lastTypedAt_of_laid, H2K12/LastTypedOfLaid.lean, which spends the entry test
                   madeRow)
  k12_kind_of_heads
                   the head and heads, at every filling 𝔏: h.Kind 𝔏 K12
  k12_kind_at_free the head alone: LastTypedAt → h.Kind h.free K12: the form of the field k12 of
                   KindsConds (Johnson/Goal/Skeleton/KindsOfConds.lean) at 𝔏 := h.free. heads is
                   AtMgA.free_q₁, to the letter
  k12Left_at_free  the head alone: there is a list L at which the named condition K12Left
                   (H2K12/Owed354AtMg.lean, which does not turn) holds at h.free and At.foldD Zp cF
                   L
  k12_kind_at_free'
                   THE HEAD ALONE: h.Kind h.free K12
WHAT IS LEFT BEHIND THIS FILE: NO PREMISE BUT THE HEAD.
WHAT IT ALL RESTS ON, AND WHAT IT IS NOT: as H2K12/K12AtHead.lean's head says, point by point; in
short: THAT THE HEAD CAN BE MET IS SHOWN NOWHERE HERE: NO EXAMPLE: where there is no head the
theorems say nothing. The head is the head over the list of entry tests that asks the two tests on
written values: over an earlier list these files do not stand. The induction along the run, the
entry tests' laws, one radius and the filling h.free are other houses' theorems and terms, called.
It stands above the files under ThirdParty/ (lean/LIMITS.md, L15). The kind's law is one premise of
a statement on the whole verifier, not that statement. At the earlier hash secondHashFunction and the full size
alone.
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

/-- **THE PREMISE OF THE COUNTED FORM, FROM THE HEAD.** -/
theorem lastTypedAt_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL :=
  lastTypedAt_of_laid h.scope
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- **THE KIND's LAW FROM THE HEAD AND ONE EQUATION ON A LETTER, at every filling.** -/
theorem k12_kind_of_heads (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) : h.Kind 𝔏 KindName.K12 :=
  k12_kind_at_head h 𝔏 heads (lastTypedAt_at_head h)

/-- **THE KIND's LAW IN THE COUNTED FORM, AT THE CLOSED FILLING.** -/
theorem k12_kind_at_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind h.free KindName.K12 :=
  k12_kind_at_head h h.free h.free_q₁

/-- **THE HOUSE's NAMED CONDITION AT THE CLOSED FILLING, FROM THE HEAD ALONE.** -/
theorem k12Left_at_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ L, K12Left h h.free (P5J.At.foldD Zp cF L) :=
  k12Left_at_head h h.free h.free_q₁ (lastTypedAt_at_head h)

/-- **THE KIND's LAW AT THE CLOSED FILLING, FROM THE HEAD ALONE.** -/
theorem k12_kind_at_free' (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.Kind h.free KindName.K12 :=
  k12_kind_at_free h (lastTypedAt_at_head h)

end H2K12

#print axioms H2K12.lastTypedAt_at_head
#print axioms H2K12.k12_kind_of_heads
#print axioms H2K12.k12_kind_at_free
#print axioms H2K12.k12Left_at_free
#print axioms H2K12.k12_kind_at_free'
