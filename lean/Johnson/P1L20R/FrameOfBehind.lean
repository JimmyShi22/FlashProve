-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameOfBehind.lean:
the share of the kind "frame" on the first chain (77 places) under the bundle of
hypotheses P5J.AtMgA FROM ITS OWN TIES AT THE 25 PLACES BEHIND THE BATCHING ALONE: no other kind's
condition is a premise.

  FrameBehind       the tie, in the counted form (the body of KindTiedR, in AtMgA.Kind's letters),
                    at the 25 numbers behindIx l, l < 25
  frame_of_behind   h.Kind L KindName.frame from FrameBehind h L (and the three lists' first
                    members)
  frameBehind_of_k9 FrameBehind h L out of the batching kind's condition
                    (k09_behindTies, Johnson/P5J/K09Behind.lean)

Of the kind's 77 places: at 51 (the front, 25 "laid", 25 "cleared") the tie is shown; at 1 (357) it
is seal_tie_atAll (Johnson/Desc/AtSeats/Seal357AtAll.lean), called; at 25 it is the premise
FrameBehind h L: a part of the conclusion.

Limits. The 52 ties that are not handed in rest on fence_atAll (FramePubAll.lean), which holds only
from the verifier's list of entry tests of thirteen rows on (GLOSSARY.md; this library's list has
fourteen). FrameBehind h L follows from the bundle and the three lists' first members, by
frameBehind_of_k9 at k09_cond_of_head (Johnson/P5J/K09CondHead.lean). A member of AtMgA is proved at
storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction alone.
h.Kind speaks of the first chain's 77 places of the kind alone. Of the eight clauses of every tie
(TiedAtR, Johnson/Desc/Sound/ChainOfPromisesR.lean) five stand under: the promise at the border,
reached, no check has failed: where no state meets these, these five are idle. The other three (the
piece's own law GoodIn; a failed check stays failed; "decodes" is handed on) bear no such guard. By
the written cut (Johnson/Desc/Ok/PlanWritten/CutLit.lean) 76 of the 77 declare no round: their ties
are book-keeping. The 25 ties of FrameBehind are asked whole inside h.K9Cond L: one debt with the
batching kind's, not two. No soundness statement.

-/
import Johnson.P1L20R.FramePubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's ties at the 25 places behind the batching**, in the counted form. -/
def FrameBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[behindIx l]? = some q →
    TiedAtR (Fr := FrAll D) (P5J.At.N Zp cF) (P5J.mgAtAll h) P5J.fullLinks P5J.At.ps (fun a => a)
      h.toAtMg.rch (behindIx l) (q.withMap (h.toAtMg.ex L (behindIx l)))

set_option maxHeartbeats 4000000 in
/-- **The kind "frame" from its own 25 ties behind the batching**: 51 ties shown, 1 called. -/
theorem frame_of_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hB : FrameBehind h L) : h.Kind L KindName.frame :=
  frame_kind_of7b h L q₁ q₂ q₃
    { low := fun k hk q hq => by
        obtain ⟨pk, hpk, -, -⟩ := idle_at hk
        exact low_atAll h L q₁ q₂ q₃ (fence_atAll h) k
          (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hpk).1) q hq
      whole := ⟨D, (whole_atAll h L q₁ q₂ q₃).1,
        fun k _ q hq => (whole_atAll h L q₁ q₂ q₃).2 k q hq⟩
      fenceEnds := fun k hk q hq m hm _ =>
        fenceEnds_atAll h L q₁ q₂ q₃ (stands24_atAll h) k hk q hq m hm
      stands24 := stands24_atAll h
      kn := kn_atAll h
      sealTie := seal_from_atAll h L q₁ q₂ q₃
        (fun q hq => (seal_low_atAll h L q₁ q₂ q₃ (fence_atAll h) q hq).1)
        fun q hq => (seal_low_atAll h L q₁ q₂ q₃ (fence_atAll h) q hq).2
      behindTies := hB }

/-- The 25 ties out of the batching kind's condition. -/
theorem frameBehind_of_k9 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (C9 : h.K9Cond L) :
    FrameBehind h L :=
  P5J.k09_behindTies h L C9

end

end P1L20

#print axioms P1L20.frame_of_behind
#print axioms P1L20.frameBehind_of_k9
