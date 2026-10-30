-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/AllFrontAtStandAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's
SIDE, AT THE STANDS OF THE HONEST THREAD: `AllFrontAtStand`
(Johnson/Desc/ProofFile/Honest/K8/ValuesJoin.lean), THE PREMISE hFront OF THAT FILE's THREE
SENTENCES, AT ALL 25 SEGMENTS, FROM TWO NAMED PREMISES: `ChainThread` (K8BehindTop.lean) AND
`LeftListAtStand` (LeftOverOfList.lean), BOTH PAID BY NOBODY. One lemma, one implication; none of
the library's goals.

  `funs_shown_at_all` the scope · the files read · an opening of the description · l < 25 · a state
                   that the chain's own blocks reach at 14 l + (if l = 24 then 11 else 9) ⊢ there
                   are funs with s.funs? = some funs
  **`allFrontAtStand_of_list`** the scope · the files read · the opening · the description's test on
                   its plan · l < 25 · ChainThread T b c Z l · LeftListAtStand Lk p T b ⊢
                   AllFrontAtStand Lk p T b: at every stand the state in front shows the test's
                   data, a ledger and the tables' routines; the data have heard some g; there are
                   nbW, Wn with AllFront tl F g nbW Wn; and the link's list has a member for each
                   array of the ledger
By: `allFront_at_all` (Johnson/Desc/K8/Honest/AllFrontAtAll.lean) · `funs_shown_at_batch`
(LeftOverOfList.lean: l < 24) · the library's LinkJoin.headSkel_at_batch
(Johnson/Desc/First/Link/Law/HeadSkel.lean: 347) · IM.ground_gets · `reach_below`
(Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean), called at its statement · the library's
`reach_raw`.
IT GOES PAST THE ELDER ROAD: `allFrontAtStand_of` (FrontOfReach.lean) has the same end from
`LeftOverAtStand`, which `leftOverAtStand_of_list` (LeftOverOfList.lean) pays at l < 24 from the
same two premises: at l < 24 the two roads meet; at l = 24 this is the only one.
WRITTEN A FURTHER TIME: the three lines from a stand to a reached state are those of
`leftBelowAtStand_of_name` (LeftOverOfName.lean), less the case on l.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
two lines, on numbers of segments alone.
Limits. AN IMPLICATION STILL: `ChainThread` AND `LeftListAtStand` ARE PAID BY NOBODY. NO MEMBER:
where there is no stand all is idle. IN SCOPE ALONE: the full size; the first chain. No prover
stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftOverOfList
import Johnson.Desc.K8.Honest.AllFrontAtAll
import Johnson.Desc.First.Link.Law.HeadSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At a state reached in front of a segment's batching the tables' routines are shown, at all 25
segments: the library's three laws joined. -/
theorem funs_shown_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ funs : Array HFun, s.funs? = some funs := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨funs, -, hf, -⟩ := LinkJoin.headSkel_at_batch hS hR O (z := z) (s' := s) h
    exact ⟨funs, hf⟩
  · rw [if_neg h24] at h
    exact funs_shown_at_batch hS hR O (by omega) h

variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

/-- **THE PREMISE OF THE THREE SENTENCES, AT ALL 25 SEGMENTS, FROM TWO NAMED PREMISES.** -/
theorem allFrontAtStand_of_list (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) (C : ChainThread T b c Z l) (hL : LeftListAtStand Lk p T b) :
    AllFrontAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  have e := (IM.ground_gets hS hR O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_below T (ProofFile.startS Z) q C.len hq C.stored hSt.thr
  rw [C.ft, C.bs, C.border] at r
  obtain ⟨tl, Fk, g, nbW, Wn, ht, hF, hg, D⟩ := allFront_at_all hS hR O hOk hl e3 r
  obtain ⟨funs, hf⟩ := funs_shown_at_all hS hR O hl (reach_raw r)
  exact ⟨tl, Fk, funs, g, nbW, Wn, ht, hF, hf, hg, D,
    fun a0 h0 => hL κ s m En ds y cols s' x z G hSt Fk a0 hF h0⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.funs_shown_at_all
#print axioms ProofFile.Honest.K8.allFrontAtStand_of_list
