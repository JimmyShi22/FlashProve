-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/LettersFull.lean: THE STRUCTURE OF PREMISES `K6ShareLetters`
(Honest/K6/Law/Share.lean), WHOLE, AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's OWN
(Honest/Thread/FirstAt.lean: `lettersAt`). Statements and proofs by calls.

WHAT IT IS NOT. EVERY STATEMENT IS CONDITIONAL on that file's one hypothesis h : `P5J.AtMgA`, and on
nothing else but, at the top, that Lk is the first chain's link 24. (The library has a member of
that hypothesis under four premises on the three public files: `P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) FACTS ON LETTERS, DATA AND PUBLIC
NUMBERS: no state of a run stands in them, and no item is shown true. `K6ShareLetters` is a
structure of premises: to meet it is no property of the protocol. The full size and the format's
second hash function alone, as h.

  `fits_turned`     the composed meaning's parameters are the head's (`MgFitsK6`), at h's data WITH
                    THE DECODER AND THE CARRIED WORD's SENTENCE TURNED INTO ANY OTHERS
  `once_at_head`    just one oracle message of segment 24 has the mask row's message's number
  `plan_at_head`    the sub-protocol's tests on the plan accept at the public parameters
  `k6_letters_full`   **the structure's eight fields, at every Lk that is the first chain's link
                    24**

THE STRUCTURE's NUMBERS ARE FIXED HERE: lay6 := At.layout Zp, num := At.num Zp, n := At.num Zp 24 0,
rb := 0, l := 24, piece := 4, the stated runs := those of the link Lk: whoever shows the structure
of debts (`K6ShareDebts`) for the same call must show it at these. That there is such a link:
`link24_at_head` (Johnson/Desc/Kinds/Law/K6StateAtHead.lean). WHO PAYS WHAT. own, join, weights:
`k6_means_full` (Honest/K6/Law/ShareAtFull.lean). fits: `paid_at_const` (Law/K06AtConst.lean) and
`runs_at_head` (Law/K6PubMore.lean); of the eight fields of `MgFitsK6` one names the decoder, inside
`oneDec`, which turns the decoder alone, and `headPartK6` reads the request and the hidden values
alone: Lean takes the field at the turned data as it stands. head: `paid_at_const`. once:
`maskC_at_head` (Johnson/HB/LLHARD/K6MaskAtHead.lean) with `mask_of_C` (Law/K6CallsTest.lean). runs:
`six_of_link_at_head` (Law/K6StateAtHead.lean). plan: every sub-protocol of the first chain passes
its test on the plan (`flat_ok`, Johnson/P5J/FoldJ1.lean); number 341 is the seated sub-protocol
laid alone (the calls of the proof of `k6_core_at_mg`, Law/K6SeatedAtHead.lean: `k6_of`,
`k6_at_341`; `alone_planOk`, Johnson/IMR/SeatForm.lean); `seatedClaims_plan`
(Law/SeatedBridge.lean). No file of the folder lean/Johnson/Goal/ is imported by this one;
`Meaning.backReq`, which `fits_turned` names, is Johnson/Meaning/ReqBytes.lean's, not that folder's.
Over files that have not yet landed in the library: Honest/K6/Law/Share.lean, ShareAtFull.lean and
the files on threads that these import.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ShareAtFull
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.HB.LLHARD.K6MaskAtHead
import Johnson.Desc.Kinds.Law.K6SeatedAtHead
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.Desc (Chain Strs Wit Link Claim)
open VerifiableInference.Desc.First (Item S)
open VerifiableInference.Desc.Sound (mgAll mgBase MsgT namedOnce)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS At.layout At.num At.reqB At.d₀ At.decT At.EAt At.tabH At.X tokVOf
  tokHOf)
open ProofFile.Honest (ProverCoinCounts Local Placed)
open ProofFile.Honest.FirstThread (Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The composed meaning's parameters are the head's, AT THE DATA WITH TWO FIELDS TURNED**: decT',
cr1': any. (The link is opened only because `paid_at_const` is stated at one; none of its fields
that are spent here hangs on it.) -/
theorem fits_turned (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (decT' : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S →
      Option (CellsM OnBytes.Flat.numsFull))
    (cr1' : ℕ → ProofFile.InstPub × S → Strs → WtF → Prop) :
    MgFitsK6 { h.𝔇 with decT := decT', cr1 := cr1' } (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0
      tokVOf (fun a => (Meaning.backReq (At.reqB a.1)).getD At.d₀)
      (fun a y => At.decT OnBytes.secondHashFunction Zp Np cF (At.EAt Z) h.plan.shape y.cell a) h.plan.hN
      h.plan.hG (At.tabH x) tokHOf := by
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  obtain ⟨_, r2, r3, r4, _⟩ := runs_at_head (D := { h.𝔇 with decT := decT', cr1 := cr1' }) A.sorts
  exact { seg := A.seg, ns := A.ns, own := r4, join := r3, planes := r2, hid := A.hid,
          head := A.head, wt := A.wt }

/-- Just one oracle message of the head's segment has the mask row's message's number. -/
theorem once_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    namedOnce h.𝔇.arr h.𝔇.N 24 (At.num Zp 24 0) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, g1, _⟩ := AtFold.mask_of_C (maskC_at_head h)
  exact g1

/-- The sub-protocol's tests on the plan accept: the chain's own test on the plan holds the seated
sub-protocol's. -/
theorem plan_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (parOf (At.X Zp).hS (workOf (At.X Zp))).ok = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', ms, e1, e2, _, hsc, hla, _, _, _⟩ := IM.k6_of h.scope h.reads O
  have eW : Bs.G₀.W = At.X Zp := O.W
  have hm : b ∈ cF.blocksInOrder := List.mem_of_getElem? (IM.k6_at_341 h.scope h.reads O e1 e2).1
  have hp : b'.planOk = true := (IM.alone_planOk hla).symm.trans (P5J.flat_ok h.toAtMg b hm)
  exact (seatedClaims_plan (eW ▸ hsc) hp).1

/-- **THE STRUCTURE, WHOLE**, under the one hypothesis, at every Lk that is the chain's link 24. -/
theorem k6_letters_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (Lk : Link S ProofFile.Cl) (hlk : cF.links[24]? = some Lk) :
      K6ShareLetters
        (ProofFile.Honest.FirstThread.lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides
          keeps).thread (Item.formsT 24 4 "own") (Item.formsT 24 4 "join")
        (Item.formsT 24 4 "weights") id id
        (fun w => { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX }) mgBase
        (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) :=
    { own := k6_means_full h hs Q stored ans test carryX item n₁ n₂ valid rides keeps "own"
      join := k6_means_full h hs Q stored ans test carryX item n₁ n₂ valid rides keeps "join"
      weights := k6_means_full h hs Q stored ans test carryX item n₁ n₂ valid rides keeps "weights"
      fits := fun _ _ => ⟨_, _, _, _, _, _, _, fits_turned h _ _⟩
      head := fun _ _ => (paid_at_const h Lk hlk).sorts
      once := fun _ _ => once_at_head h
      runs := (P4.six_of_link_at_head h hlk).1
      plan := plan_at_head h }

#print axioms fits_turned
#print axioms once_at_head
#print axioms plan_at_head
#print axioms k6_letters_full

end VerifiableInference.Desc.Kinds.Head.Law.AtTable
