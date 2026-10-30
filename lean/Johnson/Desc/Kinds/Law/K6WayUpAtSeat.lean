-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean.
WHAT IT IS NOT. THAT AN OPENING OF THE IOP AS WRITTEN IN LEAN IS THERE, OR THAT THE HEAD OF A
COUNTED STATEMENT (P5J.AtMg) IS MET, IS SHOWN BY NOBODY HERE: both are premises. At the format's
second hash function OnBytes.secondHashFunction alone, the full size alone, in the goals' scope: as IM.k6_of is. No
accept is shown. Nothing on soundness, on completeness or on hiding.
WHAT IT IS. WHO PAYS TWO PREMISES OF Law/K6WayUp.lean | Law/K6YesAtMember.lean AT THE FIRST CHAIN OF
THE IOP AS WRITTEN IN LEAN: the member's form, and the state's own test on the request. Calls and
ties: no new mathematics.
  k6_member_step     at the driver's own guard (ProofFile.sameReply) and K6's address (IM.k6Place) the two
                     premises on these letters are paid: CONDITIONAL on the member's form alone: its
                     step accepts just where the bare sub-protocol's does and the test on the
                     request accepts.
  k6_member_at_seat  CONDITIONAL: in scope, at an opening: number 341, from 0, of the first chain's
                     flat list is of the form K6MemberIs at the base's public parameters, link 24.
  startOk_reached    CONDITIONAL: in scope, at an opening, where every member of the flat list
                     passes its test on the plan: at a reached state without a mark the state's own
                     test on the request accepts. WHY: the chain's start lays the request's words
                     only if they pass, else the blank state, which bears a mark; no member writes
                     them.
  k6_member_at_mg    CONDITIONAL on P5J.AtMg: the second at these letters, at P5J.At.X Zp.
LETTERS. b stands under "there is", pinned by its place in the flat list.
THE NAMESPACE IS P4, as in P4SR/K6BackAtSeat.lean, whose same_of_eq is called and beside whose
k6Back_at_seat these statements belong; the path is this folder's because they pay its premises.
CALLED: K6MemberIs.step_iff, P4.same_of_eq, IM.k6_of, IM.k6_at_341, IM.Open.W, IM.Open.public,
Meaning.K2.reqOk_of_noMark (IMR/AtReach.lean), Meaning.K2.req_at_open (LTPileR/AtGate.lean),
reqOk_of_req (Law/TokenAtEnd.lean), InScope.T_in_scope, InScope.V_public
(Goal/Meaning/HeadStartScope.lean). k6_member_at_mg goes as Law/K6SeatedAtHead.lean's k6_core_at_mg,
which keeps "narrows" of the form; this one keeps the form.
OF THE FOLDER Johnson/Goal/ it imports Goal/Meaning/HeadStartScope.lean, for the two lemmas named
above; nothing else of that folder is called.

-/
import Mathlib
import Johnson.P4SR.K6BackAtSeat
import Johnson.IMR.FlatScope
import Johnson.IMR.AtReach
import Johnson.LTPileR.AtGate
import Johnson.P5J.MgAtAll
import Johnson.Goal.Meaning.HeadStartScope
import Johnson.Desc.Kinds.Law.TokenAtEnd
import Johnson.Desc.Kinds.Law.K6WayUp

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Claim Chain FileDescription OpenedColumn)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workOf readsOf K6MemberIs)
open ProofFile (Cl)

/-- AT THE DRIVER's OWN GUARD AND K6's ADDRESS: the two premises on the letters are paid. -/
theorem k6_member_step {W : OnBytes.Model.Verify.Public} {l : Nat} {b : Block S Claim}
    (M : K6MemberIs W l ProofFile.sameReply IM.k6Place b) (ft : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) :
    b.step ft s rs cols = .ok (s', n) ↔
      (blockAt W.hS (readsOf W) (workOf W) l).step ft s rs cols = .ok (s', n) ∧
        startOk W s = true := by
  exact M.step_iff (by decide) (fun _ _ e => same_of_eq e) ft s s' rs cols n

section Opening

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- AT THE FIRST CHAIN OF THE IOP AS WRITTEN IN LEAN: number 341, from 0, of its flat list. -/
theorem k6_member_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b : Block S Cl, c.blocksInOrder[341]? = some b ∧
      K6MemberIs Bs.G₀.W 24 ProofFile.sameReply IM.k6Place b := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, hsc, hla, _, _, _⟩ := IM.k6_of hS hR O
  exact ⟨b, (IM.k6_at_341 hS hR O e1 e2).1, ms, b', b.name, hsc, hla⟩

/-- THE STATE's OWN TEST ON THE REQUEST, AT A REACHED STATE WITHOUT A MARK. CONDITIONAL: in scope,
at an opening, where every member of the flat list passes its test on the plan. -/
theorem startOk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : Nat} {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) :
    startOk Bs.G₀.W s = true := by
  have hq := Meaning.K2.reqOk_of_noMark hS hR O h hu
  have hr : s.req = OnBytes.Model.Verify.words32 z.request :=
    Meaning.K2.req_at_open O hp 0 k (z, s) h hu
  have hX := O.public
  rw [← O.W, Law.InScope.T_in_scope hS hR hX, Law.InScope.V_public hX] at hq
  exact (Law.reqOk_of_req (s := Z.s₀.withReq (OnBytes.Model.Verify.words32 z.request)) (s' := s)
    hr _ _).trans hq

end Opening

/-- AT THE PREMISES OF A COUNTED STATEMENT (P5J.AtMg, P5J/MgAtAll.lean). CONDITIONAL on them. -/
theorem k6_member_at_mg {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ b : Block S Claim, cF.blocksInOrder[341]? = some b ∧
      K6MemberIs (P5J.At.X Zp) 24 ProofFile.sameReply IM.k6Place b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, e, M⟩ := k6_member_at_seat h.scope h.reads O
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  exact ⟨b, e, eW ▸ M⟩

end P4

#print axioms P4.k6_member_step
#print axioms P4.k6_member_at_seat
#print axioms P4.startOk_reached
#print axioms P4.k6_member_at_mg
