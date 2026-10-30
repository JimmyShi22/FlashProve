-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SayOwed.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the named premise `SayOwed` of the statement
on the debts of the member that stands at an attention segment's own rounds
(Honest/K5/Law/Exchange.lean): along every step of that member, at every continuation of the
challenges, what the kind's claims say holds in the item's own world. One statement with its proof:
a joining of lemmas.

What is joined: `sayAt_member` (Honest/K5/Law/SayMember.lean); that each written reader's form meets
the honest side's value, at the head (`meets_head`, Honest/K5/Law/AddrInAt.lean); the step's yes as
the kind's hearing and lay (`seated_decides`, `behind_is`, Honest/K5/Law/Accepted.lean;
`behind_inj`, Johnson/Desc/First/Att/K05BehindOk.lean); what `Thr` in front gives at the head's
letters (Honest/K5/Law/Front.lean, Behind.lean); the ledger's sizes and the stated functions
(Johnson/Desc/K5/Honest/Law/DoorAtHead.lean, AttAtHead.lean); the mask row and the world
(Honest/K5/Law/Slots.lean, SayParts.lean); the public premises
(Johnson/Desc/K5/Honest/Law/PublicAtHead.lean).

THE PREMISES THAT ARE LEFT beside the head and the seat: the three ties between the witness and the
honest side (`K5Script`), WHICH ARE NOT SHOWN; the seat's public data are the plan's; and hV:
whatever input the thread's letter valid admits has cells that meet the library's three families of
identities (`IdnOwed`, Honest/K5/Law/IdnAt.lean), WHICH IS SHOWN OF NO valid. A like end
(`SayOwedT`, with the thread a variable) without `IdnOwed`: `sayOwedT_of₂`,
Honest/K5/Law/Idn12/SayOwedT2.lean: in its stead it takes the test T.fits and `HoldsOwed`, WHICH IS
SHOWN OF NO valid.
Main name:
  `sayOwed_of`

Limits. The head is a hypothesis. At the function OnBytes.secondHashFunction, of which nothing is asked here; at
the library's full size alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SayMember
import Johnson.Desc.ProofFile.Honest.K5.Law.Exchange
import Johnson.Desc.ProofFile.Honest.K5.Law.AddrInAt
import Johnson.Desc.ProofFile.Honest.K5.Law.IdnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Strs Chain)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (public_at_head front_at_head stated_at_head)
open ProofFile.Honest.FirstThread (Script WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE NAMED PREMISE `SayOwed` OF THE STATEMENT ON THE MEMBER's DEBTS**
(Honest/K5/Law/Exchange.lean: along every step of the member at the border, at every continuation,
what the claims say holds in the item's own world), under the library's one head on the public
input. CONDITIONAL on: the head h; g is below 12, and a is the plan of group g; the half's seat
(Hs); THE THREE TIES BETWEEN THE WITNESS AND THE HONEST SIDE (Sc), at the group's plan and in the
letters in which the item's sentence reads the witness, WHICH ARE NOT SHOWN; the seat's public
data are the plan's shape and own numbers (hP); AND: WHATEVER INPUT THE LETTER valid ADMITS HAS
CELLS THAT MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES (hV: `IdnOwed`,
Honest/K5/Law/IdnAt.lean), WHICH IS SHOWN OF NO valid. -/
theorem sayOwed_of {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (Sc : K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hP : Z5.P = ⟨a.S, a.own⟩)
    (hV : IdnOwed valid cells Z5) :
    SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a := by
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' att hd5 G gL e hgL es i K hin
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att', hd5', G', e', hh, es'⟩ := behind_is _ Hs Dc hd hS
  obtain rfl : att' = att := by
    rw [e] at e'
    cases e'
    rfl
  obtain ⟨rfl, rfl, -, -⟩ := P.behind_inj (es'.symm.trans es)
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  obtain ⟨_, _, _, _, _, _, hz⟩ := front_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl
    _ _ (open8_at hg) hr hu hon e
  have St := stated_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr
    hu hon e hd5' G'
  have hD := mask_behind (s := s) (own := h.𝔇.pubD.N.sent (2 * g + 1) 0)
    (rdOf := seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) hS.1 att' G' h.𝔇.St.at1 St.mask ds'
  obtain ⟨MP, MU, M5, MV, M7, M8⟩ := meets_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl
    _ _ (open8_at hg) hr hu hon Hs Sc hT hS.1 e hz hh hP ds' hgL hin
  have hpairs : a.own.pairs ≠ 0 := by
    have h0 := Dc.plan
    unfold P.planOk at h0
    simp only [Bool.and_eq_true, bne_iff_ne] at h0
    have ex : (parAt Zp g a).own = a.own := Hs.own.trans (by rw [hP])
    rw [← ex]
    exact h0.1.2
  exact sayAt_member Hs Sc hT hd hS.1 e hD hz hh hP (public_at_head h hg ha) hpairs
    (atIdn_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hV hT) hgL hin MP MU M5 MV
    M7 M8

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sayOwed_of
