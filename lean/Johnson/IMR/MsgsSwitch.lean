-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsSwitch.lean: THE
LAST MILE OF msgs_at_cut_but's hM AT A CODE SWITCH: under THE FIRST CLAUSE of the fence on the
verifier's state in front (K2.Fence, Johnson/Top/H0/Tw/K2C/SendsOn.lean; here Fence1; fence1_of), a
yes adds as many oracle messages as the
block tells.

  K2Told: OWED HERE, A NAMED PREMISE: layTrees codes sent = some lay → the tenants of P1K2.oraclesAt
      grp codes sent number sent.size. P1K2.told_tenants (Johnson/Top/H0/Tw/K2C/ToldTenants.lean)
      says just this (k2Told_paid, Johnson/IMR/ToldPaid.lean); that file is not imported here.
  toldMsgs_k2. k2_adds_of_fence: **K2Told · Fence1 p sent s · p.sent = P1K2.oraclesAt
      p.grp codes sent · layTrees codes sent = some lay · a yes of K2.decideWith sendByL8 p from s
      to s' ⇒ s'.st.oracles.size = s.st.oracles.size + toldMsgs (codeSwitchKind p).** By yes_size.
  joined_adds: the same of the block AS IT STANDS AT A LINK (Joined, SameSpot.lean: the lot's block,
      under its name and place, with the link's "opened" behind), at a yes of its step: "opened"
      leaves the number (framesOf_three) and tells nothing.
  headLot_adds: the lot's block at the head's link (the switch with headOpened behind). alone_adds:
      a block that the seat lays alone over a lot's block.
WHO PAYS THE FENCE's FIRST CLAUSE: Johnson/IMR/MsgsPlaces.lean.
OBJECT: K2's maker, and its block at a link. USER: hM's payer. LETTERS: p, sent, codes, lay.



Compiled with the whole library.
Limits. Nothing on soundness.

-/
import Johnson.IMR.MsgsCut
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- **OWED (the plan's side at K2)**: the tenants that the lot's list of a sending's oracle messages
tells are as many as the messages announced. -/
def K2Told : Prop := ∀ (grp : Nat) (codes : Codes) (sent : Array OracleNotice) (lay : TreeLay),
  layTrees codes sent = some lay →
    ((P1K2.oraclesAt grp codes sent).map fun o => o.tenants.length).sum = sent.size

/-- The first clause of the fence K2.Fence (Johnson/Top/H0/Tw/K2C/SendsOn.lean): whatever front the
switch takes off the verifier's state announces just these messages. -/
def Fence1 (p : K2.P2) (sent : Array OracleNotice) (s : S) : Prop :=
  ∀ x, K2.FrontOf p s x → _root_.Tw.K2.switchNotices x.T x.others = sent

theorem fence1_of {p : K2.P2} {sent : Array OracleNotice} {codes : Codes} {n₀ : Nat} {s : S}
    (h : K2.Fence p sent codes n₀ s) : Fence1 p sent s := fun x hx => (h x hx).1

theorem toldMsgs_k2 (p : K2.P2) :
    toldMsgs (K2.codeSwitchKind p : Block S Unit) = (p.sent.map fun o => o.tenants.length).sum := by
  show (([p.sent, []] : List (List VerifiableInference.Desc.Oracle)).flatten.map
    fun o => o.tenants.length).sum = _
  simp

/-- **A code switch, under the fence (K2.Fence) on the verifier's state in front**: a yes adds as
many oracle messages as the block tells. -/
theorem k2_adds_of_fence (hT : K2Told) {p : K2.P2} {sent : Array OracleNotice} {codes : Codes}
    {lay : TreeLay} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hF : Fence1 p sent s)
    (hs : p.sent = P1K2.oraclesAt p.grp codes sent) (hl : layTrees codes sent = some lay)
    (h : K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size + toldMsgs (K2.codeSwitchKind p : Block S Unit) := by
  obtain ⟨x, hx, e1, -, e2, -⟩ := K2.yes_size h
  rw [e2, e1, hF x hx, toldMsgs_k2, hs, hT _ _ _ _ hl]

/-- **The switch's block as it stands at a link** (Joined, SameSpot.lean: the lot's block with the
link's "opened" behind): a yes of its step adds what it tells. -/
theorem joined_adds (hT : K2Told) {Z : ProofFile.Pub} {l : Nat} {b : Block S Cl} {a : Place}
    {nm : String} {p : K2.P2} (hj : IM.Joined Z l b (IM.under nm a (K2.codeSwitchKind p)).retype a)
    {sent : Array OracleNotice} {codes : Codes} {lay : TreeLay} {ft : Nat} {s t : S}
    {n : Nat} {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hF : Fence1 p sent s) (hs : p.sent = P1K2.oraclesAt p.grp codes sent)
    (hl : layTrees codes sent = some lay) (hy : b.step ft s rs cols = .ok (t, n)) :
    t.st.oracles.size = s.st.oracles.size + toldMsgs b := by
  obtain ⟨fs, f, m, hfs, hf, hm, -, ho, -, -⟩ := hj.step hy
  have hd := ((VerifiableInference.Desc.Sound.step_ok_iff ft _ s m rs cols n).1 hm).2.2.2
  have e1 := k2_adds_of_fence hT hF hs hl hd
  have e2 : t.st.oracles.size = m.st.oracles.size :=
    (Meaning.K2.framesOf_three rcM_three hfs f (List.mem_of_getElem? hf)).2.1 m t ho
  have e3 : toldMsgs b = toldMsgs (K2.codeSwitchKind p : Block S Unit) := by
    obtain ⟨fs', f', -, -, e⟩ := hj
    rw [e]
    show (((K2.codeSwitchKind p : Block S Unit).oracles ++ []).flatten.map
      fun o : VerifiableInference.Desc.Oracle => o.tenants.length).sum = _
    rw [List.append_nil]
    rfl
  rw [e2, e1, e3]

/-- **The lot's block at the head's link** (the switch with the step that opens the head's link
behind it): a yes adds what it tells. -/
theorem headLot_adds (hT : K2Told) {p : K2.P2} {HP : K2.HeadPar} {nm : String} {a : Place}
    {sent : Array OracleNotice} {codes : Codes} {lay : TreeLay} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hF : Fence1 p sent s)
    (hs : p.sent = P1K2.oraclesAt p.grp codes sent) (hl : layTrees codes sent = some lay)
    (h : (IM.under nm a ((K2.codeSwitchKind p : Block S Unit).andThen nm (K2.headOpened nm a HP))).decide s rs
      gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size +
      toldMsgs (IM.under nm a ((K2.codeSwitchKind p : Block S Unit).andThen nm (K2.headOpened nm a HP))) := by
  obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
  have e1 := k2_adds_of_fence hT hF hs hl h1
  have e2 : s'.st.oracles.size = m.st.oracles.size := K2.headOpenQ_size h2
  have e3 : toldMsgs (IM.under nm a ((K2.codeSwitchKind p : Block S Unit).andThen nm
      (K2.headOpened nm a HP))) = toldMsgs (K2.codeSwitchKind p : Block S Unit) := by
    show toldMsgs ((K2.codeSwitchKind p : Block S Unit).andThen nm (K2.headOpened nm a HP)) = _
    rw [toldMsgs_andThen]
    rfl
  rw [e2, e1, e3]

/-- A block that the seat lays alone over a lot's block x (carried over to the fold's type of a
claim): where a yes of x adds what x tells, so does a yes of the block. -/
theorem alone_adds {same : S → S → Bool} {b : Block S Cl} {x : Block S Unit} {name : String}
    {a : Place} (h : IM.LaidAlone same b x.retype name a) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hx : x.decide s rs gs = .ok t → t.st.oracles.size = s.st.oracles.size + toldMsgs x)
    (hy : b.decide s rs gs = .ok t) : t.st.oracles.size = s.st.oracles.size + toldMsgs b := by
  have e : toldMsgs b = toldMsgs x := by
    unfold toldMsgs
    rw [IM.alone_oracles h]
    rfl
  rw [e]
  exact hx ((IM.alone_underR h).2 s rs gs t hy)

#print axioms k2_adds_of_fence
#print axioms joined_adds
#print axioms headLot_adds
#print axioms alone_adds

end Meaning.Carry
