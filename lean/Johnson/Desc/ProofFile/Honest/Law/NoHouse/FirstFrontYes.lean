-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FirstFrontYes.lean: the front of a later link's first call
accepts, at every reached state without a mark.

The first hearing member of a link behind link 0 begins with the same text, `Tw.K2.firstFront`: a
first message is due (guard F1), the link is not link 0 (F0), the shape has the link (F2), the list
of groups has the link's (F3), and a new group can be opened (F4 to F6). At the head's link that
text stands inside `headFrontQ`, with two guards in front (B0, W0) and the record's own entering
behind. The library's laws start from these texts' accepts. To show that the honest prover's run is
accepted one needs the accepts themselves. Here they follow from the reach, the library's facts on
every reached state, and one test with code on the public parameters. Lemmas only; no definition.

  `newGroupG_yes`, `firstFront_yes`, `headFrontQ_yes`   the three texts, one by one
  `firstFront_at`   in the goals' scope, at a state reached in front of the first hearing member of
      link l + 1, l < 24, that bears no mark: `firstFront` accepts
  `headFront_at`    the same for `headFrontQ`, at number 338
  `groupL_written`  the test on the public parameters accepts at the written codes and shape
  `head_unheard`, `head_unmarked`, `head_enters`   at the first chain's thread under the library's
      head, at border 338: no reply is held; no mark; `headFrontQ` accepts

Who pays what. F1, B0, W0 and the link's number: `first_due_at`
(Honest/Law/NoHouse/CallsBetween.lean). F2: W0 says it. F3: the groups are the shape's
(`Meaning.K2.recAll_all`, Johnson/IMR/AtReach.lean), one more than the links
(`Meaning.Carry.reqGroups_size`, Johnson/IMR/MsgsPlaces.lean). F4 to F6 read the codes and two
numbers of the shape alone (`Ground.groupL`, Johnson/Desc/First/Base/Ground.lean): these are the
public ones at a reached state, and the test on them is a premise in scope and is evaluated by
Lean's kernel at the written values. "No reply is held": the library's `IM.unheard_reach`
(Johnson/IMR/ReplyNatField.lean).

Limits. In the goals' scope, at the format's second hash function; the last three at the full size alone,
with the library's head as a premise. These are laws from a reach: where no state is reached they
say nothing. What stands behind `firstFront` in a member's text is not treated. None is one of the
library's goals. Nothing is said on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.CallsBetween
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.IMR.AtReach
import Johnson.IMR.MsgsPlaces
import Johnson.IMR.ReplyNatField
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Desc.Sound.K11Tests.LettersSevenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_iff)
open VerifiableInference.Desc.Ground (groupL newGroupL)
open Johnson.Desc.First.Walk (firstDue)
open Johnson.Desc.First.Walk.Props (firstDue_iff)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-! ## 1 The three texts -/

/-- A new group can be opened where the test on the codes accepts. -/
theorem newGroupG_yes {S₀ : OnBytes.Statement} {code maskCode : Nat}
    (h : VerifiableInference.Desc.Ground.ok (groupL S₀.codes code maskCode) = true) :
    ∃ y, Tw.K2.newGroupG S₀ code maskCode = .ok y := by
  have h' : VerifiableInference.Desc.Ground.ok
      (newGroupL (Tw.K2.dOf S₀).st code maskCode) = true := h
  unfold Tw.K2.newGroupG VerifiableInference.Desc.Ground.newGroupP
  rw [if_pos h']
  exact ⟨_, rfl⟩

/-- The front of a later link's first call accepts. -/
theorem firstFront_yes {S₀ : OnBytes.Statement} {f : OnBytes.ReqFrame} (h1 : f.next = .first)
    (h0 : f.link ≠ 0) (h2 : f.link < f.shape.link.length) (h3 : f.link < f.groups.size)
    (h4 : VerifiableInference.Desc.Ground.ok
      (groupL S₀.codes f.shape.code f.shape.maskCode) = true) :
    ∃ x, Tw.K2.firstFront S₀ f = .ok x := by
  obtain ⟨y, hy⟩ := newGroupG_yes h4
  exact ⟨_, (Tw.K2.firstFront_iff S₀ f _).2 ⟨_, _, y.1, y.2,
    ⟨h1, h0, List.getElem?_eq_getElem h2, Array.getElem?_eq_getElem h3, hy, rfl⟩⟩⟩

/-- The head's link's front accepts. -/
theorem headFrontQ_yes (tl : OnBytes.Model.HTailF2) {s : S} (hB : s.atBetween = true)
    (hW : firstDue s.check = true) (hx : ∃ x, Tw.K2.firstFront s.st s.check.frame = .ok x)
    (hm : s.failed = none) : ∃ t, headFrontQ tl s = .ok t := by
  obtain ⟨x, hx⟩ := hx
  have hh : ∃ a, (s.enterHead tl).here = .head a := by
    unfold VerifiableInference.Desc.First.S.enterHead
    rw [if_pos hB]
    exact ⟨_, rfl⟩
  have hf : (s.enterHead tl).failed = none := by
    unfold VerifiableInference.Desc.First.S.enterHead
    rw [if_pos hB]
    exact hm
  obtain ⟨a, ha⟩ := hh
  exact ⟨_, (headFrontQ_iff tl s _).2 ⟨x, _, a,
    ⟨hB, hW, hx, (VerifiableInference.Desc.First.S.unmarked_ok _ _).2 ⟨rfl, hf⟩, ha, rfl⟩⟩⟩

/-! ## 2 Along the reach, in the goals' scope -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In front of the first hearing member of link l + 1 the front of the first call accepts.** -/
theorem firstFront_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : Nat} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (l + 1) + 2) (z, s)) (hm : s.failed = none)
    (hc : VerifiableInference.Desc.Ground.ok
      (groupL Z.first.codes Z.first.shape.code Z.first.shape.maskCode) = true) :
    ∃ x, Tw.K2.firstFront s.st s.check.frame = .ok x := by
  obtain ⟨⟨-, hD, hL⟩, hn⟩ := first_due_at hS hR O hl R
  have RA := Meaning.K2.recAll_all hS hR O hp R hm
  refine firstFront_yes hn (by rw [hL]; omega) hD.2 ?_ ?_
  · have h2 := hD.2
    rw [RA.walk.shape] at h2
    rw [RA.walk.groups, Meaning.Carry.reqGroups_size]
    omega
  · rw [RA.codes, RA.walk.shape]
    exact hc

/-- **In front of the member that hears the reply the head's link's front accepts.** -/
theorem headFront_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : ProofFile.InstPub} {s : S}
    (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) 338 (z, s)) (hm : s.failed = none)
    (hc : VerifiableInference.Desc.Ground.ok
      (groupL Z.first.codes Z.first.shape.code Z.first.shape.maskCode) = true)
    (tl : OnBytes.Model.HTailF2) : ∃ t, headFrontQ tl s = .ok t := by
  have R' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (23 + 1) + 2) (z, s) := R
  obtain ⟨⟨hB, hD, -⟩, -⟩ := first_due_at hS hR O (l := 23) (by omega) R'
  exact headFrontQ_yes tl hB ((firstDue_iff _).2 hD)
    (firstFront_at hS hR O hp (l := 23) (by omega) R' hm hc) hm

end

/-! ## 3 Under the library's head, at the first chain's thread -/

/-- The test on the public parameters accepts at the written codes and shape. By the kernel. -/
theorem groupL_written : VerifiableInference.Desc.Ground.ok
    (groupL Johnson.G.codesFull2 VerifiableInference.Desc.ReqLit.shapeFull.code
      VerifiableInference.Desc.ReqLit.shapeFull.maskCode) = true := by decide +kernel

namespace FirstThread
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the test on the public parameters accepts. -/
theorem groupL_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    VerifiableInference.Desc.Ground.ok
      (groupL Zp.first.codes Zp.first.shape.code Zp.first.shape.maskCode) = true := by
  rw [LT28.K11Tests.codes_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1,
    (P5J.written_at_head h.toAtMg).2]
  exact groupL_written

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Up to border 338 the state at which the thread stands holds no reply. -/
theorem head_unheard {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length) (h338 : b ≤ 338)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.out.reply = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact IM.unheard_reach h.scope h.reads O h338
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)

/-- The state at which the thread stands bears no mark. -/
theorem head_unmarked {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    s.failed = none := by
  have h1 : s.failed.isNone = true := hT.2.2.1.1
  exact Option.isNone_iff_eq_none.1 h1

/-- **At border 338 the head's link's front accepts**, at whatever tail. -/
theorem head_enters {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : 338 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 338 k s m E)
    (tl : OnBytes.Model.HTailF2) : ∃ t, headFrontQ tl s = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact headFront_at h.scope h.reads O (P5J.flat_ok h.toAtMg)
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (head_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT) (groupL_at_head h) tl

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.newGroupG_yes
#print axioms ProofFile.Honest.firstFront_yes
#print axioms ProofFile.Honest.headFrontQ_yes
#print axioms ProofFile.Honest.firstFront_at
#print axioms ProofFile.Honest.headFront_at
#print axioms ProofFile.Honest.groupL_written
#print axioms ProofFile.Honest.FirstThread.groupL_at_head
#print axioms ProofFile.Honest.FirstThread.head_unheard
#print axioms ProofFile.Honest.FirstThread.head_unmarked
#print axioms ProofFile.Honest.FirstThread.head_enters
