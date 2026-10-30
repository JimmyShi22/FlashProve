-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalInAt.lean: FOR THE ITEM "totalB": `TotalInBehind` (Honest/K9/TotalFront.lean) AT
THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT EACH OF THE 25 SEGMENTS, AT own := THE TABLE's OWN GROUP: UNDER ONE
NAMED PREMISE. Statements and proofs: calls; no goal is stated.
  `ledFit_W`   the library's test "the ledger's item is asked in front of a batching and behind it", at the written
      lists: by the kernel
  `ledger_of_xk`   from the promise's five Bools (`IM.XK`) at the border behind segment l's batching: the public test on
      the ledger says yes there
  `XkAtStand`   THE NAMED PREMISE (a definition of THIS file; Honest/K9/XkFront.lean holds other things): at every stand
      of the batching the promise's five Bools hold at the state in front, at the public part of the run's input
  **`totalIn_at_head`**   under the head, l < 25, K9's seat Sd at l and `XkAtStand`: `TotalInBehind Lk p T b ((P5J.At.N
      Zp cF).group l)` at T := the thread of `lettersHead …`, b := the number of the segment's batching in the head's
      own table
PAID INSIDE, BY CALLS: Honest/K9/TotalInFill.lean's eight named facts, and its premise on the group's number: "reached"
behind the step (the frame's `thr_reach`, one step on by the member's own yes: `stepped_yes`, `batching_at_table`) · the
five Bools behind (`xk_bat_at`, Honest/K9/XkAtHead.lean; that no mark stands in front, which it asks too, is read off
the thread's form, by unfolding), and off them the ledger's test (`ledger_of_xk`) and "the members are held" · a
coefficient for each slot (the library's `LPFK9.ls_at_const` at `P5J.headSpots_at`) · the four closed facts on the plan
(the library's `P5J.AtMg.linkPlan`, `LPFK9.planB_blank`, `linkPlanFits_of_B`) · the opening, the built segment, the link
(`h.laid.opened`, the library's `TocK8.k08_scope`, Sd.link) · the group's number (by definition). For TotalInFill's
letters Fr and y (its head says what they are) the empty frame and empty strings are named.
WHAT STAYS: `XkAtStand`. Honest/K9/TotalInPaid.lean pays it, by a lemma of the frame's; this file stands without that
lemma's ground.
GROUND: beside the sealed library, the frame's files (Honest/, Honest/Law/, Honest/Law/Rule/, Honest/Thread/: live, not
sealed) and our own (Honest/K9/). At the full size and the format's second hash function alone: the head's.
SINCE THIS FILE the words "called by no line" in the head of Honest/K9/TotalInFill.lean, and "the eight others by no
line" in Honest/K9/XkAtHead.lean's, are overtaken for `totalIn_fill`, `xk_bat_at`.
WHAT IS NOT CLAIMED. `XkAtStand` at any thread. That a stand is there. No member; `totalIn_at_head` is called by
Honest/K9/TotalInPaid.lean. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalInFill
import Johnson.Desc.ProofFile.Honest.K9.XkAtHead
import Johnson.Desc.ProofFile.Honest.K9.ThrBehind
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.Link.Law.LedgerAsked
import Johnson.LPFK9R.HtinAtConstantSlots
import Johnson.LPFE1R.HeadSpotsConst
import Johnson.P5T.SortsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT moreAll mgBase)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open LPFK9.HandsAt (EW)

set_option maxRecDepth 1000000 in
/-- The library's test on the tables, at the written lists. -/
theorem ledFit_W : LinkJoin.ledFit moreAll IM.linksW IM.placesW = true := by decide +kernel

/-- From XK behind the batching: the public test on the ledger. -/
theorem ledger_of_xk {l : ℕ} (hl : l < 25) {N : Numbers} {Dp : PubData} {P : Type}
    {base : First.Pub → P × S → Bool} {z : P} {s : S}
    (hx : IM.XK N IM.linksW IM.placesW (EW Dp base z) (14 * l + IM.nAt l + 2 + 1) s = true) :
    First.ledgerB s = true := by
  obtain ⟨p, _, h1, _, h3, h4⟩ := LPFK9.HandsAt.place_W (l := l) (i := 1) hl (by omega)
  have hmem := LinkJoin.led_at moreAll IM.linksW IM.placesW ledFit_W _ l 2 p h1 h3 h4 (Or.inr rfl)
  have he : EW Dp base z (14 * l + IM.nAt l + 2 + 1) s = true := (IM.xk_parts hx).2.2.2.2
  have h5 : pubAll Dp base (.ledger l) (z, s) = true := List.all_eq_true.1 he (.ledger l) hmem
  rw [pubAll_ledger] at h5
  exact h5

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE NAMED PREMISE**: the promise's five Bools in front, at every stand. -/
def XkAtStand (l : ℕ) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) : Prop :=
  ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G →
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW
      (EW h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub) (14 * l + IM.nAt l + 2) s = true

/-- **`TotalInBehind` at the frame's own thread.** -/
theorem totalIn_at_head {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww)
    (hX : XkAtStand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l Lk p) :
    TotalInBehind Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) ((P5J.At.N Zp cF).group l) := by
  intro κ s m En ds y cols s' x' z G St
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have h9 := LPFK9.HandsAt.nAt_le l
  have hb : batchAt P5J.At.links P5J.At.ps l = 14 * l + IM.nAt l + 2 := LPFK9.batch_nAt l hl
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 St.thr.1.2.2.1.1
  have hbk : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
    rw [← hb]
    exact batching_at_table h hl Sd
  have h1 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2 + 1) (m.st.input.x.pub, s') :=
    Reach.succ hq hbk (stepped_yes St.step)
  have hx' := xk_bat_at h hl 0 (mgBase : Meaning ProofFile.InstPub WtF).pub m.st.input.x.pub (fun _ _ _ => rfl) hbk
    ⟨_, _, _, St.step.2⟩ h0 (hX κ s m En ds y cols s' x' z G St)
  obtain ⟨nH, hH⟩ := P5J.headSpots_at h
  obtain ⟨_, Xl, _, e3, _⟩ := TocK8.k08_scope h.scope h.reads O l hl
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hbd : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) + 1 = 14 * l + IM.nAt l + 2 + 1 := by
    unfold IM.nAt
    split <;> omega
  exact totalIn_fill (Fr := ⟨0, [], id, 0⟩) (fun _ => (0, []), fun _ => []) h.scope h.reads O hx Sd.link e3
    (LinkJoin.linkPlanFits_of_B (LPFK9.planB_blank O.blank e3 (h.toAtMg.linkPlan hl))) (P5J.At.N Zp cF) rfl
    m.st.input.x.pub s' (by rw [hbd]; exact h1) (ledger_of_xk hl hx')
    (LPFK9.ls_at_const h.toAtMg hH (by omega) h1) (IM.xk_parts hx').2.2.1

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ledFit_W
#print axioms ProofFile.Honest.K9.ledger_of_xk
#print axioms ProofFile.Honest.K9.totalIn_at_head
