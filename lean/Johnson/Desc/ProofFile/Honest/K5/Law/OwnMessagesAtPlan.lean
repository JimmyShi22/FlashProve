-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OwnMessagesAtPlan.lean: THREE SMALL JOINTS ON A CODE SWITCH's
OWN MESSAGES, ON PUBLIC DATA ALONE: a request's shape, the plan's places, numbers of messages: no
run, no input, no book, no lot. TWO ARE GENERAL: NO HYPOTHESIS BUT THE PLACE's MEMBERSHIP IN THE
PLAN's LIST. THE THIRD IS CONDITIONAL: under the hypothesis h, the library's head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), over one closed fact at the written request. Two
definitions, a public test with code; seven theorems.

Main names:
  `first_sender_own`: hp: the switch is the first sender (`K2.firstSender`,
    Honest/K2/ScriptLots.lean) of its message number 1 + p.sizes.kept.length + m.
  `own_in_range`: hp; hm : msgNo G.first.shape p.link 0 m = some m': m is below p.others.size - 1.
  `own_below_notices`: its last step, general in the list L: L[m]? = some M: m is below the size,
    less 1, of L's notices with one notice laid behind them.
  `momentFirst t L`: THE TEST: in the link L the messages of moment t come first: it walks the list
    that `msgNo` (Honest/LaidData.lean) reads, the link's messages with their numbers, those of
    moment t alone, and asks at its k-th member that the member's own number be k. `momentFirstAll t
    s`: that at every link of the shape s.
  `msgNo_of_momentFirst`: general in s and t: the test; msgNo s l t m = some m': m' = m.
  `momentZeroFirstW`: THE CLOSED FACT: the written ground of the code switch's numbers (`IM.prepW`,
    Johnson/IMR/SendsPinned.lean) is there, and its request passes the test at moment 0.
  `momentOneFirstW_fails`: A CONTROL: at moment 1 the same term says no.
  `own_number_head`: h; hG; msgNo G.first.shape l 0 m = some m': m' = m. Its statement names Zp, not
    h: h comes in by the line "include h in" in front of it.

What they are for. Forms of ours on a switch's lots come to a message's number m' through the seat
(`seated_at_switch_msg`, FillSwitchHead.lean in this folder: msgNo G.first.shape p.link 0 m = some
m'), and lay the lot at the switch's message 1 + p.sizes.kept.length + m. A law that ranges over m
below p.others.size - 1 and speaks of m itself meets such a form through the second and the third
joint; that the lot is one of `K2.switchMsgLots` wants the first.

How. The first two: `K2.switchPlaces`' own text (Honest/K2/Half.lean): kept is laid out of the
target's kept copies; others is the notices of the link's messages of moment 0 and one notice more.
With `Meaning.Carry.prep_facts` (Johnson/IMR/MsgsPlaces.lean), `K1.msgNo_at` and
`K1.atMoment_filter` (Honest/K1/SeatShape.lean): the steps of `switch_notice_shape`
(FillSwitchHead.lean). The third: `K2.Law.prep_at_head` (Honest/K2/Law/PlacesWritten.lean), carried
from the ground of the head's opening to G as in `places_under_head` (MaskRowWritten.lean in this
folder); `prep_facts`; the closed fact; the general law.

Limits. `first_sender_own` HOLDS AT EVERY m: `K2.firstSender` has no upper bound: beyond the
sending's size it says yes too, and means nothing there. Where the plan's list is empty hp is unmet
and the first two say nothing. THE TWO CLOSED FACTS ARE EVALUATIONS BY LEAN's KERNEL, under a lifted
limit on depth: this file replays neither by another checker. THE CONTROL SAYS THAT AT LEAST ONE
LINK OF THE WRITTEN REQUEST FAILS THE TEST AT MOMENT 1, NOT THAT EVERY LINK DOES; alone it could
also mean that the written ground is not there, which `momentZeroFirstW` shuts out; it bends the
moment, not the request: a request with a message of moment 0 behind a later one is not tried.
Nothing on what a message holds. The full size alone. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitchHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- **A PUBLIC TEST: in the link L the messages of moment t come first.** -/
def momentFirst
    (t : ℕ)
    (L : OnBytes.Params.ReqLink) :
    Bool := ((L.messages.zipIdx.filter fun x => x.1.moment == t).zipIdx).all fun y => y.1.2 == y.2

/-- **That test at every link of a request's shape.** -/
def momentFirstAll
    (t : ℕ)
    (s : OnBytes.Params.ReqShape) :
    Bool := s.link.all (momentFirst t)

/-- **The switch is the first sender of each message behind its kept copies.** No hypothesis but hp.
-/
theorem first_sender_own
    {Z : Pub}
    {G : Ground}
    {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Z G)
    (m : ℕ) :
    K2.firstSender p (1 + p.sizes.kept.length + m) = true := by
  unfold K2.switchPlaces at hp
  split at hp
  · obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    unfold K2.firstSender
    dsimp only
    rw [List.length_map, Array.length_toList]
    exact Bool.or_eq_true_iff.2 (Or.inr (decide_eq_true (by omega)))
  · cases hp

/-- **A member of a list of messages lies in front of the one notice that is laid behind theirs.**
General in the list. -/
theorem own_below_notices
    (L : List OnBytes.Params.ReqMessage)
    (x : OnBytes.OracleNotice)
    {m : ℕ}
    {M : OnBytes.Params.ReqMessage}
    (hF : L[m]? = some M) :
    m < (OnBytes.ReqFrame.notices L ++ #[x]).size - 1 := by
  have hlt : m < L.length := (List.getElem?_eq_some_iff.1 hF).1
  rw [Array.size_append]
  unfold OnBytes.ReqFrame.notices
  simpa using hlt

/-- **An own message that has a number among its link's messages lies in front of the last notice.**
No hypothesis but hp and hm. -/
theorem own_in_range
    {Z : Pub}
    {G : Ground}
    {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Z G)
    {m m' : ℕ}
    (hm : msgNo G.first.shape p.link 0 m = some m') :
    m < p.others.size - 1 := by
  unfold K2.switchPlaces at hp
  split at hp
  · rename_i P sps hP hsp
    obtain ⟨eR, -, -⟩ := _root_.Meaning.Carry.prep_facts hP
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    dsimp only at hm ⊢
    obtain ⟨M, -, hF⟩ := K1.msgNo_at _ _ _ _ _ hm
    rw [← eR] at hF
    have hF' := (congrArg (·[m]?) (K1.atMoment_filter P.z.request
      (OnBytes.reqGroups P.z.request) (sp.place.link.getD P.z.request.link.length) 0)).trans hF
    exact own_below_notices _ _ hF'
  · cases hp

/-- **Where the messages of moment t come first, the m-th of them has the number m.** General in the
shape and the moment. -/
theorem msgNo_of_momentFirst
    {s : OnBytes.Params.ReqShape}
    {t : ℕ}
    (hs : momentFirstAll t s = true)
    {l m m' : ℕ}
    (hm : msgNo s l t m = some m') :
    m' = m := by
  unfold msgNo at hm
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hm
  have hL : momentFirst t (s.link.getD l default) = true := by
    by_cases hl : l < s.link.length
    · rw [List.getD_eq_getElem _ _ hl]
      exact List.all_eq_true.1 hs _ (List.getElem_mem hl)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hl)]
      rfl
  have hy2 := List.all_eq_true.1 hL (y, m) (List.mem_zipIdx_iff_getElem?.2 hy)
  exact e.symm.trans (eq_of_beq hy2)

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT: the written ground is there, and its request passes the test at moment 0.**
An evaluation by the kernel. -/
theorem momentZeroFirstW :
    (IM.prepW.any fun P => momentFirstAll 0 P.z.request) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A CONTROL: at moment 1 the same term says no**: at least one link of the written request fails
the test there. An evaluation by the kernel. -/
theorem momentOneFirstW_fails :
    (IM.prepW.any fun P => momentFirstAll 1 P.z.request) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **Under the head the m-th message of moment 0 of a link has the number m.** CONDITIONAL: h; hG;
hm. -/
theorem own_number_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G)
    {l m m' : ℕ}
    (hm : msgNo G.first.shape l 0 m = some m') :
    m' = m := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hP : P1K2.prepOf Zp G = IM.prepW := e ▸ K2.Law.prep_at_head h.toAtMg O
  have hW := momentZeroFirstW
  cases hq : IM.prepW with
  | none =>
    rw [hq] at hW
    exact absurd hW (by simp)
  | some P =>
    rw [hq] at hW hP
    simp only [Option.any_some] at hW
    obtain ⟨eR, -, -⟩ := _root_.Meaning.Carry.prep_facts hP
    rw [eR] at hW
    exact msgNo_of_momentFirst hW hm

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.momentFirst
#print axioms ProofFile.Honest.K5.momentFirstAll
#print axioms ProofFile.Honest.K5.first_sender_own
#print axioms ProofFile.Honest.K5.own_below_notices
#print axioms ProofFile.Honest.K5.own_in_range
#print axioms ProofFile.Honest.K5.msgNo_of_momentFirst
#print axioms ProofFile.Honest.K5.momentZeroFirstW
#print axioms ProofFile.Honest.K5.momentOneFirstW_fails
#print axioms ProofFile.Honest.K5.own_number_head
