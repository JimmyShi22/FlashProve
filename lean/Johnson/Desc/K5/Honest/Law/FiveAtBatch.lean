-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FiveAtBatch.lean: CONDITIONAL, on «reached», AND NOTHING HERE SAYS THAT
ANY STATE IS REACHED: AT EVERY STATE THAT THE FIRST CHAIN's OWN SUB-PROTOCOLS REACH IN FRONT OF AN
ATTENTION SEGMENT's BATCHING, THE STATE HOLDS WHAT THE SEGMENT's OWN ROUNDS HANDED ON, AND THE START
FORM OF EACH SUMCHECK IN IT NAMES NO ENTRY (`K5Law.HeardPlain`,
Johnson/Desc/First/Att/Claims/HeardPlain.lean). Under the goals' scope, the files read and an
opening of the description (`IM.Open`) alone: no head on the public input, no test on the plan, no
premise on the ledger. On the verifier's chain alone.

Why. A bound for the batching behind a segment asks this of the state in front of the batching, at
the twelve attention segments. Kin in the library, at the segment's other end: `heard5_none_at`
(Johnson/IMR/UnheardAt.lean): in scope, at an opening, for l below 24: wherever a fold over the
first 14 l + 3 sub-protocols returns and the open part is an attention segment's, nothing is held
yet. This file has the field laid at two numbers: 14 l + 5 (`heard_behind_own`) and 14 l + 9
(`five_at_batch`); of the three numbers between no theorem here speaks.

The five sub-protocols, by their numbers in the first chain's flat list, l := 2 g + 1:
  14 l + 4  the segment's own rounds: its yes lays what the hearing returned;
  14 l + 5  the sending of the reads with its quiet step;  14 l + 6  the smallness test's draw;
  14 l + 7  the sending of the digits;  14 l + 8  the lookup on the digits: these four leave it.

How. Which block stands at which number: the library's `IM.k5_of`, `IM.k1_reads_of`,
`IM.k8_of_attention`, `IM.k1_digits_of`, `IM.k3_of` (Johnson/IMR/), `IM.hear_at_flat` and
`IM.flatIx_scope`. That the four leave the reading `S.heard5?`:
Johnson/Desc/K5/Honest/Law/Heard5Leaves.lean, through `alone_retype_under`
(Johnson/P1K8R/OrderAtSeat.lean), `IM.alone_underR` and `leaves_of_under`
(Johnson/Desc/Sound/HearsOnce.lean). Back along «reached»: `reach_leaves`
(Johnson/Desc/First/Link/Law/ReachLeaves.lean), then one step by `reach_pred`
(Johnson/Road/K4/FunsThirdReached.lean). The yes of the own rounds' block: `IM.k5_yes`, `k5AtN_is`,
`decide_lays`, `seatSO_lay` (Johnson/Desc/First/Att/). `HeardPlain` of what the hearing returned:
Johnson/Desc/K5/Honest/Law/PlainOfHear.lean.

Main names:
  `reads_at5`, `draw_at6`, `digits_at7`, `look_at8`: the four members, each with its number.
  `stretch_leaves_heard5`: the four, by number.
  `heard_behind_own`: at every state reached right behind the segment's own rounds.
  `five_at_batch`: **at every state reached in front of the batching.**
  `five_reached`: the same at a segment's number l below 25, in the form «for every group g and plan
    with l = 2 g + 1».
  `five_wrapped`: **the same at a state that the wrapped sub-protocols reach.**

Limits. «REACHED» IS A PREMISE: nothing here says that any state is reached at these numbers; where
none is, the theorems say nothing. Reached by the sub-protocols' own steps (`Reach`,
Johnson/Top/H0/Walk/Reach.lean); what the wrapped sub-protocols reach is reached so (`reach_raw`
there). Nothing on the ledger, on the slots that the forms name, or on any other field of what was
heard. At the function `OnBytes.secondHashFunction`, of which nothing is asked here; in the goals' scope alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PlainOfHear
import Johnson.Desc.K5.Honest.Law.Heard5Leaves
import Johnson.IMR.K5Seat
import Johnson.IMR.K1Scope
import Johnson.IMR.K8Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.P1K8R.OrderAtSeat
import Johnson.Desc.Sound.HearsOnce
import Johnson.Desc.First.Link.Law.ReachLeaves
import Johnson.Road.K4.FunsThirdReached
import Johnson.Desc.First.Att.K05LawGuard
import Johnson.Desc.First.Att.K05LeavesTl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (reach_leaves)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open P1K8S (alone_retype_under)
open K5Law (HeardPlain)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The sending of the reads with its quiet step, at its number. Conditional: the scope; the files
read; the opening; hg. -/
theorem reads_at5 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g + 1) + 5]? = some b ∧ b.Leaves S.heard5? := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, _, _, hla⟩ :=
    IM.k1_reads_of hS hR O (2 * g + 1) (by omega)
  have e3 : IM.k1Ix (2 * g + 1) false = 3 := by
    show 3 + (if 2 * g + 1 = 24 then 1 else 0) = 3
    rw [if_neg (by omega)]
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) (IM.k1Ix (2 * g + 1) false), e3,
    show 14 * (2 * g + 1) + 3 + 2 = 14 * (2 * g + 1) + 5 by omega] at hfl
  exact ⟨b, hfl, leaves_of_under (alone_retype_under hla) (k1Reads_leaves5 _ _ _ _ _ _)⟩

/-- The smallness test's draw, at its number. Conditional: as `reads_at5`. -/
theorem draw_at6 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g + 1) + 6]? = some b ∧ b.Leaves S.heard5? := by
  obtain ⟨Lk, b, Xl, _, e1, e2, _, hla, _⟩ := IM.k8_of_attention hS hR O g hg
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) 4,
    show 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 by omega] at hfl
  exact ⟨b, hfl, fun s rs gs s' hd =>
    draw_leaves5 _ s rs gs s' ((IM.k8_yes hla s s' rs gs).1 hd).1⟩

/-- The sending of the digits, at its number. Conditional: as `reads_at5`. -/
theorem digits_at7 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g + 1) + 7]? = some b ∧ b.Leaves S.heard5? := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, _, _, hla⟩ :=
    IM.k1_digits_of hS hR O (2 * g + 1) (by omega)
  have e3 : IM.k1Ix (2 * g + 1) true = 5 := by
    show 5 + (if 2 * g + 1 = 24 then 1 else 0) = 5
    rw [if_neg (by omega)]
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) (IM.k1Ix (2 * g + 1) true), e3,
    show 14 * (2 * g + 1) + 5 + 2 = 14 * (2 * g + 1) + 7 by omega] at hfl
  exact ⟨b, hfl, leaves_of_under (alone_retype_under hla) (commitAtS_leaves5 _ _ _ _)⟩

/-- The lookup on the digits, at its number. Conditional: as `reads_at5`. -/
theorem look_at8 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ b, c.blocksInOrder[14 * (2 * g + 1) + 8]? = some b ∧ b.Leaves S.heard5? := by
  obtain ⟨Lk, b, b', e1, e2, hb', hla⟩ := IM.k3_of hS hR O (2 * g + 1) (by omega) true
  have hix : IM.k3Ix (2 * g + 1) true = 6 := by
    show (if true = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) (IM.k3Ix (2 * g + 1) true), hix,
    show 14 * (2 * g + 1) + 6 + 2 = 14 * (2 * g + 1) + 8 by omega] at hfl
  exact ⟨b, hfl, leaves_of_under (IM.alone_underR hla).2 (theStated_leaves_heard5 hb')⟩

/-- **The four members between the segment's own rounds and its batching leave what these rounds
handed on.** Conditional: as `reads_at5`. -/
theorem stretch_leaves_heard5 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∀ j, 14 * (2 * g + 1) + 5 ≤ j → j < 14 * (2 * g + 1) + 5 + 4 →
      ∀ b, c.blocksInOrder[j]? = some b → b.Leaves S.heard5? := by
  intro j h1 h2 b hb
  obtain ⟨b5, f5, w5⟩ := reads_at5 hS hR O hg
  obtain ⟨b6, f6, w6⟩ := draw_at6 hS hR O hg
  obtain ⟨b7, f7, w7⟩ := digits_at7 hS hR O hg
  obtain ⟨b8, f8, w8⟩ := look_at8 hS hR O hg
  have hj : j = 14 * (2 * g + 1) + 5 ∨ j = 14 * (2 * g + 1) + 6 ∨ j = 14 * (2 * g + 1) + 7 ∨
      j = 14 * (2 * g + 1) + 8 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · exact Option.some.inj (f5.symm.trans hb) ▸ w5
  · exact Option.some.inj (f6.symm.trans hb) ▸ w6
  · exact Option.some.inj (f7.symm.trans hb) ▸ w7
  · exact Option.some.inj (f8.symm.trans hb) ▸ w8

/-- **At every state reached right behind the segment's own rounds.** Conditional: as `reads_at5`;
h: the state is reached at 14 (2 g + 1) + 5. -/
theorem heard_behind_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 5) (z, s)) :
    ∃ hd, s.heard5? = some hd ∧ HeardPlain hd := by
  obtain ⟨z', s4, s', b₀, e, _, hb, hy⟩ := reach_pred (k := 14 * (2 * g + 1) + 4) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, b', a, e1, e2, hat, hla, _⟩ := IM.k5_of hS hR O g hg
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) 2,
    show 14 * (2 * g + 1) + 2 + 2 = 14 * (2 * g + 1) + 4 by omega] at hfl
  obtain rfl : b = b₀ := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.k5_yes hla s4 _ rs gs).1 hd).1
  obtain ⟨a', _, eb⟩ := Att.P.k5AtN_is _ _ _ _ _ hat
  subst eb
  have hd'' : Att.P.decide Att.P.seatSO (Att.P.parO Bs.G₀.W (2 * g + 1) a' _) s4 rs = .ok _ := hd'
  obtain ⟨_, F₀, h5, G, _, hh, l2⟩ := (Att.P.decide_lays Att.P.seatSO _ _ _ _).1 hd''
  obtain ⟨att, _, rfl⟩ := Att.P.seatSO_lay l2
  exact ⟨h5, rfl, heardPlain_of_hear hh⟩

/-- **AT EVERY STATE REACHED IN FRONT OF AN ATTENTION SEGMENT's BATCHING: what the segment's own
rounds handed on is held, and no start form in it names an entry.** Conditional: the scope; the
files read; the opening; hg; h: the state is reached at 14 (2 g + 1) + 9. -/
theorem five_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ hd, s.heard5? = some hd ∧ HeardPlain hd := by
  obtain ⟨s5, h5, e⟩ := reach_leaves 0 c.blocksInOrder (ProofFile.startS Z) S.heard5? (14 * (2 * g + 1) + 5) 4
    (stretch_leaves_heard5 hS hR O hg) (z, s) h
  obtain ⟨hd, a1, a2⟩ := heard_behind_own hS hR O hg h5
  exact ⟨hd, e.trans a1, a2⟩

/-- The same at a segment's number l below 25, at the number of the flat list at which that
segment's batching stands: for every group g with l = 2 g + 1 and every plan of that group.
Conditional: the scope; the files read; the opening; hl; h: the state is reached there. The plan is
not spent. -/
theorem five_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∀ (g : ℕ) (Ap : Attention.Plan), l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap →
      ∃ hd, s.heard5? = some hd ∧ HeardPlain hd := by
  intro g _ e _
  subst e
  rw [if_neg (by omega)] at h
  exact five_at_batch hS hR O (by omega) h

/-- **The same at a state that the WRAPPED sub-protocols reach there** ("below b": b behind the test
that every word shown is below the prime, Johnson/Desc/Sound/ChainRule.lean): what these reach the
sub-protocols' own steps reach (`reach_raw`). Conditional: the scope; the files read; the opening;
hl; w: there is a public part at which the state is so reached. -/
theorem five_wrapped (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {s : S}
    (w : ∃ z : ProofFile.InstPub, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∀ (g : ℕ) (Ap : Attention.Plan), l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap →
      ∃ hd, s.heard5? = some hd ∧ HeardPlain hd := by
  obtain ⟨z, h⟩ := w
  exact five_reached hS hR O hl (reach_raw h)

end H2K5.Honest

#print axioms H2K5.Honest.reads_at5
#print axioms H2K5.Honest.draw_at6
#print axioms H2K5.Honest.digits_at7
#print axioms H2K5.Honest.look_at8
#print axioms H2K5.Honest.stretch_leaves_heard5
#print axioms H2K5.Honest.heard_behind_own
#print axioms H2K5.Honest.five_at_batch
#print axioms H2K5.Honest.five_reached
#print axioms H2K5.Honest.five_wrapped
