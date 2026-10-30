-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksListLaw.lean: ON THE LIST OF THE MARKS OF THE ATTENTION
SEGMENTS' OWN ROUNDS (`k5Marks`, Johnson/Desc/ProofFile/Honest/K5/MarksList.lean): what its members
are and at which kind of place they stand: no premise; HOW MANY THEY ARE, WHICH THEY ARE, AND THAT
EACH STANDS AT THE PLACE OF A SUB-PROTOCOL OF THE FIRST CHAIN: CONDITIONAL: in the goals' scope at
an opening of the description, or under the library's head on the public input (`P5J.AtMgA`).
Lemmas. NO BOUND FOR A MARK IS SHOWN; EACH share IS A WRITTEN PAIR OF NUMBERS AND NO BOUND.

Main names:
  `k5Marks_eq`: the list is the list of `mkReads` (MarkReads.lean in this folder) and `mkLive`
    (MarkLive.lean): by unfolding alone. `mem_k5Marks`: what its members are: an iff.
  `k5Marks_place`, `k5Marks_seat`: **each stands at ⟨1, some l, 3, K5⟩, which is a mark's seat**
    (`markSeat`, Johnson/Desc/ProofFile/Honest/Law/CoverSeats.lean). No premise.
  `k5Marks_sharesOk`: no stated share has the denominator 0. No premise.
  `k5Marks_drops`: a control: where no place's group has a plan the list is empty.
  `den_ok`, `flatMap_length_const`: two helpers: the written pairs' denominator is not 0; lists of
    one length laid in a row.
  `k5Marks_open`: CONDITIONAL: the goals' scope, the files read, an opening of the description:
    **24 members; at each group g below 12 the two marks at 2 g + 1 and the group's plan are among
    them.**
  `k5Marks_at_member`: CONDITIONAL, as `k5Marks_open`: each member's place is the place of the
    sub-protocol at number 14 (2 g + 1) + 4 of the first chain's flat list, for a g below 12.
  `k5Marks_length`, `k5Marks_head`, `k5Marks_stands`: CONDITIONAL: the library's head on the public
    input and the base's return: 24 members · at each group's plan, as the laws on the two marks
    look it up, the two marks are members · **each member's place is the place of a sub-protocol
    of the first chain.**

Which form is for whom. `k5Marks_seat`, `k5Marks_length`, `k5Marks_stands`: the forms that the
frame's law on the first chain takes. `k5Marks_head`: for whoever holds a law on one of the two
marks, at that law's own look-up of the plan. `k5Marks_open`, `k5Marks_at_member`: the same in the
letters of an opening, for callers without the head; the three under the head are made of them.
`mem_k5Marks`: for proofs.

How. The places in scope: `k5Places_scope` (Johnson/Desc/First/Att/Row/K5RowSeat.lean). The plans:
`scope_plans` (Johnson/Goal/Meaning/PlanShapes.lean). Which sub-protocol stands where: `IM.k5_of`
(Johnson/IMR/K5Seat.lean), `IM.hear_at_flat`, `IM.flatIx_scope`, `IM.alone_place` (Johnson/IMR/).

Limits. No sentence on a measure stands here: nothing holds a share against its test, and no bound
for a mark (`MarkDebt`, Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean) is shown. That no OTHER
sub-protocol of the chain has a member's place is not shown here: it is `own_member_only`
(MarksData.lean in this folder). At the function `OnBytes.secondHashFunction`; the conditional ones at the
library's full size alone. h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) is a hypothesis of every
statement that names it. It can be met: at the goals' two named sets of full-size public files, as
Lean's written copies spell them, the head has a member with no premise (the side library's
`AtFullSide.Top.headMember_zFull`; at the second set `AtFullSide.Top.headMember_zGap`, and at either
set `AtFullSide.Top.headMember_named` (AtFullSide/Top/HeadMemberAtGap.lean)). Of the files on this
kind's honest side only those under AtFullSide/K5/ call these; this one does not: `k5Marks_zFull`
(AtFullSide/K5/MarksAtFull.lean) does, for `k5Marks_length` and `k5Marks_stands`. At other public
files in scope the library's `P5J.head_exists_at_name` gives a member under premises on the files,
of which the fourth follows from the third (`P5J.owed_of_live`).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.MarksList
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkReads
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkLive
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats
import Johnson.Desc.First.Att.Row.K5RowSeat
import Johnson.IMR.K5Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open P5J (AtMgA TS)

/-- **The list is the list of the two marks.** No premise; by unfolding alone. -/
theorem k5Marks_eq (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    k5Marks Zp G₀ = (H2K5.k5Places G₀).flatMap fun y =>
      match G₀.W.A[y.2.2]? with
      | some a => [mkReads y.1 a.own (Att.P.parCOf a).geo, mkLive y.1 a.own]
      | none => [] := rfl

/-- **What the members are.** No premise. -/
theorem mem_k5Marks {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground} {mk : Mark} :
    mk ∈ k5Marks Zp G₀ ↔ ∃ y ∈ H2K5.k5Places G₀, ∃ a, G₀.W.A[y.2.2]? = some a ∧
      (mk = mkReads y.1 a.own (Att.P.parCOf a).geo ∨ mk = mkLive y.1 a.own) := by
  rw [k5Marks_eq, List.mem_flatMap]
  constructor
  · rintro ⟨y, hy, hm⟩
    cases ha : G₀.W.A[y.2.2]? with
    | none =>
      rw [ha] at hm
      simp at hm
    | some a =>
      rw [ha] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact ⟨y, hy, a, ha, hm⟩
  · rintro ⟨y, hy, a, ha, hm⟩
    refine ⟨y, hy, ?_⟩
    rw [ha]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hm

/-- Each member stands at the own rounds of a segment of the first chain. No premise. -/
theorem k5Marks_place (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ k5Marks Zp G₀, ∃ l, mk.place = ⟨1, some l, 3, .K5⟩ := by
  intro mk hm
  obtain ⟨y, _, a, _, rfl | rfl⟩ := mem_k5Marks.1 hm
  · exact ⟨y.1, rfl⟩
  · exact ⟨y.1, rfl⟩

/-- **Each member stands at a mark's seat.** No premise. -/
theorem k5Marks_seat (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ k5Marks Zp G₀, markSeat mk.place = true := by
  intro mk hm
  obtain ⟨l, e⟩ := k5Marks_place Zp G₀ mk hm
  rw [e]
  rfl

/-- The written pairs' common denominator is not 0. -/
theorem den_ok (n : ℕ) : (⟨n, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).ok = true :=
  bne_iff_ne.2 (Nat.mul_ne_zero (pow_ne_zero 3 Code.pGold_prime.ne_zero)
    (pow_ne_zero 3 (pow_ne_zero 128 (by decide))))

/-- No stated share of a member has the denominator 0. No premise. It says nothing of what a share
is worth. -/
theorem k5Marks_sharesOk (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    Marks.sharesOk (k5Marks Zp G₀) = true := by
  unfold Marks.sharesOk
  rw [List.all_eq_true]
  intro mk hm
  obtain ⟨y, _, a, _, rfl | rfl⟩ := mem_k5Marks.1 hm
  · exact den_ok _
  · exact den_ok _

/-- A control: where no place's group has a plan the list is empty: so the look-up can drop a mark,
and the count below is not idle. Conditional: h: here the premise on the look-ups, not the head. -/
theorem k5Marks_drops (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (h : ∀ y ∈ H2K5.k5Places G₀, G₀.W.A[y.2.2]? = none) : k5Marks Zp G₀ = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun mk hm => ?_
  obtain ⟨y, hy, a, ha, _⟩ := mem_k5Marks.1 hm
  rw [h y hy] at ha
  cases ha

/-- Lists of one length, laid in a row. -/
theorem flatMap_length_const {α β : Type} (f : α → List β) (n : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length = n) → (l.flatMap f).length = l.length * n
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a (List.mem_cons_self ..),
      flatMap_length_const f n l fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **IN SCOPE NO MARK IS DROPPED: 24 members; and which.** Conditional: the scope; the files read;
an opening of the description. -/
theorem k5Marks_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (k5Marks Z Bs.G₀).length = 24 ∧
      ∀ g < 12, ∃ a, Bs.G₀.W.A[g]? = some a ∧
        mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo ∈ k5Marks Z Bs.G₀ ∧
        mkLive (2 * g + 1) a.own ∈ k5Marks Z Bs.G₀ := by
  have hP := H2K5.Row.k5Places_scope hS hR O.pub O.blank
  obtain ⟨-, -, -, hA⟩ := Meaning.scope_plans hS hR O.public
  refine ⟨?_, fun g hg => ?_⟩
  · have h2 : ∀ y ∈ (List.range 12).map fun g => (2 * g + 1, "A" ++ toString g, g),
        (match Bs.G₀.W.A[y.2.2]? with
          | some a => [mkReads y.1 a.own (Att.P.parCOf a).geo, mkLive y.1 a.own]
          | none => []).length = 2 := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a, ea, -⟩ := hA g (List.mem_range.1 hg)
      show (match Bs.G₀.W.A[g]? with
        | some a => [mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo, mkLive (2 * g + 1) a.own]
        | none => []).length = 2
      rw [ea]
      rfl
    rw [k5Marks_eq, hP, flatMap_length_const _ 2 _ h2, List.length_map, List.length_range]
  · obtain ⟨a, ea, -⟩ := hA g hg
    have hy : (2 * g + 1, "A" ++ toString g, g) ∈ H2K5.k5Places Bs.G₀ := by
      rw [hP]
      exact List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩
    exact ⟨a, ea, mem_k5Marks.2 ⟨_, hy, a, ea, Or.inl rfl⟩,
      mem_k5Marks.2 ⟨_, hy, a, ea, Or.inr rfl⟩⟩

/-- **Under the library's head, at the base that the maker returns, the list has 24 members**: so no
look-up drops a mark there. Conditional: h: the head; hB: the base's return. -/
theorem k5Marks_length {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (k5Marks Zp Bs.G₀).length = 24 := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact (k5Marks_open h.scope h.reads O).1

/-- **Under the head, by name, at the look-up of the laws on the two marks.** Conditional: h: the
head; hB: the base's return; hg; ea: the group's plan. -/
theorem k5Marks_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo ∈ k5Marks Zp Bs.G₀ ∧
      mkLive (2 * g + 1) a.own ∈ k5Marks Zp Bs.G₀ := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨a', ea', m1, m2⟩ := (k5Marks_open h.scope h.reads O).2 g hg
  rw [O.W] at ea'
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ea)
  exact ⟨m1, m2⟩

/-- **At which member of the first chain a mark stands.** Conditional: the scope; the files read; an
opening of the description. -/
theorem k5Marks_at_member {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ mk ∈ k5Marks Z Bs.G₀, ∃ g < 12, ∃ b,
      c.blocksInOrder[14 * (2 * g + 1) + 4]? = some b ∧ b.place = mk.place := by
  intro mk hm
  obtain ⟨y, hy, a, _, hk⟩ := mem_k5Marks.1 hm
  rw [H2K5.Row.k5Places_scope hS hR O.pub O.blank] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  have hg' : g < 12 := List.mem_range.1 hg
  obtain ⟨Lk, b, b', a', e1, e2, _, hla, _⟩ := IM.k5_of hS hR O g hg'
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g + 1) (by omega) 2,
    show 14 * (2 * g + 1) + 2 + 2 = 14 * (2 * g + 1) + 4 by omega] at hfl
  have hp : b.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := IM.alone_place hla
  rcases hk with rfl | rfl
  · exact ⟨g, hg', b, hfl, hp⟩
  · exact ⟨g, hg', b, hfl, hp⟩

/-- **Under the head each member's place is the place of a sub-protocol of the first chain**: so no
mark stands where nothing of the chain would ask it. Conditional: h: the head; hB: the base's
return. -/
theorem k5Marks_stands {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ mk ∈ k5Marks Zp Bs.G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  intro mk hm
  obtain ⟨g, _, b, hb, hp⟩ := k5Marks_at_member h.scope h.reads O mk hm
  exact ⟨b, List.mem_of_getElem? hb, hp⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Marks_eq
#print axioms ProofFile.Honest.K5.mem_k5Marks
#print axioms ProofFile.Honest.K5.k5Marks_place
#print axioms ProofFile.Honest.K5.k5Marks_seat
#print axioms ProofFile.Honest.K5.den_ok
#print axioms ProofFile.Honest.K5.k5Marks_sharesOk
#print axioms ProofFile.Honest.K5.k5Marks_drops
#print axioms ProofFile.Honest.K5.flatMap_length_const
#print axioms ProofFile.Honest.K5.k5Marks_open
#print axioms ProofFile.Honest.K5.k5Marks_length
#print axioms ProofFile.Honest.K5.k5Marks_head
#print axioms ProofFile.Honest.K5.k5Marks_at_member
#print axioms ProofFile.Honest.K5.k5Marks_stands
