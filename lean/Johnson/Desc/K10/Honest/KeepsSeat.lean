-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/KeepsSeat.lean: THE CLOSING OF A SEGMENT (K10): `K10Keeps`
(Johnson/Desc/K10/Honest/Keeps.lean) PAID AT THE VERY BLOCK THAT THE DESCRIPTION SEATS: at each
link l < 25 of the first chain, by the block's number in the chain's flat list; and at each place
of the kind K10. Lemmas on the verifier's own text; no honest side's frame in them; none of the
library's goals. Of this folder it imports Keeps.lean alone.

WHICH BLOCK STANDS THERE IS THE LIBRARY's OWN LAW, other authors' (`IM.close_of`,
Johnson/IMR/CloseSeat.lean; by places `P5J.k10_block_at`, Johnson/P5J/K10Seat.lean): of a link's
three closing blocks the middle one (number 1, counted from 0) IS `IM.seatedAs ProofFile.sameReply
x.retype b.name a` (Johnson/IMR/SeatForm.lean), ALONE, with x the middle member of `K9.closeOf p
Q`: the lifted block, retyped, under the wrapper on the mark of failure, under its own name, at
the driver's address, under the driver's guard on the seat; NO BLOCK IS JOINED BEHIND IT. THE
LIBRARY HOLDS MORE OF THIS FILE's MATTER, in other files: Johnson/LPFK10R/Sits.lean: `k10_sits`
(the first four clauses of `K10Seated` and its sixth) and `seated_yes` (a yes of the seated block
is a yes of the frame's closing at the state's record, written back; no mark behind; the seat's
test holds); SitsAll.lean: `seated_unmarked` (no mark in front), `ixK10` and `k10_at_flat` (the
number in the flat list). WHAT THIS FILE ADDS, as far as one search of the library looked (it did
not open every file): that each yes of that block gives `K10Keeps`; at any address (the library's
two ask that the address is not of the kind K7).

  `seated_keeps`    a yes of `IM.seatedAs same (K9.closing Q).retype name a`, at any test, name
                    and address, gives `K10Keeps`
  `K10Seated`       what is said of a chain c, the public part Z and a link l: there are the link
                    Lk, K9's numbers p at l (`IM.k9At`), the closing's parameters Q (made of Z and
                    p by the lot's own
                    `k10Par`) and a block b; b is the middle closing block of Lk, and number
                    14 l + (9 at l = 24, else 7) + 5 of c's flat list; b is the seated term at the
                    driver's address `IM.cAt l (IM.subAt l) 1 .K10`; each yes of b's decision
                    gives `K10Keeps`
  `seated_at_scope`   `K10Seated` at every l < 25, under the three premises of `IM.close_of`: the
                    public files are in the goals' scope; they are read; the description's maker's
                    value is opened
  `seated_at_headK10`   the same under the library's one head (`P5J.AtMgA`,
                   Johnson/P5J/MgAtAll.lean)
    `number_is`       the number as it is written here is the library's `LPFK10.ixK10 l`
  `keeps_at_place`  under that head, BY PLACES: at a number k whose place in `P5J.At.ps` is of the
                    kind K10 the flat list holds a block at that place, and each yes of its
                    decision gives `K10Keeps`

Limits. AT `OnBytes.secondHashFunction` ALONE, IN SCOPE: so stand the library's laws on the NUMBER, which are
called here. That the block sits alone at its link the library has at every older hash and without
the premise on scope, under two others (the maker's value is opened; a link that the driver takes
for the head has kind 2) (`IM.close_alone`; `LPFK10.k10_sits_every`,
Johnson/LPFK10R/SitsEvery.lean): not spent here. No member. Whether the three premises hold
together is no theorem (Johnson/IMR/K6Seat.lean's head); that the head can be met, under four
premises: `P5J.head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean). In this folder
`seated_keeps` is called by SeatYes.lean, AtChain.lean and AtPair.lean; `seated_at_headK10` by
AtChain.lean and KeepsStep.lean; `keeps_at_place` by KeepsStep.lean; `number_is` by AtPair.lean
and KeepsStep.lean. AtChain.lean and AtPair.lean STAND OVER THIS FILE AND OVER OTHER AUTHORS'
FILES: a tree may hold this file without them: what this head says of them is then said of no file
of that tree. `K10Keeps` IS FOR THE MIDDLE ONE OF THE THREE CLOSING BLOCKS ALONE: the two others
are another kind's. It speaks of the decision. Of the step (`Block.step`), which strips the
rounds' sealed digest and hands the decision the columns' groups, nothing is said here. Nothing on
soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Keeps
import Johnson.IMR.CloseSeat
import Johnson.IMR.FirstSeats
import Johnson.IMR.FrameSeat
import Johnson.P5J.MgAtAll
import Johnson.P5J.K10Seat
import Johnson.LPFK10R.SitsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)

/-- **THE PAYER AT THE SEATED TERM.** -/
theorem seated_keeps {Q : Par} (same : S → S → Bool) (name : String) (a : Place) {t t' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs = .ok t') :
    K10Keeps t t' := by
  have key : ∀ u, (IM.marked (K9.closing (Cl := Unit) Q).retype name).decide t rs gs = .ok u →
      K10Keeps t u := fun u hu => by
    obtain ⟨h1, h2⟩ := ProofFile.Law.guardMark_yes.1
      (show (ProofFile.guardMark (K9.closing (Cl := Unit) Q).retype).decide t rs gs = _ from hu)
    exact ⟨closing_turns (Cl := Unit) (P := Q) h1, h2⟩
  unfold IM.seatedAs Block.guarded at h
  simp only at h
  split at h
  · exact key _ h
  · obtain ⟨u, hu, hv⟩ := ok_bind h
    unfold seatSame at hv
    split at hv
    · obtain rfl := Except.ok.inj hv
      exact key _ hu
    · cases hv

/-- **What is said of a chain, the public part and a link.** -/
def K10Seated (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (l : Nat) : Prop :=
  ∃ (Lk : Link S ProofFile.Cl) (p : K9.Where) (Q : Par) (b : Block S ProofFile.Cl),
    c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧
    ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
    c.blocksInOrder[14 * l + (if l = 24 then 9 else 7) + 5]? = some b ∧
    b = IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype b.name
      (IM.cAt l (IM.subAt l) 1 .K10) ∧
    ∀ t t' rs gs, b.decide t rs gs = .ok t' → K10Keeps t t'

/-- The number as it is written in `K10Seated` is the library's own name for it. -/
theorem number_is (l : Nat) : LPFK10.ixK10 l = 14 * l + (if l = 24 then 9 else 7) + 5 := by
  unfold LPFK10.ixK10
  rw [IM.hear_len_at]

/-- **At every link, in scope.** -/
theorem seated_at_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : Nat) (hl : l < 25) :
    K10Seated c Z l := by
  obtain ⟨Lk, p, Q, e1, hp, hQ, hall⟩ := IM.close_of hS hR O l hl
  obtain ⟨b, x, h1, h2, h3⟩ := hall 1 .K10 rfl
  obtain rfl : K9.closing (Cl := Unit) Q = x := Option.some.inj h2
  have hn := IM.close_numbers hS hR O hl e1 h1
  obtain ⟨_, _, _, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', _, _, _, _, e1', hlen, _⟩ := hfr l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  rw [hlen] at hn
  refine ⟨Lk', p, Q, b, e1, hp, hQ, h1, hn, h3, fun t t' rs gs hd => ?_⟩
  rw [show b = _ from h3] at hd
  exact seated_keeps _ _ _ hd

/-- **The same under the library's one head.** -/
theorem seated_at_headK10 {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    K10Seated cF Zp l := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact seated_at_scope h.scope h.reads O l hl

/-- **Under that head, by places.** -/
theorem keeps_at_place {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat) (p : Place)
    (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[k]? = some b ∧ b.place = p ∧
      ∀ t t' rs gs, b.decide t rs gs = .ok t' → K10Keeps t t' := by
  obtain ⟨b, Q, a, h1, h2, _, _, h5⟩ := P5J.k10_block_at h k p hp hK
  refine ⟨b, h1, h2, fun t t' rs gs hd => ?_⟩
  rw [show b = _ from h5] at hd
  exact seated_keeps _ _ _ hd

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.seated_keeps
#print axioms ProofFile.Honest.K10.YesFree.number_is
#print axioms ProofFile.Honest.K10.YesFree.seated_at_scope
#print axioms ProofFile.Honest.K10.YesFree.seated_at_headK10
#print axioms ProofFile.Honest.K10.YesFree.keeps_at_place
