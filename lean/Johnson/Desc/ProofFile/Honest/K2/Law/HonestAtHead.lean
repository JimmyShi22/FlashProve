-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HonestAtHead.lean: the kind "the code switch" (K2): UNDER THE
LIBRARY's HEAD AND THE OPENING, AT EVERY SWITCH OF THE PLAN: THE PUBLIC PREMISES OF
`honestMain_at_closing` (HonestAtClosing.lean of this folder) ARE PAID: so, where the part's laying
returns V and the lot's closing at the plan's own segments returns W, `HonestMain` holds at the
place's own sizes. One definition with code: a public test; two closed facts by Lean's kernel, one
of them a control; statements with their proofs.

  `honestPublicB`   THE PUBLIC TEST, into Bool: the fields of `HonestPublic`, one by one
  `honestPublic_of_test`   its yes gives the record
  `honestPublicW`   BY LEAN's KERNEL: at each of the 25 written places a segment stands in front,
                    and the test says yes at the last of these
  `honestPublicW_can_fail`   a control: with one empty shape more among the kept members' shapes the
                    test says no at every written place
  `honestPublic_at_head`   under the head and the opening, at a switch of the plan: the segments in
                    front are some A and then Sg, and the record holds at Sg
  `honestMain_at_head`   THE END

By: `places_at_head`, `segments_at_head` (PlacesWritten.lean of this folder) · `noWord_yes`
(Counts.lean of this folder).

Limits. AT THE PLACE's SIZES p.sizes: THE FIELD honest OF `MadeAsks` ASKS IT AT `sizesAt` OF THE
STATEMENT AT A YES: that these are one is not said here. Both returns are premises: whether the
laying or the closing returns is not said. The head and the opening are premises. WHAT IS WRITTEN
WHERE: an equation at each run's coins between two texts' values. The full size; the format's
second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.HonestAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left HonestMain)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **THE PUBLIC TEST.** -/
def honestPublicB (p : SwitchPlace) (Sg : SegmentPub) : Bool :=
  noWord (switchSent p.sizes p.others) &&
  decide (1 + p.sizes.kept.length ≤ (switchSent p.sizes p.others).size) &&
  decide (((switchSent p.sizes p.others).getD 0 default).shape = p.sizes.target.shape) &&
  (p.sizes.target.shape.mainDeg == 3) &&
  decide (p.sizes.target.shape.answers ≠ 0) &&
  (OnBytes.Send.pad p.sizes.codes p.sizes.target.shape).isSome &&
  (List.range p.sizes.kept.length).all fun a =>
    decide (((switchSent p.sizes p.others).getD (1 + a) default).shape = p.sizes.kept.getD a {}) &&
    decide ((p.sizes.kept.getD a {}).answers ≠ 0) &&
    (OnBytes.Send.pad p.sizes.codes (p.sizes.kept.getD a {})).isSome &&
    decide ((p.sizes.codes.base.getD (p.sizes.kept.getD a {}).code default).ell ≤
      (Sg.sizes.codes.base.getD Sg.sizes.code default).ell)

/-- The test's yes gives the record. -/
theorem honestPublic_of_test {p : SwitchPlace} {Sg : SegmentPub}
    (h : honestPublicB p Sg = true) : HonestPublic p Sg := by
  unfold honestPublicB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact
    { noWord := noWord_yes h1
      size := h2
      first := h3
      copies := fun a ha => (h7 a ha).1.1.1
      overE := h4
      firstAns := h5
      firstPad := h6
      copyAns := fun a ha => (h7 a ha).1.1.2
      copyPad := fun a ha => (h7 a ha).1.2
      room := fun a ha => (h7 a ha).2 }

set_option maxRecDepth 1000000 in
/-- At each written place a segment stands in front, and the test says yes at the last. -/
theorem honestPublicW : (placesW.all fun p =>
    ((segsW.take p.link).getLast?).any (honestPublicB p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with one empty shape more among the kept shapes the test says no everywhere. -/
theorem honestPublicW_can_fail : (placesW.any fun p =>
    ((segsW.take p.link).getLast?).any
      (honestPublicB { p with sizes := { p.sizes with kept := p.sizes.kept ++ [{}] } })) =
    false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening, at a switch of the plan: the record.** -/
theorem honestPublic_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∃ A Sg, (segmentsOf Zp Bs.G₀).take p.link = A ++ [Sg] ∧ HonestPublic p Sg := by
  rw [places_at_head h O] at hp
  rw [segments_at_head h O]
  have t := List.all_eq_true.1 honestPublicW p hp
  cases hS : (segsW.take p.link).getLast? with
  | none =>
    rw [hS] at t
    cases t
  | some Sg =>
    rw [hS] at t
    exact ⟨(segsW.take p.link).dropLast, Sg,
      (List.dropLast_append_getLast? Sg (Option.mem_def.2 hS)).symm, honestPublic_of_test t⟩

/-- hV AND hW ARE PREMISES. **THE FIELD honest, AT THE PLACE's OWN SIZES, UNDER THE HEAD AND THE
OPENING.** An equation at each run's coins: what is written where. -/
theorem honestMain_at_head {W₀ Rc Xi Tr : Type} (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {V : Nat → Johnson.Prover.Send.Rows} {Wl : Left}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p c w hd = .ok V)
    (hW : lotClosingAt lay (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) (hd.take (hd.length - 0))
      (Stretch.carried p.carries c.2.2) = .ok Wl) : HonestMain p.sizes Wl V := by
  obtain ⟨A, Sg, hA, hP⟩ := honestPublic_at_head h O hp
  exact honestMain_at_closing hV hW hA hP

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.honestPublicB
#print axioms ProofFile.Honest.K2.Law.honestPublic_of_test
#print axioms ProofFile.Honest.K2.Law.honestPublicW
#print axioms ProofFile.Honest.K2.Law.honestPublicW_can_fail
#print axioms ProofFile.Honest.K2.Law.honestPublic_at_head
#print axioms ProofFile.Honest.K2.Law.honestMain_at_head
