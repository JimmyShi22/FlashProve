-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PublicMoreAtHead.lean: the kind "the code switch" (K2): SIX
PUBLIC PREMISES OF THE RECORD `K2SeatedL` AT THE HEAD's LETTERS (Honest/K2/Law/RecordAtHead.lean),
UNDER THE LIBRARY's HEAD AND THE OPENING, AT EACH SWITCH OF THE PLAN: hcodes · trees · answersNo ·
seedsNo · nonZeroNo, at the place's numbers q := `IM.k2P` Zp a nm st n, n: the plan's own numbers at
the place's link, whatever a, nm and st are · port, at the written record's radii. Two definitions,
public tests; three closed facts by evaluation in Lean's kernel, one with two controls; lemmas.

  `codesW`, `codes_switch`   BY LEAN's KERNEL: each written place's codes are the written codes;
                    so, under the head, hcodes: the sending's codes are the real table's
  `seedsStated`, `seedsStatedW`   A PUBLIC TEST: the plan's numbers state the sending's seeds, each
                    with its coordinates and one factor, and as many non-zero draws as seeds; BY
                    LEAN's KERNEL at the written places; TWO CONTROLS: with one non-zero draw more
                    stated, and with one drawn element more, it says no at each place
  `nums_there`      under the head the plan has numbers at each switch's link
  `four_public_at_head`   THE FOUR FIELDS trees · answersNo · seedsNo · nonZeroNo, in the record's
                    own text
  `portAt`, `portW`, `port_switch`   the library's condition on the sending at the radii of entry
                    3 l of the written record, l: the place's link; BY LEAN's KERNEL (no control);
                    then under the head

By: `place_shapes` (Honest/K2/Law/PlaysAtPlan.lean) · `answers_at_head`, `numsW_at_head`
(Honest/K2/Law/PublicAtHead.lean) · `prep_at_head`, `places_at_head`
(Honest/K2/Law/PlacesWritten.lean) · of other authors, sealed: `codes_at_head`
(Honest/K1/Law/RecordAtHead.lean) · `hc_atAll`, `pin1_atAll` (Johnson/Desc/K1/Law/).

Limits. PUBLIC NUMBERS ALONE: no coin, input or run occurs. rad IS TIED TO NOTHING BY THE RECORD:
here it is the written record's. THAT ENTRY 3 l OF THE WRITTEN RECORD IS THE SWITCH's SENDING is not
said: the test would say no at radii that do not meet the condition, no more. The full size and the
format's second hash function alone. The head and the opening are premises; that they can be met is not
said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.G (codesFull2)

/-! ## 1 At the written constants -/

set_option maxRecDepth 1000000 in
/-- Each written place's codes are the written codes. -/
theorem codesW : (placesW.all fun p => decide (p.sizes.codes = codesFull2)) = true := by
  decide +kernel

/-- **A PUBLIC TEST**: the plan's numbers state the sending's seeds, each with its coordinates and
one factor, and as many non-zero draws as seeds. -/
def seedsStated (p : SwitchPlace) (n : P1K2.Nums) : Bool :=
  n.seeds == (switchPar p).seeds * ((switchPar p).coordinates + 1) &&
    n.nonZero == (switchPar p).seeds

set_option maxRecDepth 1000000 in
/-- **At the written places, at the written plan's numbers**; two controls: with one non-zero draw
more stated, and with one drawn element more stated, the test says no at each place. -/
theorem seedsStatedW :
    (placesW.all fun p => (numsW p.place.link).any (seedsStated p)) = true ∧
      (placesW.any fun p => (numsW p.place.link).any fun n =>
        seedsStated p { n with nonZero := n.nonZero + 1 }) = false ∧
      (placesW.any fun p => (numsW p.place.link).any fun n =>
        seedsStated p { n with seeds := n.seeds + 1 }) = false := by
  decide +kernel

/-- The library's condition on the sending, at the radii of entry 3 l of the written record. -/
def portAt (p : SwitchPlace) : Bool :=
  K1.condPort (switchPar p) (K1.radRec (3 * p.link) (switchPar p))

set_option maxRecDepth 1000000 in
/-- **At the written places.** -/
theorem portW : placesW.all portAt = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)} {p : SwitchPlace}

/-- **hcodes**: the sending's codes are the real table's. -/
theorem codes_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    (switchPar p).codes = P5J.At.cs Zp := by
  rw [places_at_head h.toAtMg O] at hp
  have e : p.sizes.codes = codesFull2 := of_decide_eq_true (List.all_eq_true.1 codesW p hp)
  show p.sizes.codes = P5J.At.cs Zp
  rw [e, ← K1.codes_at_head O, K1.hc_atAll h O (K1.pin1_atAll h)]

/-- Under the head the plan has numbers at each switch's link. -/
theorem nums_there (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∃ Pp n, P1K2.prepOf Zp Bs.G₀ = some Pp ∧ P1K2.numsAt Pp p.place.link = some n := by
  rw [places_at_head h.toAtMg O] at hp
  have t := List.all_eq_true.1 seedsStatedW.1 p hp
  cases hN : numsW p.place.link with
  | none =>
    rw [hN] at t
    cases t
  | some n =>
    unfold numsW at hN
    cases hP : IM.prepW with
    | none =>
      rw [hP] at hN
      cases hN
    | some Pp =>
      rw [hP] at hN
      exact ⟨Pp, n, (prep_at_head h.toAtMg O).trans hP, hN⟩

/-- **trees · answersNo · seedsNo · nonZeroNo**, in the record's own text, at q := `IM.k2P` Zp a nm
st n, n: the plan's numbers at the place's link; a, nm, st: any. -/
theorem four_public_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) (a : Place) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At) :
    (IM.k2P Zp a nm st n).sent.map (fun o => (o.logLength, o.words)) =
        treeShapes p.sizes.codes (switchSent p.sizes p.others) ∧
      (switchPar p).answers = (IM.k2P Zp a nm st n).answers ∧
      (IM.k2P Zp a nm st n).seeds = (switchPar p).seeds * ((switchPar p).coordinates + 1) ∧
      (IM.k2P Zp a nm st n).nonZero = (switchPar p).seeds := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t : (numsW p.place.link).any (seedsStated p) = true :=
    List.all_eq_true.1 seedsStatedW.1 p hpW
  rw [numsW_at_head h.toAtMg O hP, hn] at t
  have t' : seedsStated p n = true := t
  unfold seedsStated at t'
  rw [Bool.and_eq_true] at t'
  exact ⟨place_shapes hP hp hn, answers_at_head h.toAtMg O hP p hp n hn, beq_iff_eq.1 t'.1,
    beq_iff_eq.1 t'.2⟩

/-- **port**, at the written record's radii. -/
theorem port_switch (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀) :
    K1.condPort (switchPar p) (K1.radRec (3 * p.link) (switchPar p)) = true := by
  rw [places_at_head h.toAtMg O] at hp
  exact List.all_eq_true.1 portW p hp

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.codesW
#print axioms ProofFile.Honest.K2.Law.seedsStated
#print axioms ProofFile.Honest.K2.Law.seedsStatedW
#print axioms ProofFile.Honest.K2.Law.portAt
#print axioms ProofFile.Honest.K2.Law.portW
#print axioms ProofFile.Honest.K2.Law.codes_switch
#print axioms ProofFile.Honest.K2.Law.nums_there
#print axioms ProofFile.Honest.K2.Law.four_public_at_head
#print axioms ProofFile.Honest.K2.Law.port_switch
