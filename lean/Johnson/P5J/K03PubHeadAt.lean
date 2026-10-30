-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03PubHeadAt.lean: THE KIND "LOOKUP" (K3): pubFree AT ALL 25 SEGMENTS, AT EITHER LOOKUP's PLACE, AND AT THE OUTPUT HEAD's OWN PLACE. Five theorems. By calls alone: pubFree_mgAllAt (Johnson/P5J/K03PubAt.lean) at "the built segment's number of slots is the place's" (Johnson/P5J/K03SlotsHeadAt.lean: k03_slots_look_any · k03_slots_head_look · k03_slots_head).
  k03_pubFree_look  l < 25, d : Bool, lookAt X l d = some y: an accept of the composed meaning's public test at freeAbove l gives the door's freeAboveB y.ns.
  k03_pubFree_head  the same at segment 24 and headAt's place x (the ledger's own).
  k03_arrays_ns | k03_hnS  x.arrays.ns = x.ns (rfl): DigShortR's hnS at n := x.ns.
  k03_ns_one        the calls' and the digits' places of one segment have one number of slots (both are the built segment's): so "n := the calls' place's" (k03_pubFree_digits, Johnson/P5J/K03PubAt.lean) and "n := the digits' own" are one number.
  So the field pubFree of ObjShortR (Johnson/P5J/K03ObjAt.lean) is paid at all 25 lookups on the calls, and DigShortR's (Johnson/P5J/K03DigAt.lean) at all 25 on the digits AT n := the digits' own place's number of slots.
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03PubAt
import Johnson.P5J.K03SlotsHeadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **pubFree at every segment, at either lookup's place.** -/
theorem k03_pubFree_look (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {d : Bool} {y : Place} (hy : lookAt (At.X Zp) l d = some y) :
    ∀ (z : ProofFile.InstPub) s, (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB y.ns s = true := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · exact pubFree_mgAllAt (h.toAtMg.𝔇 h.𝔇) mgBase l y.ns (k03_slots_look_any h h24 hy)
  · obtain rfl : l = 24 := by omega
    exact pubFree_mgAllAt (h.toAtMg.𝔇 h.𝔇) mgBase 24 y.ns (k03_slots_head_look h hy)

/-- **pubFree at the output head's own place.** -/
theorem k03_pubFree_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {x : Place}
    (hx : VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some x) :
    ∀ (z : ProofFile.InstPub) s, (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.freeAbove 24) (z, s) = true →
      H2K5.Door.freeAboveB x.ns s = true := by
  obtain rfl : x₀ = x := Option.some.inj (h.headAt.symm.trans hx)
  exact pubFree_mgAllAt (h.toAtMg.𝔇 h.𝔇) mgBase 24 x₀.ns (k03_slots_head h)

/-- A place's ledger's shape has the place's number of slots: so DigShortR's hnS at n := x.ns is ≤ by
equality. -/
theorem k03_arrays_ns (x : Place) : x.arrays.ns = x.ns := rfl

theorem k03_hnS (x : Place) : x.ns ≤ x.arrays.ns := Nat.le_of_eq (k03_arrays_ns x).symm

/-- **One ledger a segment**: the two lookups' places of a segment have one number of slots. -/
theorem k03_ns_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {y x : Place} (hy : lookAt (At.X Zp) l false = some y) (hx : lookAt (At.X Zp) l true = some x) :
    y.ns = x.ns := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · exact Option.some.inj ((k03_slots_look_any h h24 hy).symm.trans (k03_slots_look_any h h24 hx))
  · obtain rfl : l = 24 := by omega
    exact Option.some.inj ((k03_slots_head_look h hy).symm.trans (k03_slots_head_look h hx))

end P5J

#print axioms P5J.k03_arrays_ns
#print axioms P5J.k03_hnS
#print axioms P5J.k03_ns_one
#print axioms P5J.k03_pubFree_look
#print axioms P5J.k03_pubFree_head
