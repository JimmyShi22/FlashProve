-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K3Light.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): THE TEST WITH CODE
ON THE PUBLIC DATA (`readsXB`, K3RowXB.lean) ONCE MORE, IN A FILE WITH A LIGHT CONE: over
K3Written.lean alone: none of the lot's heavy closed facts lies beneath it. Definitions, and laws
without a kernel fact. Why. Whoever decides the test at a value by the kernel runs that fact often;
K3RowXB.lean's cone holds four heavy files that the test's own text does not need.
  `Light.viewOf`, `Light.viewW`, `Light.sameCall`, `Light.sameList`, `Light.sameView`,
    `Light.readsAt`, `Light.readsB`: the texts of K3Row.lean's and K3RowXB.lean's definitions of
    these short names, sign for sign. That they ARE these is proved in K3LightTie.lean.
  `Light.look_mk`, `tl_mk`, `laid_mk`, `key_mk`, `quiet_mk`, `readers_mk`: in front of the head's
    segment (i < 24, at profile 4 and twelve groups) the six readers have one value at two public
    data that share layers, G and A.
  `Light.readsAt_congr`: **so does the test at such a segment.**
  `Light.readsB_of_parts`: the whole test from its first 24 segments and the head's.
TWO NAMES FOR ONE TEXT, BY DESIGN: this file goes with whoever decides the test at a value;
K3RowXB.lean and K3LightTie.lean go with the join.
Limits. That the test says yes at any public data is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3.Light
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt isHead)
open VerifiableInference.Desc.First.Look (lookAt laidAt tlAt padKeyAt)
open Johnson.AtFull.ProofRows.K3 (strip)

/-- What a skeleton reads of a lookup's place. -/
def viewOf (strp : Bool) (x : First.Look.Place) :
    String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat :=
  (x.name, x.link, if strp then x.calls.map strip else x.calls, x.pub, x.lid, x.F.next, x.ns, x.lm)

/-- The written one. -/
def viewW (i : Nat) (d : Bool) : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat :=
  (nameW i d, i, callsW (sortOf i) d, pubW (sortOf i) d, 28, firstW (sortOf i) d, nsW (sortOf i),
    lmW (sortOf i) d)

/-- Two calls without a table are one. -/
def sameCall (a b : Call) : Bool :=
  a.name == b.name && a.n == b.n && a.iota == b.iota && a.k == b.k && a.kappa == b.kappa &&
    a.fn == b.fn && a.t0 == b.t0 && a.tau.isNone && b.tau.isNone && a.pub == b.pub &&
    a.heavy == b.heavy

def sameList : List Call → List Call → Bool
  | [], [] => true
  | a :: l, b :: m => sameCall a b && sameList l m
  | _, _ => false

/-- Two views are one. -/
def sameView (v w : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat) : Bool :=
  v.1 == w.1 && v.2.1 == w.2.1 && sameList v.2.2.1.toList w.2.2.1.toList && v.2.2.2 == w.2.2.2

/-- The test at one segment. -/
def readsAt (X : Verify.Public) (i : Nat) : Bool :=
  ((lookAt X i false).any fun x => sameView (viewOf true x) (viewW i false)) &&
    ((lookAt X i true).any fun x => sameView (viewOf false x) (viewW i true)) &&
    ([false, true].all fun d => laidAt X i d == some (pubW (sortOf i) d) &&
      padKeyAt X i d == some true && (quietAt X i d).isSome == quietW i d) &&
    ((K3Lot.readersAt X i).isSome == callerW i)

/-- The six hypotheses of `ReadsX` (K3RowXB.lean), as one test with code. -/
def readsB (X : Verify.Public) : Bool := (List.range 25).all (readsAt X)

section
variable {P P' : PolScan} {dg dg' : Verify.Digests} {L : Layer.Pub} {hS hS' : Head.Shape}
  {HLy HLy' : Head.HL} {G : Array Layer.HPlan2} {A : Array Attention.Plan}
  {H H' : Head.HPlanH2} {ow ow' : Head.Owner} {i : Nat}

theorem ne24 (hi : i < 24) : (i == 24) = false := beq_eq_false_iff_ne.2 (by omega)

theorem look_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) (d : Bool) :
    lookAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i d =
      lookAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i d := by
  simp only [lookAt, Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4, hN, ↓reduceIte,
    Nat.reduceMul, ne24 hi, Bool.false_eq_true]

theorem tl_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) :
    tlAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i = tlAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i := by
  simp only [tlAt, Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4, hN, ↓reduceIte,
    Nat.reduceMul, ne24 hi, Bool.false_eq_true]

theorem laid_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) (d : Bool) :
    laidAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i d =
      laidAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i d := by
  simp only [laidAt, tl_mk (P := P) (P' := P') (dg := dg) (dg' := dg') (hS := hS) (hS' := hS')
    (HLy := HLy) (HLy' := HLy') (G := G) (A := A) (H := H) (H' := H') (ow := ow) (ow' := ow') h4 hN
    hi,
    Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4, hN, ↓reduceIte, Nat.reduceMul,
    ne24 hi, Bool.false_eq_true]

/-- At an attention segment the test on the padding key reads row t0 of a call's table where the
call has one (`padKeyAtt`, Johnson/Desc/First/Look/Laid.lean): the call lies in A. -/
theorem key_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) (d : Bool) :
    padKeyAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i d =
      padKeyAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i d := by
  simp only [padKeyAt, tl_mk (P := P) (P' := P') (dg := dg) (dg' := dg') (hS := hS) (hS' := hS')
    (HLy := HLy) (HLy' := HLy') (G := G) (A := A) (H := H) (H' := H') (ow := ow) (ow' := ow') h4 hN
    hi,
    Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4, hN, ↓reduceIte, Nat.reduceMul,
    ne24 hi, Bool.false_eq_true]

theorem quiet_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) (d : Bool) :
    quietAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i d =
      quietAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i d := by
  simp only [quietAt, isHead, Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4, hN,
    ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true]

theorem readers_mk (h4 : L.y.h.p4 = true) (hN : L.y.NGr = 12) (hi : i < 24) :
    K3Lot.readersAt ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ i =
      K3Lot.readersAt ⟨P', dg', L, hS', HLy', G, A, H', ow'⟩ i := by
  simp only [K3Lot.readersAt, isHead, Verify.Public.p4, Verify.Public.NGr, Verify.Public.y, h4,
    hN, ↓reduceIte, Nat.reduceMul, ne24 hi, Bool.false_eq_true]

end

/-- **IN FRONT OF THE HEAD's SEGMENT THE TEST READS OF X ITS layers, G AND A ALONE.** h4 and hN
stand on X alone: X' has them through hL: p4 and NGr are read off layers. -/
theorem readsAt_congr {X X' : Verify.Public} (hL : X.layers = X'.layers) (hG : X.G = X'.G)
    (hA : X.A = X'.A) (h4 : X.p4 = true) (hN : X.NGr = 12) {i : Nat} (hi : i < 24) :
    readsAt X i = readsAt X' i := by
  obtain ⟨P, dg, L, hS, HLy, G, A, H, ow⟩ := X
  obtain ⟨P', dg', L', hS', HLy', G', A', H', ow'⟩ := X'
  obtain rfl : L = L' := hL
  obtain rfl : G = G' := hG
  obtain rfl : A = A' := hA
  have h4' : L.y.h.p4 = true := h4
  have hN' : L.y.NGr = 12 := hN
  unfold readsAt
  rw [look_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN' hi
      false,
    look_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN' hi
      true,
    readers_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN'
      hi]
  congr 2
  congr 1
  funext d
  rw [laid_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN' hi
      d,
    key_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN' hi d,
    quiet_mk (P' := P') (dg' := dg') (hS' := hS') (HLy' := HLy') (H' := H') (ow' := ow') h4' hN' hi
      d]

/-- The whole test from its first 24 segments and the head's. -/
theorem readsB_of_parts {X : Verify.Public} (h : (List.range 24).all (readsAt X) = true)
    (h24 : readsAt X 24 = true) : readsB X = true := by
  unfold readsB
  rw [show (25 : Nat) = 24 + 1 from rfl, List.range_succ, List.all_append, h]
  simp [h24]

end Johnson.AtFull.Lots.K3.Light

#print axioms Johnson.AtFull.Lots.K3.Light.ne24
#print axioms Johnson.AtFull.Lots.K3.Light.look_mk
#print axioms Johnson.AtFull.Lots.K3.Light.tl_mk
#print axioms Johnson.AtFull.Lots.K3.Light.laid_mk
#print axioms Johnson.AtFull.Lots.K3.Light.key_mk
#print axioms Johnson.AtFull.Lots.K3.Light.quiet_mk
#print axioms Johnson.AtFull.Lots.K3.Light.readers_mk
#print axioms Johnson.AtFull.Lots.K3.Light.readsAt_congr
#print axioms Johnson.AtFull.Lots.K3.Light.readsB_of_parts
