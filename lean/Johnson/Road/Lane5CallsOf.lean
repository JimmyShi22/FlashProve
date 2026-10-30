-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5CallsOf.lean

The library's numbers of the main lookup argument of an attention segment (Inst.Model.AttSeg.Calls:
call c has 2^(a c) keys; a tree has 2^Dk; 2^sg tree numbers) FROM THE VERIFIER's OWN LOOKUP SHAPE,
and the three hypotheses on sizes under which the library's key forms are the extensions of the key
vectors (kfExt), as ONE public statement that a program can test.

Main definitions and theorems:
* "callsOf fs": a c := n of the lookup's call c; Dk := dT; sg := rK.
* "CallsFit S fs": the clauses of Calls.OK (callsOf fs) (dimOf S) at the shift of sclOf S; each of
  the five sizes of pieces is at most Dk; a 0 = a 1; the verifier's iota of each call is the
  library's e and at most rK; and the library's first tree of each call is the verifier's. Numbers
  alone: public; decidable.
* "callsFit_ok", "callsFit_deep", "callsFit_a01", "callsFit_first", "callsFit_iota": the parts, in
  the forms in which kfExt, its users and Lane5ZkZc.lean ask them.
The runs (#guard): at the two configurations of Lane5KvCfg.lean. There: a = 27, 27, 26, 25, Dk = 25,
sg = 4, first trees 0, 4, 8, 10 (the library's Calls.ref); and a = 20 four times, Dk = 20, sg = 2.
-/
import Johnson.Road.Lane5AttDef
import OnBytes.Model.Forest
import Inst.Model.Att.Points
import Johnson.Road.Lane5KvCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model Inst.Model.AttSeg
open OnBytes.Attention (Shape shapeHid)

/-- **The library's numbers of the lookup, from the verifier's lookup shape.** -/
def callsOf (fs : Model.Forest.Shape) : Calls :=
  ⟨fun c => ((fs.calls[c.val]?).map fun k => k.n).getD 0, fs.dT, fs.rK⟩

/-- **The numbers fit.** Public. -/
def CallsFit (S : Shape) (fs : Model.Forest.Shape) : Prop :=
  (∀ c, (dimOf S).used c ≤ 2 ^ (callsOf fs).a c) ∧ (∀ c, (callsOf fs).Dk ≤ (callsOf fs).a c) ∧
    (callsOf fs).NT ≤ 2 ^ (callsOf fs).sg ∧ (∀ c, (callsOf fs).trees c ∣ (callsOf fs).first c) ∧
    10 ≤ (callsOf fs).Dk ∧ ExpOK (S.cf.sh.getD 0 0) S.u0 ∧
    ((dimOf S).lM ≤ (callsOf fs).Dk ∧ (dimOf S).lD ≤ (callsOf fs).Dk ∧
      (dimOf S).lW ≤ (callsOf fs).Dk ∧ (dimOf S).lX ≤ (callsOf fs).Dk ∧
      (dimOf S).l4 ≤ (callsOf fs).Dk) ∧
    (callsOf fs).a 0 = (callsOf fs).a 1 ∧
    (∀ c : Fin 4, (callsOf fs).first c = fs.first.getD c.val 0) ∧
    ∀ c : Fin 4, fs.iota.getD c.val 0 = (callsOf fs).e c ∧ (callsOf fs).e c ≤ fs.rK

instance (S : Shape) (fs : Model.Forest.Shape) : Decidable (CallsFit S fs) := by
  unfold CallsFit
  infer_instance

variable {S : Shape} {fs : Model.Forest.Shape}

/-- The library's condition on the numbers. -/
theorem callsFit_ok (h : CallsFit S fs) : Calls.OK (scl := sclOf S) (callsOf fs) (dimOf S) :=
  @Calls.OK.mk (callsOf fs) (sclOf S) (dimOf S) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1

/-- A piece of every family fits into a tree. -/
theorem callsFit_deep (h : CallsFit S fs) : ∀ u : Fam, u.l (dimOf S) ≤ (callsOf fs).Dk := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.2.2.2.2.2.2.1
  intro u
  cases u
  exacts [h1, h2, h1, h2, h3, h4, h5]

/-- The first two calls have as many keys. -/
theorem callsFit_a01 (h : CallsFit S fs) : (callsOf fs).a 0 = (callsOf fs).a 1 :=
  h.2.2.2.2.2.2.2.1

/-- The library's first tree of a call is the verifier's. -/
theorem callsFit_first (h : CallsFit S fs) (c : Fin 4) :
    (callsOf fs).first c = fs.first.getD c.val 0 := h.2.2.2.2.2.2.2.2.1 c

/-- The verifier's number of bits of a call's trees is the library's, and is at most rK. -/
theorem callsFit_iota (h : CallsFit S fs) (c : Fin 4) :
    fs.iota.getD c.val 0 = (callsOf fs).e c ∧ (callsOf fs).e c ≤ fs.rK := h.2.2.2.2.2.2.2.2.2 c

/-! ## The runs -/

namespace CallsWit

open KvCfg

#guard ((shapeHid 28 cfFull).toOption.map fun x =>
  ((List.finRange 4).map (callsOf x.2).a, (callsOf x.2).Dk, (callsOf x.2).sg, x.2.first)) ==
  some ([27, 27, 26, 25], 25, 4, #[0, 4, 8, 10])
#guard ((shapeHid 28 cfFull).toOption.map fun x => decide (CallsFit x.1 x.2)) == some true
#guard ((shapeHid 24 cfSmall).toOption.map fun x => decide (CallsFit x.1 x.2)) == some true

end CallsWit

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.callsFit_ok
#print axioms OnBytes.Road.L5.callsFit_deep
#print axioms OnBytes.Road.L5.callsFit_a01
#print axioms OnBytes.Road.L5.callsFit_first
#print axioms OnBytes.Road.L5.callsFit_iota
