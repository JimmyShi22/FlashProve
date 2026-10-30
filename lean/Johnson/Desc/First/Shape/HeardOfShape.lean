-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeardOfShape.lean: FROM THE SHAPE OF ALL THAT THE OUTPUT HEAD's OWN ROUNDS
LEAVE (HeardAllSh, HearHead.lean) TO THE SHAPE OF THE PROGRAM's RECORD OF IT (HeadHeardSh,
HeadHeard.lean): Kinds.Head.heardOf and pscOf (Johnson/Stored/HeadSeat.lean) through the shapes.
General laws; nothing is evaluated.
  1 `slotOfSh`, `slotOf_sh`: a hidden scalar's number, off its form's shape. `weightOf_d`.
    `pscOfSh`, **`pscOf_sh`**: the program's record of a sumcheck. `zip_degrees_take`. `leftSh`,
    `left_sh`: the one form that a sumcheck leaves. `hidSh_getD`, `end_sh`. `tscOfSh`, `tscOf_sh`: a
    token sumcheck as the program keeps it.
  2 `headHeardOfSh zx A`, **`heardOf_sh`**: headHeardSh (heardOf g1 H) = headHeardOfSh g1.zx.size
    (heardAllSh H): every length, every slot's number, every PscSh and AffSh of the program's record
    is a function of the shape of what was heard, the sizes and the number of coordinates of the
    lookup's point. One equation; no premise.
By HearSum.lean's affSh_msRow and HearHead.lean's getD_hidSh.
Limits. g1 is not in HeadHeardSh; of win the size alone (HeadHeard.lean). TWO SILENT DEFAULTS STAND
ONE BEHIND THE OTHER: a list that is too short gives the empty form (getD … (AffSh.mk [] [])), and
the empty form gives the slot number 0 (slotOfSh), which is a true slot's number: whoever feeds
headHeardOfSh a HeardAllSh that no hearing left gets numbers without a warning. Nothing on what any
field is worth. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HearHead
import Johnson.Desc.First.Shape.HeadHeard
import Johnson.Stored.HeadSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Kinds (Hear Hid Sum Point)
open VerifiableInference.Desc.Part.MaskedSum (Var)

/-! ## 1 A slot's number; the program's record of a sumcheck; the form that is left -/

/-- A hidden scalar's number, off its form's shape; 0 where the form names no slot, as the library's
slotOf (slotOf_sh). -/
def slotOfSh (a : AffSh) : Nat := a.slots.getD 0 0

theorem slotOf_sh (h : Hid) : Kinds.Head.slotOf h = slotOfSh (hidSh h) := by
  unfold Kinds.Head.slotOf slotOfSh hidSh
  show _ = (h.var.slots.toList.map (·.1)).getD 0 0
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases h.var.slots[0]? <;> rfl

theorem weightOf_d (v : Var) : (Kinds.Head.weightOf v).d = v.d := by
  cases v <;> rfl

/-- The program's record of a sumcheck, on shapes. -/
def pscOfSh (k : Option SumSh) (rowMade : Bool) : PscSh :=
  match k with
  | none => pscSh {}
  | some h => PscSh.mk rowMade true h.degrees h.r h.first h.start true

theorem pscOf_sh (k : Option Part.MaskedSum.Heard) (rowMade : Bool) :
    pscSh (Kinds.Head.pscOf k rowMade) = pscOfSh (k.map sumSh) rowMade := by
  cases k with
  | none => rfl
  | some h =>
    show PscSh.mk rowMade true (((h.vars.map Kinds.Head.weightOf).toArray).toList.map (·.d))
      h.r.toArray.size h.first (affSh h.start) true = PscSh.mk rowMade true (h.vars.map (·.d))
      h.r.length h.first (affSh h.start) true
    rw [List.toList_toArray, List.map_map, List.size_toArray]
    congr 2
    exact funext fun v => weightOf_d v

theorem zip_degrees_take : ∀ (vs : List Var) (r : List E),
    (vs.zip r).map (·.1.d) = (vs.map (·.d)).take r.length
  | [], _ => by simp
  | _ :: _, [] => rfl
  | v :: vs, x :: r => by
    show v.d :: ((vs.zip r).map (·.1.d)) = v.d :: ((vs.map (·.d)).take r.length)
    rw [zip_degrees_take vs r]

/-- The one form that a sumcheck leaves, on shapes. -/
def leftSh (s : KSumSh) : AffSh :=
  match s.psc with
  | some h => msRowSh h (hidingLen (h.degrees.take h.r)) (AffSh.mk [] [])
  | none => AffSh.mk [] []

theorem left_sh (s : Sum) (S0 : E) : affSh (s.left S0) = leftSh (kSumSh s) := by
  unfold Kinds.Sum.left leftSh
  cases hp : s.psc with
  | none =>
    show affSh (Aff.ofConst oneE) = (match (kSumSh s).psc with
      | some h => _
      | none => AffSh.mk [] [])
    have e : (kSumSh s).psc = none := by
      show s.psc.map sumSh = none
      rw [hp]
      rfl
    rw [e]
    rfl
  | some h =>
    have e : (kSumSh s).psc = some (sumSh h) := by
      show s.psc.map sumSh = _
      rw [hp]
      rfl
    rw [e]
    show affSh (Part.MaskedSum.rowForm h S0 {}) = _
    rw [affSh_msRow, zip_degrees_take]
    rfl

theorem hidSh_getD (W : Array Hid) (j : Nat) :
    hidSh (W.getD j {}) = (W.toList.map hidSh).getD j (AffSh.mk [] []) := getD_hidSh W j

theorem end_sh (s : Sum) (j : Nat) :
    hidSh (s.end_ j) = (kSumSh s).ends.getD j (AffSh.mk [] []) := getD_hidSh s.ends j

/-- A token sumcheck as the program keeps it, on shapes. r: the number of its challenges on the
positions. -/
def tscOfSh (s : KSumSh) (r : Nat) : TscSh :=
  { sCl := slotOfSh s.claimed, sEnd := slotOfSh (s.ends.getD 0 (AffSh.mk [] [])), r := r
    p := pscOfSh s.psc true, rowU := leftSh s }

theorem tscOf_sh (s : Sum) (r : Point) (S0 : E) :
    tscSh (Kinds.Head.tscOf s r S0) = tscOfSh (kSumSh s) r.size := by
  show TscSh.mk (Kinds.Head.slotOf s.claimed) (Kinds.Head.slotOf (s.end_ 0)) r.size
    (pscSh (Kinds.Head.pscOf s.psc true)) (affSh (s.left S0)) = _
  rw [slotOf_sh, slotOf_sh, end_sh, pscOf_sh, left_sh]
  rfl

/-! ## 2 The program's record of what was heard -/

section
variable [Kinds.Head.Sizes] [Kinds.Head.Request] [Kinds.Head.Token]

/-- **The shape of the program's record, of the shape of all that was heard.** zx: the number of
coordinates of the lookup's point. -/
def headHeardOfSh (zx : Nat) (A : HeardAllSh) : HeadHeardSh :=
  { win := Kinds.Norm.T
    Zl := min zx zx - (zx - (Kinds.Norm.ls + Kinds.Norm.lt))
    PV := A.norm.pV
    sW := slotOfSh (A.norm.W.getD 0 (AffSh.mk [] []))
    gp := 9
    wpl := { r := A.norm.squares.r, sL := slotOfSh (A.norm.squares.ends.getD 0 (AffSh.mk [] []))
             sR := slotOfSh (A.norm.squares.ends.getD 1 (AffSh.mk [] []))
             row := leftSh A.norm.squares }
    sPv := slotOfSh (A.norm.P.getD 0 (AffSh.mk [] []))
    omV := 7
    tV := tscOfSh A.norm.products A.norm.products.r
    tN := tscOfSh A.normed A.normed.r
    tH := tscOfSh A.logits (min Kinds.Norm.lt A.logits.r - 0)
    rs := min (Kinds.Norm.lt + Kinds.Norm.lPd) A.logits.r - Kinds.Norm.lt
    qN := 0
    qH := 0 }

theorem heardOf_sh (g1 : Forest.Heard) (H : Kinds.Head.HeardAll) :
    headHeardSh (Kinds.Head.heardOf g1 H) = headHeardOfSh g1.zx.size (heardAllSh H) := by
  obtain ⟨n, f, h⟩ := H
  unfold Kinds.Head.heardOf headHeardSh headHeardOfSh
  dsimp only
  simp only [tscOf_sh, slotOf_sh, end_sh, left_sh, hidSh_getD, levelSh, Array.size_map,
    Array.size_range, Array.size_extract, Array.size_reverse, Kinds.Head.powersOf]
  rfl

end

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.slotOf_sh
#print axioms VerifiableInference.Desc.First.Shape.weightOf_d
#print axioms VerifiableInference.Desc.First.Shape.pscOf_sh
#print axioms VerifiableInference.Desc.First.Shape.zip_degrees_take
#print axioms VerifiableInference.Desc.First.Shape.left_sh
#print axioms VerifiableInference.Desc.First.Shape.hidSh_getD
#print axioms VerifiableInference.Desc.First.Shape.end_sh
#print axioms VerifiableInference.Desc.First.Shape.tscOf_sh
#print axioms VerifiableInference.Desc.First.Shape.heardOf_sh
#print axioms VerifiableInference.Desc.First.Shape.slotOfSh
#print axioms VerifiableInference.Desc.First.Shape.pscOfSh
#print axioms VerifiableInference.Desc.First.Shape.leftSh
#print axioms VerifiableInference.Desc.First.Shape.tscOfSh
#print axioms VerifiableInference.Desc.First.Shape.headHeardOfSh
