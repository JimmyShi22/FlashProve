-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerMeans.lean: FOUR CLAUSES OF THE MEANING's ROW, IN THAT ROW's OWN
WORDS, FROM THE JOINTS IN FRONT OF THE LOOKUPS ON THE CALLS AT THE CLOSED CALLERS. Four definitions,
each the type of a field of the structure Means, and four theorems. NO SOUNDNESS OF ANY TEXT THAT
RUNS IS CLAIMED.

Why. The integer model's row on the meaning of a proof file (Johnson/Goal/Meaning/Row.lean)
rests on a structure Means X pp i x w of named clauses. That file is
not imported here. In its place the four clauses that
name the lookup are typed here AS THAT FILE TYPES THEM, under that file's own «open» lines: the body
of each definition below, from behind «:=» on, is the text of the field behind «∀ g < 12,»,
CHARACTER FOR CHARACTER: held by a program against that file, not by Lean.
  AttKeyAt X w g · AttRiddenAt X w g · LayKeyAt X i w g · LayHotAt X i x w g.
w: of the row's record Hid the two fields that these clauses read (Hid2). i: of the index its matrix
(Idx2.mat). The letters have the row's names, so that the text is the same.

The theorems: attKey_at, attRidden_at (from K3CallerAttMeans.lean), layKey_at, layHot_at (from
K3CallerLay.lean): the closed caller's joint in front, with the named readings at the row's own
hidden matrices, gives the clause at the group g.

Limits. Those of the three files named. A clause is had at one group g, at a place x whose
sub-proof's shape is the public record's at g. The readings are premises; CellsAre and MatsAre are
paid from the smallness test's clause at the integers behind the symbols (attCells_cast,
lay_mats_cast): so the row's hidden matrices have to BE these. WeightsAre is the pin's.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Road.HeadL5Grp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look.Clauses

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.AttSeg (Raw Idn idnVal keyVec lut lutSet castT)

/-- Of the row's record of hidden values: the lists of integer matrices of the groups of layers and
of the attention sub-proofs. -/
structure Hid2 where
  MG : ℕ → Mats ℤ
  MA : ℕ → Zs

/-- Of the index: its matrix. -/
structure Idx2 where
  mat : Mat

def AttKeyAt (X : Model.Verify.Public) (w : Hid2) (g : ℕ) : Prop :=
  ∀ (c : Fin 4) (n : ℕ), n < (dimOf (Hd.shapeA X g)).used c →
    keyVec (scl := sclOf (Hd.shapeA X g)) (dimOf (Hd.shapeA X g)) (tbOf (Hd.shapeA X g))
        (castT (cellsA (Hd.shapeA X g) (w.MA g)) : Raw → Cb.Gl.F) c n ∈
      lutSet (lut (scl := sclOf (Hd.shapeA X g)) (dimOf (Hd.shapeA X g)) (tbOf (Hd.shapeA X g)) c)

def AttRiddenAt (X : Model.Verify.Public) (w : Hid2) (g : ℕ) : Prop :=
  ∀ b g' n, (Idn.at3 b g' n).Valid (dimOf (Hd.shapeA X g)) →
    idnVal (dimOf (Hd.shapeA X g))
      (castT (cellsA (Hd.shapeA X g) (w.MA g)) : Raw → Cb.Gl.F) (.at3 b g' n) = 0

def LayKeyAt (X : Model.Verify.Public) (i : Idx2) (w : Hid2) (g : ℕ) : Prop :=
  KeyField (layerShape X.P) X.layers.sc X.y g (w.MG g) i.mat

def LayHotAt (X : Model.Verify.Public) (i : Idx2) (x : Cm.Seg.XI) (w : Hid2) (g : ℕ) : Prop :=
  HotField (layerShape X.P) X.layers.sc X.y g (w.MG g) i.mat x

end VerifiableInference.Desc.First.Look.Clauses

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model VerifiableInference.OnPublicFiles
open Clauses (Hid2 Idx2 AttKeyAt AttRiddenAt LayKeyAt LayHotAt)

section
variable {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat}
  (Ex : Iop.ExtSpec) (Wp : Type) (X : Verify.Public) (w : Hid2) (g : ℕ)

/-- **attRidden at the group g.** -/
theorem attRidden_at (H : AttOK set x (Road.Hd.shapeA X g) tl D rad) (a : Unit × Ex.Str)
    (v : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x (Road.Hd.shapeA X g) tl D rad Ex Wp]).A
      (attRider x (Road.Hd.shapeA X g) tl D rad Ex Wp)).relR a v)
    (hZ : CellsAre x (Road.Hd.shapeA X g) tl D rad v.1 (w.MA g)) : AttRiddenAt X w g :=
  att_attRidden Ex Wp H a v h (w.MA g) hZ

/-- **attKey at the group g.** -/
theorem attKey_at (H : AttOK set x (Road.Hd.shapeA X g) tl D rad) (a : Unit × Ex.Str)
    (v : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x (Road.Hd.shapeA X g) tl D rad Ex Wp]).A
      (attRider x (Road.Hd.shapeA X g) tl D rad Ex Wp)).relR a v)
    (hZ : CellsAre x (Road.Hd.shapeA X g) tl D rad v.1 (w.MA g))
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) : AttKeyAt X w g :=
  att_attKey Ex Wp H a v h (w.MA g) hZ hT hU

variable {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : Nat} (i : Idx2)

/-- The public letters of the layers' link of group g. -/
def pubAt (X : Verify.Public) (g : ℕ) : LayPub := ⟨Verify.layerShape X.P, X.layers.sc, X.y, g⟩

/-- **layKey at the group g.** -/
theorem layKey_at (H : LayOK set x) (a : Unit × Ex.Str) (v : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x (pubAt X g) tl D rad oW wOf nr nc Ex Wp]).A
      (layRider x (pubAt X g) tl D rad oW wOf nr nc Ex Wp)).relR a v)
    (hM : MatsAre x tl D rad oW wOf nr nc v.1 (w.MG g))
    (hW : WeightsAre x tl D rad oW wOf nr nc g v.1 i.mat) : LayKeyAt X i w g :=
  lay_layKey (p := pubAt X g) Ex Wp H a v h (w.MG g) hM i.mat hW

/-- **layHot at the group g.** -/
theorem layHot_at (xi : Cm.Seg.XI) (a : Unit × Ex.Str) (v : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x (pubAt X g) tl D rad oW wOf nr nc Ex Wp]).A
      (layRider x (pubAt X g) tl D rad oW wOf nr nc Ex Wp)).relR a v)
    (hM : MatsAre x tl D rad oW wOf nr nc v.1 (w.MG g)) : LayHotAt X i xi w g :=
  lay_layHot (p := pubAt X g) Ex Wp a v h (w.MG g) hM i.mat xi

end

#print axioms attRidden_at
#print axioms attKey_at
#print axioms layKey_at
#print axioms layHot_at

end VerifiableInference.Desc.First.Look
