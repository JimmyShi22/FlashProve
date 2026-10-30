-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Single.lean: THE SHAPE OF THE SINGLE ROWS THAT A CLOSED SEGMENT LEAVES IN
THE FRAME OF THE CALLS (SingleRows, OnBytes/Iop/Fold.lean; the field rows of ReqFrame): what is left
of them when every field element is left out. Definitions, a way back, and that the shape of the way
back is the shape.

What it is for. The closing of a segment lays these rows; the code switch at the next segment's
first place reads them. Johnson/Desc/First/Shape/Calls.lean holds this shape as a field of the
frame's.

THE FIELDS' TYPES, so that a reader can hold them against the records (OnBytes/Iop/Tensor.lean:68
and :414, OnBytes/Iop/Ground.lean:287 and :311, OnBytes/Iop/Fold.lean:106):
  `TensorSh`  of Tensor: denseVars : List Nat and first : Nat as they are; of pairs its length; of
              values its size. LEFT OUT: scalar.
  `FormSh`    of Form: tensors : List TensorSh; of each single entry its index: entries : List Nat.
  `SingleSh`  of SingleRows: code maskCode masks fresh keptRows : Nat and layout : GroupLayout as
              they are; of gamma its length; c : FormSh; of each kept form its oracle message's
              number and its form's shape: kept : List (Nat × FormSh); of d each row's size:
              d : List Nat.
              LEFT OUT: target.
GroupLayout is the library's own record of numbers, Bools, arrays and options of these.

  `tensorSh`, `formSh`, `singleSh`: the makers: no default is laid.
  `TensorSh.blank`, `FormSh.blank`, `SingleSh.blank`: the way back: zeros for the elements.
  `tensorSh_blank`, `formSh_blank`, `singleSh_blank`.

Limits. A form's shape holds HOW MANY tensors the form has. Elsewhere in the library that number can
hang on values (tensorBelow in Tensor.lean drops terms): that no step of the first chain makes these
forms so is a reading, not a theorem. The test "at a written-out variable the pair is (1, 1)"
(Tensor.ok; Own.tensorInOrder) compares elements: it cannot be written on this shape, and is meant
not to be. Nothing on soundness, completeness or hiding.

-/
import OnBytes.Iop.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes

structure TensorSh where
  pairs : Nat
  denseVars : List Nat
  values : Nat
  first : Nat

def tensorSh (v : Tensor) : TensorSh :=
  { pairs := v.pairs.length, denseVars := v.denseVars, values := v.values.size, first := v.first }

def TensorSh.blank (v : TensorSh) : Tensor :=
  { scalar := zeroE, pairs := List.replicate v.pairs (zeroE, zeroE), denseVars := v.denseVars
    values := Array.replicate v.values zeroE, first := v.first }

theorem tensorSh_blank (v : TensorSh) : tensorSh v.blank = v := by
  cases v
  simp [tensorSh, TensorSh.blank]

structure FormSh where
  tensors : List TensorSh
  entries : List Nat

def formSh (c : Form) : FormSh :=
  { tensors := c.tensors.map tensorSh, entries := c.entries.map (·.1) }

def FormSh.blank (c : FormSh) : Form :=
  { tensors := c.tensors.map TensorSh.blank, entries := c.entries.map fun i => (i, zeroE) }

theorem formSh_blank (c : FormSh) : formSh c.blank = c := by
  cases c
  simp [formSh, FormSh.blank, Function.comp_def, tensorSh_blank]

structure SingleSh where
  code : Nat
  maskCode : Nat
  layout : GroupLayout
  gamma : Nat
  masks : Nat
  fresh : Nat
  c : FormSh
  kept : List (Nat × FormSh)
  d : List Nat
  keptRows : Nat

def singleSh (r : SingleRows) : SingleSh :=
  { code := r.code, maskCode := r.maskCode, layout := r.layout, gamma := r.gamma.length
    masks := r.masks, fresh := r.fresh, c := formSh r.c
    kept := r.kept.toList.map fun k => (k.oracle, formSh k.c), d := r.d.toList.map (·.size)
    keptRows := r.keptRows }

def SingleSh.blank (r : SingleSh) : SingleRows :=
  { code := r.code, maskCode := r.maskCode, layout := r.layout
    gamma := List.replicate r.gamma zeroE, masks := r.masks, fresh := r.fresh, c := r.c.blank
    kept := (r.kept.map fun k => ({ oracle := k.1, c := k.2.blank } : KeptForm)).toArray
    d := (r.d.map fun n => Array.replicate n zeroE).toArray, keptRows := r.keptRows }

theorem singleSh_blank (r : SingleSh) : singleSh r.blank = r := by
  cases r
  simp [singleSh, SingleSh.blank, Function.comp_def, formSh_blank]

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.tensorSh_blank
#print axioms VerifiableInference.Desc.First.Shape.formSh_blank
#print axioms VerifiableInference.Desc.First.Shape.singleSh_blank
