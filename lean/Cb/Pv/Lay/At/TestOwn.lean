-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/TestOwn.lean: a toy: the letters' records of Cb/Pv/Lay/At/OwnW.lean and OwnFirstW.lean
are inhabited at the library's reference sizes (Dim.ref), so their conditions can be met together.

Main names:
  `toy`: a value of FullPar over the field of 3 elements, at Dim.ref, the reference scales and
    L0 = 0: one entry; the cells read as 0; the committed matrix read as 0,
    with just room for all units; the group's weights the library's reading of that matrix; every
    mask at the one entry; the weight claims numbered by Fintype.equivFin.
  `toyF`: the like value of FullFPar: the features cut as 5 high parts of 2^10; token 0 at every
    position.
  `toy_knowAt`, `toyF_knowAt`: own_knowAt and ownF_knowAt applied at them.

Limits: nothing is said on the programs. The readings are trivial: this file shows that no two
fields of the letters' records contradict one another at the reference sizes, and nothing more. As
statements of soundness the two theorems say nothing: over 3 elements several of the chain's bounds
on bad draws exceed the number of draws.


-/
import Cb.Pv.Lay.At.OwnFirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At.Toy
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.FFSeg (Dim layerR)

noncomputable section

/-- The field of 3 elements. -/
abbrev F3 : Type := ZMod 3

/-- The reference scales. -/
local instance sclRef : Scl := Inst.Model.Scl.ref

/-- The tables, all 0. -/
def tb0 : Tables := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- The letters of the chain of a sub-proof that is not the first, at the reference sizes. -/
def toy : FullPar F3 Unit Unit where
  D := Dim.ref
  tb := tb0
  L0 := 0
  J := Unit
  msg := fun _ _ => 0
  rd := fun _ _ => 0
  rw := fun _ l => layerR Dim.ref.P 10 (fun _ _ => 0) (0 + l)
  two := by decide
  zOf := fun _ _ => 0
  kTg := fun _ => 0
  kInc := fun _ _ => 0
  eS := Equiv.refl _
  mkS := fun _ _ => ()
  wS := fun _ => ()
  cS := fun _ => ()
  mkP := fun _ => ()
  rP := ()
  wP := fun _ => ()
  cP := fun _ => ()
  rT := ()
  wT := fun _ => ()
  cT := fun _ => ()
  hrd := fun _ _ _ _ _ => by simp
  hfe := by decide
  wI := fun _ => ()
  cI := fun _ => ()
  e5 := Equiv.refl _
  e6 := Equiv.refl _
  w5 := fun _ => ()
  c5 := fun _ => ()
  w6 := fun _ => ()
  c6 := fun _ => ()
  kW := 10
  hW := off 10 (units Dim.ref.P) (units Dim.ref.P).length
  Wn := fun _ _ _ => 0
  hrw := fun _ => rfl
  nW := Fintype.card (Piece Dim.ref)
  num := (Fintype.equivFin (Piece Dim.ref)).symm
  w7 := fun _ => ()
  c7 := ()
  h0 := rfl
  hf := by decide
  hh := ref_heads
  hLay := by decide
  hH := le_refl _

/-- The letters of the chain of the first sub-proof, at the reference sizes. -/
def toyF : FullFPar F3 Unit Unit where
  toFullPar := toy
  ls := 10
  nb := 5
  gB := 3
  hnb := by decide
  hd := by decide
  tok := fun _ _ => 0
  mkE := ()

/-- own_knowAt, applied. -/
theorem toy_knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (Unit × Wp))
    (pr : Unit → X0) (Dn : Unit → Unit → Prop) :
    KnowAt (toy.own.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ toy.own.pT x m)
      (jt A0 (fun e => pr (toy.own.toOwn.ch.back e)) (toy.own.toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) (toy.own.toOwn.ch.eps Ex) :=
  toy.own_knowAt Ex A0 pr Dn

/-- ownF_knowAt, applied. -/
theorem toyF_knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (Unit × Wp))
    (pr : Unit → X0) (Dn : Unit → Unit → Prop) :
    KnowAt (toyF.ownF.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ toyF.ownF.pT x m)
      (jt A0 (fun e => pr (toyF.ownF.toOwn.ch.back e)) (toyF.ownF.toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) (toyF.ownF.toOwn.ch.eps Ex) :=
  toyF.ownF_knowAt Ex A0 pr Dn

end
end Cb.Pv.Lay.At.Toy

#print axioms Cb.Pv.Lay.At.Toy.toy_knowAt
#print axioms Cb.Pv.Lay.At.Toy.toyF_knowAt
