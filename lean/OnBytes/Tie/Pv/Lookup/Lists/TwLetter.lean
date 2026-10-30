-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean.
The rounds and the errors of the whole lookup where the sumcheck's letter is filled by the two
records ShortK, ShortKC: no premise on the letter is left, since its two laws are fields of these
records.

For every finite field E, every record A of a lookup's letters, every V : ∀ Y Ex, ShortK Y Ex and VC
: ∀ Y Ex, ShortKC Y Ex.
Main statements.
  asmV_shape: OnBytes.G4.ShapeIs E (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape (entG ..). asmV_eps:
    the list of that block's errors is epsG ... asmV_shape_port, asmV_eps_port: where A.oE =
    Fin.revPerm the two lists are TwPlan.entN and TwErr.epsN.
  shapeIs_unique, asmV_bent: no list that differs from entG in msg, drawE or drawNZ of some entry is
    ShapeIs of that shape (over a field of more than two elements).
  shapeIs_sizes, asmV_sizes: each round's challenge set has the size that its entry says.
  asmV_shape_gl, asmV₀_shape_gl: at the challenge field; at the filling V₀, V₀C.
To be read with it. ShapeIs counts: it ties sizes, not which scalar is which, and it ties three of
an entry's twelve fields. A verifier that rejects everything also fills ShortK: a statement for
every filling says nothing on what is accepted.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwAsm
import Cb.Pv.Lookup.Know.AsmKV
import Cb.G6.Pick

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 Johnson.L5.Layers

section
variable {E : Type} [Field E] [Fintype E]

variable (V : ∀ (Y : PscPar E) Ex, TWhole.ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, TWhole.ShortKC Y Ex) (Ex : ExtSpec)

theorem ltShape_ofShort : LtShape (PscLtK.ofShort V VC Ex) :=
  ⟨fun Y => (V Y Ex).shape, fun Y => (VC Y Ex).shape⟩
theorem ltErr_ofShort : LtErr (PscLtK.ofShort V VC Ex) :=
  ⟨fun Y => (V Y Ex).nums, fun Y => (VC Y Ex).nums⟩

variable (A : LkAsmH E)

theorem asmV_shape (wk : Nat) :
    ShapeIs E (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape
        (entG wk A.v' A.d A.w A.n (List.ofFn (dgEnd A.w A.d A.oE))) :=
  asmK_roundIs A (ltShape_ofShort V VC Ex) wk

theorem asmV_eps :
    TWhole.errList (A.baseKS (PscLtK.ofShort V VC Ex)).e = epsG A.v' A.d A.w A.n (Fintype.card E)
        (List.ofFn (dgEnd A.w A.d A.oE)) :=
  asmK_eps A (ltErr_ofShort V VC Ex)

theorem asmV_shape_port (wk : Nat) (ho : A.oE = Fin.revPerm) :
    ShapeIs E (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape (entN wk A.v' A.d A.w A.n) :=
  asmK_roundIs_port A (ltShape_ofShort V VC Ex) wk ho

theorem asmV_eps_port (ho : A.oE = Fin.revPerm) :
    TWhole.errList (A.baseKS (PscLtK.ofShort V VC Ex)).e = epsN A.v' A.d A.w A.n (Fintype.card E) :=
  asmK_eps_port A (ltErr_ofShort V VC Ex) ho

/-- Two lists that are both ShapeIs of one shape agree in msg, drawE and drawNZ, entry by entry. -/
theorem shapeIs_unique (hq : 2 < Nat.card E) : ∀ {s : Shape} {ds ds' : List Fmt.Entry},
    ShapeIs E s ds → ShapeIs E s ds' →
    List.Forall₂ (fun e e' : Fmt.Entry => e.msg = e'.msg ∧ e.drawE = e'.drawE ∧ e.drawNZ =
        e'.drawNZ) ds ds'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (h.unique hq h') (shapeIs_unique hq t t')

/-- No list that differs from entG in msg, drawE or drawNZ of some entry is ShapeIs of the lookup's
shape. -/
theorem asmV_bent (hq : 2 < Nat.card E) (wk : Nat) (ds' : List Fmt.Entry)
    (hne : ¬ List.Forall₂ (fun e e' : Fmt.Entry => e.msg = e'.msg ∧ e.drawE = e'.drawE ∧ e.drawNZ =
        e'.drawNZ)
      (entG wk A.v' A.d A.w A.n (List.ofFn (dgEnd A.w A.d A.oE))) ds') :
    ¬ ShapeIs E (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape ds' :=
  fun h => hne (shapeIs_unique hq (asmV_shape V VC Ex A wk) h)

/-- the size that an entry says -/
def sizeOf (q : Nat) (e : Fmt.Entry) : Nat :=
  if e.drawNZ = 0 then q ^ e.drawE else if e.drawNZ = 1 ∧ e.drawE = 1 then q - 1 else 0

/-- The sizes of a shape's challenge sets are the sizes that its entries say. -/
theorem shapeIs_sizes : ∀ {s : Shape} {ds : List Fmt.Entry}, ShapeIs E s ds →
    s.map (fun r => Nat.card r.Chal) = ds.map (sizeOf (Nat.card E))
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.map_cons, List.map_cons, shapeIs_sizes t, h.card_chal]
    rfl

theorem asmV_sizes (ho : A.oE = Fin.revPerm) :
    (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape.map (fun r => Nat.card r.Chal) =
      (entN 0 A.v' A.d A.w A.n).map (sizeOf (Nat.card E)) :=
  shapeIs_sizes (asmV_shape_port V VC Ex A 0 ho)

end

/-- At the challenge field, for every A, V, VC. -/
theorem asmV_shape_gl (V : ∀ (Y : PscPar Cb.Gl.E) Ex, TWhole.ShortK Y Ex)
    (VC : ∀ (Y : PscPar Cb.Gl.E) Ex, TWhole.ShortKC Y Ex)
    (Ex : ExtSpec) (A : LkAsmH Cb.Gl.E) (wk : Nat) (ho : A.oE = Fin.revPerm) :
    ShapeIs Cb.Gl.E (A.baseKS (PscLtK.ofShort V VC Ex)).R.shape (entN wk A.v' A.d A.w A.n) :=
  asmV_shape_port V VC Ex A wk ho

/-- At the short sumchecks `TWhole.V₀`, `TWhole.V₀C`. -/
theorem asmV₀_shape_gl (Ex : ExtSpec) (A : LkAsmH Cb.Gl.E) (wk : Nat) (ho : A.oE = Fin.revPerm) :
    ShapeIs Cb.Gl.E (A.baseKS (PscLtK.ofShort TWhole.V₀ TWhole.V₀C Ex)).R.shape
        (entN wk A.v' A.d A.w A.n) :=
  asmV_shape_gl _ _ Ex A wk ho

end TwRound
