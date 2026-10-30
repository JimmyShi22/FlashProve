-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/StringTo.lean: an argument string for one batch protocol as an argument string for
another whose rounds and external strings are the same by equations, not by unfolding.

The type of argument strings `OneProtocolProof lam Q` (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) hangs on the
protocol Q through its rounds (`Q.loc.shape`) and the kind E of its external strings alone: not on
its instances, its decision, what it reads, or its annotation. Six of a string's nine fields do not
hang on Q at all. So a string is carried to another protocol by carrying three fields along
equations (two, where the kind of external strings is one and the same).

Main names:
  `plTo`, `opTo`, `exTo`: the plain parts, the openings of the prover's oracles, the openings of the
    external strings, carried along an equation; `plTo_heq`, `opTo_heq`, `exTo_heq`: each is what it
    was, as a heterogeneous equation.
  `strTo hs hE π`: the string π, carried.
  `strTo_salt`, `strTo_roots`, `strTo_rtreq`, `strTo_slot`, `strTo_path`, `strTo_rsalt`: six fields
    are π's. `strTo_plains`, `strTo_opens`, `strTo_ext`: three are π's as heterogeneous equations.
  `strTo_ext_eq`: where the kind of external strings is one and the same, the third is an equation.
  `strTo_rfl`: along two trivial equations the string is itself.

Limits: types and values alone. Nothing on any verifier.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace OnBytes.K
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol

variable {lam : ℕ}

/-- plain parts, carried along an equation of rounds -/
def plTo {s s' : Shape} (h : s = s') (x : Plains s) : Plains s' := h ▸ x

/-- openings of the prover's oracles, carried along an equation of rounds -/
def opTo {s s' : Shape} (h : s = s') (f : (p : OPos s) → Option (Opening lam (OSym s p))) :
    (p : OPos s') → Option (Opening lam (OSym s' p)) := h ▸ f

/-- openings of the external strings, carried along an equation of their kinds -/
def exTo {E E' : ExtSpec} (h : E = E') (f : E.Pos → Option (Opening lam E.Sym)) :
    E'.Pos → Option (Opening lam E'.Sym) := h ▸ f

theorem plTo_heq {s s' : Shape} (h : s = s') (x : Plains s) : HEq (plTo h x) x := by
  subst h
  rfl

theorem opTo_heq {s s' : Shape} (h : s = s')
    (f : (p : OPos s) → Option (Opening lam (OSym s p))) : HEq (opTo h f) f := by
  subst h
  rfl

theorem exTo_heq {E E' : ExtSpec} (h : E = E') (f : E.Pos → Option (Opening lam E.Sym)) :
    HEq (exTo h f) f := by
  subst h
  rfl

variable {Y Y' : Type} {E E' : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Q' : BatchInteractiveOracleProof Y' E'}

/-- The argument string π for Q, as one for Q': the rounds are the same by hs, the kind of external
strings by hE. -/
def strTo (hs : Q.loc.shape = Q'.loc.shape) (hE : E = E') (π : OneProtocolProof lam Q) : OneProtocolProof lam Q' :=
  ⟨π.salt, π.roots, plTo hs π.plains, opTo hs π.opens, exTo hE π.ext, π.rtreq, π.slot, π.path,
    π.rsalt⟩

section Fields
variable (hs : Q.loc.shape = Q'.loc.shape) (hE : E = E') (π : OneProtocolProof lam Q)

theorem strTo_salt : (strTo hs hE π).salt = π.salt := rfl
theorem strTo_roots : (strTo hs hE π).roots = π.roots := rfl
theorem strTo_rtreq : (strTo hs hE π).rtreq = π.rtreq := rfl
theorem strTo_slot : (strTo hs hE π).slot = π.slot := rfl
theorem strTo_path : (strTo hs hE π).path = π.path := rfl
theorem strTo_rsalt : (strTo hs hE π).rsalt = π.rsalt := rfl
theorem strTo_plains : HEq (strTo hs hE π).plains π.plains := plTo_heq hs π.plains
theorem strTo_opens : HEq (strTo hs hE π).opens π.opens := opTo_heq hs π.opens
theorem strTo_ext : HEq (strTo hs hE π).ext π.ext := exTo_heq hE π.ext

end Fields

/-- Where the kind of external strings is one and the same, their openings are π's. -/
theorem strTo_ext_eq {Q'' : BatchInteractiveOracleProof Y' E} (hs : Q.loc.shape = Q''.loc.shape) (π : OneProtocolProof lam Q) :
    (strTo hs rfl π).ext = π.ext := rfl

/-- Along two trivial equations the string is itself. -/
theorem strTo_rfl (π : OneProtocolProof lam Q) : strTo (Q' := Q) rfl rfl π = π := rfl

end OnBytes.K
