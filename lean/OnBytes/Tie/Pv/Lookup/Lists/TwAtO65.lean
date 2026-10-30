-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwAtO65.lean.
The rounds and the errors of the assembled lookup at the small lookup `o65A`, for every V, VC, and
at `V₀`, `V₀C`.

Statements and proofs, from the general ones of OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean.
Main names:
  `o65ds : List Fmt.Entry := entN 0 3 1 3 6`: the 65 entries.
  `o65_shape`: `OnBytes.G4.ShapeIs Cb.Gl.E (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape o65ds`. No
    premise is left: `o65A.oE = Fin.revPerm` (`o65_oE`) and the four numbers 3, 1, 3, 6 hold by rfl.
  `o65_eps`: the list of the errors of that chain is `epsN 3 1 3 6 (Fintype.card Cb.Gl.E)`.
  `o65_sizes`: each round's number of challenges is what its entry says. `o65_len`: 65 rounds.
  `o65_bent`: no list that differs from `o65ds` in msg, drawE or drawNZ of some entry, or in length,
    is `ShapeIs` of that shape.
  `o65_card`: `Fintype.card Cb.Gl.E = Cb.Gl.p ^ 3` (`Cb.Gl.gl_card`).
  `o65_shape₀`, `o65_eps₀`: `o65_shape`, `o65_eps` at `V₀`, `V₀C` (Cb/G6/Pick.lean).
Limits: `ShapeIs` ties three of an entry's numbers to its round (the bytes of the message, the
elements drawn, whether the draw is non-zero); the name and the other eight are tied to a typed
round by nothing (OnBytes/Tie/Pv/Lookup/Lists/TwPlan.lean); the 0 in `entN 0 ..`, the bits of work,
is one of the eight. A verifier that rejects everything also fills `ShortK`: a statement for every
V, VC says nothing on what is accepted.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwLetter
import OnBytes.Tie.Pv.Lookup.Value.TwO65

set_option autoImplicit false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 Cb.Tw

def o65ds : List Fmt.Entry := entN 0 3 1 3 6

theorem o65_oE : o65A.oE = Fin.revPerm := rfl

section
variable (V : ∀ (Y : PscPar Cb.Gl.E) Ex, TWhole.ShortK Y Ex) (VC : ∀ (Y : PscPar Cb.Gl.E) Ex,
    TWhole.ShortKC Y Ex) (Ex : ExtSpec)

theorem o65_shape : ShapeIs Cb.Gl.E (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape o65ds :=
  asmV_shape_gl V VC Ex o65A 0 o65_oE

theorem o65_eps : TWhole.errList (o65A.baseKS (PscLtK.ofShort V VC Ex)).e = epsN 3 1 3 6
    (Fintype.card Cb.Gl.E) :=
  asmV_eps_port V VC Ex o65A o65_oE

theorem o65_sizes : (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape.map (fun r => Nat.card r.Chal) =
    o65ds.map (sizeOf (Nat.card Cb.Gl.E)) :=
  asmV_sizes V VC Ex o65A o65_oE

theorem o65_len : (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape.length = 65 :=
  (List.Forall₂.length_eq (o65_shape V VC Ex)).trans (by decide)

theorem o65_bent (ds' : List Fmt.Entry)
    (hne : ¬ List.Forall₂ (fun e e' : Fmt.Entry => e.msg = e'.msg ∧ e.drawE = e'.drawE ∧ e.drawNZ =
        e'.drawNZ) o65ds ds') :
    ¬ ShapeIs Cb.Gl.E (o65A.baseKS (PscLtK.ofShort V VC Ex)).R.shape ds' :=
  fun h => hne (shapeIs_unique two_lt_card_gl (o65_shape V VC Ex) h)

end

theorem o65_card : Fintype.card Cb.Gl.E = Cb.Gl.p ^ 3 := Cb.Gl.gl_card.2.1

/-- At `V₀`, `V₀C`. -/
theorem o65_shape₀ (Ex : ExtSpec) : ShapeIs Cb.Gl.E (o65A.baseKS (PscLtK.ofShort TWhole.V₀
    TWhole.V₀C Ex)).R.shape o65ds := o65_shape _ _ Ex
theorem o65_eps₀ (Ex : ExtSpec) :
    TWhole.errList (o65A.baseKS (PscLtK.ofShort TWhole.V₀ TWhole.V₀C Ex)).e = epsN 3 1 3 6
        (Fintype.card Cb.Gl.E) := o65_eps _ _ Ex

end TwRound

#print axioms TwRound.o65_shape
#print axioms TwRound.o65_eps
#print axioms TwRound.o65_sizes
#print axioms TwRound.o65_len
#print axioms TwRound.o65_bent
#print axioms TwRound.o65_shape₀
#print axioms TwRound.o65_eps₀
