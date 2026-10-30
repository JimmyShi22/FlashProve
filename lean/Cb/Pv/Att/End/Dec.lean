-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Dec.lean: equality of entries can be decided, for the sumchecks of an attention
segment at the parameters of Cb/Pv/Att/Steps.lean, Step18.lean, BitsSc3.lean and OwnSteps.lean.

Instances. The forms of Cb/Pv/Att/End/Forms.lean ask that equality on the entries T.J of a plain
sumcheck T can be decided. At these parameters T.J is the type J of the entries, by definition, but
Lean's search for instances does not unfold the definitions. This file says it.

Main names: decStep, decBits, decKey, decPull.


-/
import Cb.Pv.Att.OwnSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open Cb Inst.Model.AttSeg

variable {E : Type} [Field E] [Fintype E] {J : Type} [Fintype J] [DecidableEq J]

instance decStep (D : Dim) (C : Calls) (rd : (J → E) → Raw → E) (s : Step) (inc : Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J)
    (cAt : Fin D.nb × Bool → J) : DecidableEq (stepSc3 D C rd s inc wAt cAt).plain.J :=
  inferInstanceAs (DecidableEq J)

instance decBits (kap : ℕ) (D : Dim) (rd : (J → E) → Raw → E) (inc : Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J)
    (cAt : Fin D.nb × Bool → J) : DecidableEq (bitsSc3 kap D rd inc wAt cAt).plain.J :=
  inferInstanceAs (DecidableEq J)

instance decKey (D : Dim) (rd : (J → E) → Raw → E) (inc : Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J)
    (cAt : (size18 D).A → J) : DecidableEq (step18 D rd inc wAt cAt).plain.J :=
  inferInstanceAs (DecidableEq J)

instance decPull (T : PlainSc E) [DecidableEq T.J] {St' : Type} (f : St' → T.St)
    (inc' : St' → T.J → E) : DecidableEq (T.pull f inc').J :=
  inferInstanceAs (DecidableEq T.J)

end Cb.Pv.Att.End
