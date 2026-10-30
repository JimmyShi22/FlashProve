-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/CarryKit.lean: a function of a kit of challenge types (PQ.CK, Run/PlanQTypes.lean)
and of the wiring's function at that kit, whose result type does not depend on the kit, has the same
value at ckPT f (Johnson/RunOne/DrawT.lean) and at ckP f (Run/PlanPull.lean): the one line by which
a run at ckPT f speaks of the term at ckP f.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. ckPT f is ckP f (ckPT_eq), but the two are not the same text: they part in the field dr. A
description's type of argument strings hangs on the whole description, and so on dr: a string typed
at the one kit is not typed at the other, and an equation between a verifier's two values cannot
even be written letter by letter. It can be written where the term is given AS A FUNCTION OF THE
KIT, with every letter whose type hangs on the kit made inside that function. The wiring's function
from hash blocks to a challenge is the one such letter that is not made of the kit: its type hangs
on the field Ch alone, which is one text in both kits, so one term serves at both.

How to use it. Write the term that an asking file runs as T C chal, for every kit C and every chal
of C: the carrier, the page, the codes of leaves' bodies, the argument string (from the parsed file)
and the lists are made inside T from C and chal. Run T (ckPT f) (chalP f K). carry_ckPT says that
its value is T (ckP f) (chalP f K).

Main theorems.
  carryKit: at two equal kits and one wiring function, T has one value.
  carry_ckPT: T (ckPT f) chal = T (ckP f) chal, for every T and every chal of ckP f. No premise.
  carry_ckPT0: the same for a T of the kit alone.

Limits. Nothing is said of any T. That a given term is T at these letters is the caller's to show
(by rfl, if it is written so). Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.DrawT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne

open _root_.Run _root_.Iop

/-- At two equal kits and one wiring function, whatever is defined for every kit has one value. -/
theorem carryKit {K : ℕ} {α : Type}
    (T : (C : PQ.CK) → (∀ e k, (Fin K → Dig 256) → C.Ch e k) → α) (C C' : PQ.CK) (h : C = C')
    (c : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (c' : ∀ e k, (Fin K → Dig 256) → C'.Ch e k)
    (hc : HEq c c') : T C c = T C' c' := by
  subst h
  rw [eq_of_heq hc]

/-- **A run at the kit made for a run speaks of the term at the descriptions' kit.** No premise. -/
theorem carry_ckPT {K : ℕ} {α : Type}
    (T : (C : PQ.CK) → (∀ e k, (Fin K → Dig 256) → C.Ch e k) → α) (f : Fmt.Fld)
    (chal : ∀ e k, (Fin K → Dig 256) → (ckP f).Ch e k) :
    T (ckPT f) chal = T (ckP f) chal :=
  carryKit T (ckPT f) (ckP f) (ckPT_eq f) chal chal HEq.rfl

/-- The same for what hangs on the kit alone. -/
theorem carry_ckPT0 {α : Type} (T : PQ.CK → α) (f : Fmt.Fld) : T (ckPT f) = T (ckP f) :=
  congrArg T (ckPT_eq f)

end Johnson.RunOne

#print axioms Johnson.RunOne.carry_ckPT
#print axioms Johnson.RunOne.carry_ckPT0
