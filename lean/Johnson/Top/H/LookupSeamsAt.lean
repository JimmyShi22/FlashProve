-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupSeamsAt.lean: the two hypotheses of Johnson/Top/H/LookupSeams.lean, written
out.

What the file states, for every caller c.
 - forIn_on, forIn_relR, forOut_on, forOut_relR: the condition and the relaxed relation of the
   lookup's two base joints, clause by clause (each by rfl).
 - splitIn_of: SplitIn c A holds if A's condition gives the condition of the caller's own joint R0,
   and A's relation follows from: R0's relation, and for every call k below NC each of the call's
   keys, read off the committed messages, is a row of that call's table.
 - carryOut_of: CarryOut c C f holds if R0's condition at the caller's old state gives C's at f x,
   and C's relation at f x gives: R0's relation at the caller's old state; the masked claim on the
   joint shifted keys in x; every row in x, at the entries read off the committed messages, the
   entry that is no cell read as 0.

Limits: as in LookupSeams.lean. The premises of the two theorems are hypotheses on the neighbour's
joint.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupSeams

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp

variable (c : LookupCCaller)

theorem forIn_on (a : c.St₀ × c.Ex.Str) :
    (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a = c.R0.on a := rfl

theorem forIn_relR (a : c.St₀ × c.Ex.Str) (w : c.Sg.Msg × c.Wp) :
    (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a w =
      (c.R0.relR a w ∧ ∀ k < c.h.NC, InTable (Port.nOf c.h k) (Port.kOf c.h k)
        (forK Cb.Gl.E c.L a.1 (zext (c.msg₀ w.1)) k) (forT Cb.Gl.E c.h a.1 k)) := rfl

theorem forOut_on (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).on b = c.R0.on (b.1.1.1, b.2) := rfl

theorem forOut_relR (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str)
    (w : c.Sg.Msg × c.Wp) :
    (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).relR b w =
      (c.R0.relR (b.1.1.1, b.2) w ∧
        (b.1.2.1.Holds ((forA Cb.Gl.E c.h c.L).v' + 1)
            ((forA Cb.Gl.E c.h c.L).key b.1.1 (zext (c.msg₀ w.1))) (zext (c.msg₀ w.1)) ∧
          RowsHold b.1.2.2 (zext (c.msg₀ w.1)) ∧ True)) := rfl

theorem splitIn_of (A : IOR.Rels c.Kc c.St₀ c.Ex (c.Sg.Msg × c.Wp))
    (on : ∀ a, A.on a → c.R0.on a)
    (rel : ∀ a w, A.on a → c.R0.relR a w →
      (∀ k < c.h.NC, InTable (Port.nOf c.h k) (Port.kOf c.h k)
        (forK Cb.Gl.E c.L a.1 (zext (c.msg₀ w.1)) k) (forT Cb.Gl.E c.h a.1 k)) → A.relR a w) :
    SplitIn c A :=
  ⟨on, fun a w ha h => rel a w ha h.1 h.2⟩

theorem carryOut_of {Kc' St' : Type} (C : IOR.Rels Kc' St' c.Ex (c.Sg.Msg × c.Wp))
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option St')
    (on : ∀ x y s', c.R0.on (x.1.1, y) → f x = some s' → C.on (s', y))
    (rel : ∀ x y s' w, c.R0.on (x.1.1, y) → f x = some s' → C.relR (s', y) w →
      c.R0.relR (x.1.1, y) w ∧
        x.2.1.Holds ((forA Cb.Gl.E c.h c.L).v' + 1)
          ((forA Cb.Gl.E c.h c.L).key x.1 (zext (c.msg₀ w.1))) (zext (c.msg₀ w.1)) ∧
        RowsHold x.2.2 (zext (c.msg₀ w.1))) :
    CarryOut c C f :=
  ⟨on, fun x y s' w ho hf hw =>
    ⟨(rel x y s' w ho hf hw).1, (rel x y s' w ho hf hw).2.1, (rel x y s' w ho hf hw).2.2, trivial⟩⟩

#print axioms VerifiableInference.OnPublicFiles.splitIn_of
#print axioms VerifiableInference.OnPublicFiles.carryOut_of

end VerifiableInference.OnPublicFiles
