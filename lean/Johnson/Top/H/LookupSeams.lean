-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupSeams.lean: the seams at the two ends of a sub-proof's lookup, each brought
down to one implication between conditions and one between relaxed relations on committed messages.

In a row of blocks (Johnson/E/KObj/RowS.lean) the seam behind a block is a step without rounds, and
what it owes is StepD.OK: the map of oracles is local; the condition is carried; a witness of the
next block's input relation is turned back into one of this block's output relation. The lookup's
own two joints are fixed by its kind (Johnson/Top/H/LookupC.lean): before the block Cb.Fo.forIn,
behind it Cb.Fo.forOut, both over the caller's signature. In this file "relation" means the relaxed
relation throughout: a joint over a signature takes the base joint's condition and relaxed relation
alone.

What the file states, for every caller c, so for every group's number. The seams are typed at the
kind of the list [c]; the kind's two joints at c do not read the list.
 - stepSame, stepSame_ok: between two joints over one signature, with one type of oracles and of
   further witnesses: a step that maps the state alone; it is in order if the base condition is
   carried and the base relation behind the step gives the base relation before it.
 - SplitIn c A: the neighbour before the lookup ends at the base joint A. Its condition gives the
   lookup's; and the lookup's input relation (the caller's own joint R0, and for every call each
   key is a row of that call's table) gives A's relation.
   seamIn c A, seamIn_ok: then the seam before the lookup is in order.
 - CarryOut c C f: the neighbour behind the lookup begins at the base joint C, at the state f x.
   The lookup's condition behind the block gives C's; and C's relation gives the lookup's output
   relation (R0 at the caller's old state; the masked claim on the joint shifted keys and all rows
   put out hold of the entries).
   seamOut c C f, seamOut_ok: then the seam behind the lookup is in order.
 - splitIn_self, carryOut_self: both hypotheses are met by the lookup's own joints, by the
   identity. Of a neighbour nothing is shown.

Limits. SplitIn and CarryOut are hypotheses: which base joint a neighbour has, and that the two
implications hold there, is said nowhere in this file. There are three cheap ways to meet them.
CarryOut holds of every C at a state map that refuses everywhere, for both its clauses stand under
f x = some s': a seam that lets nothing through is in order. SplitIn holds of every A whose
condition is never met. And with R0 taken as a relation that already holds the clause "each key is
a row of its table", SplitIn is met and the lookup's block shows nothing: R0 is meant to be the
neighbour's relation without that clause. The neighbour must be laid over the caller's own
signature, oracles and further witness, and the neighbour before the lookup over the caller's type
Kc too; where it is not, a step that turns these is owed beside.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupC
import Johnson.E.KObj.RowS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp

/-! ### a step on the state alone, over one signature -/

section
variable {E : Type} [Field E] (S : Sig E) {Kc Kc' St St' Wp : Type} {E₀ : ExtSpec}

/-- A step that maps the state and leaves samples, oracles and witnesses as they are. -/
@[reducible] def stepSame (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) (B : IOR.Rels Kc' St' E₀ (S.Msg ×
    Wp))
    (f : St → Option St') : StepD (jOver S A) (jOver S B) where
  f := fun x => (f x.1).map fun s => (s, x.2)
  g := ExtMap.id _
  back := fun _ w => w

theorem stepSame_ok (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) (B : IOR.Rels Kc' St' E₀ (S.Msg × Wp))
    (f : St → Option St')
    (on : ∀ (s : St) (y : E₀.Str) (s' : St'), A.on (s, y) → f s = some s' → B.on (s', y))
    (rel : ∀ (s : St) (y : E₀.Str) (s' : St') (w : S.Msg × Wp), A.on (s, y) → f s = some s' →
      B.relR (s', y) w → A.relR (s, y) w) : (stepSame S A B f).OK where
  isLocal := fun _ _ q h => h q (Finset.mem_singleton_self q)
  onOut := by
    rintro ⟨⟨s, z⟩, y⟩ x' ha hf
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact ⟨ha.1, on s y.1 s' ha.2 hs⟩
  know := by
    rintro ⟨⟨s, z⟩, y⟩ x' w ha hf hw
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact ⟨hw.1, rel s y.1 s' _ ha.2 hs hw.2⟩

end

/-! ### before the lookup -/

/-- The neighbour's base joint A before the lookup is given back by the lookup's input relation. -/
structure SplitIn (c : LookupCCaller) (A : IOR.Rels c.Kc c.St₀ c.Ex (c.Sg.Msg × c.Wp)) : Prop where
  on : ∀ a, A.on a → (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a
  rel : ∀ a w, A.on a → (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).relR a w → A.relR a w

/-- The seam before the lookup. -/
@[reducible] def seamIn (c : LookupCCaller) (A : IOR.Rels c.Kc c.St₀ c.Ex (c.Sg.Msg × c.Wp)) :
    StepD (jOver c.Sg A) ((kLookupC [c]).toKind.src c) :=
  stepSame c.Sg A (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) some

theorem seamIn_ok (c : LookupCCaller) (A : IOR.Rels c.Kc c.St₀ c.Ex (c.Sg.Msg × c.Wp))
    (h : SplitIn c A) : (seamIn c A).OK :=
  stepSame_ok c.Sg A _ some
    (fun s y s' ha e => by obtain rfl := Option.some.inj e; exact h.on _ ha)
    (fun s y s' w ha e hw => by obtain rfl := Option.some.inj e; exact h.rel _ w ha hw)

theorem splitIn_self (c : LookupCCaller) : SplitIn c (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀) :=
  ⟨fun _ h => h, fun _ _ _ h => h⟩

/-! ### behind the lookup -/

/-- The neighbour's base joint C behind the lookup, at the state f x, gives the lookup's output
relation. -/
structure CarryOut (c : LookupCCaller) {Kc' St' : Type}
    (C : IOR.Rels Kc' St' c.Ex (c.Sg.Msg × c.Wp))
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option St') : Prop where
  on : ∀ x y s', (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).on (x, y) → f x = some s' → C.on (s', y)
  rel : ∀ x y s' w, (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).on (x, y) → f x = some s' →
    C.relR (s', y) w → (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀).relR (x, y) w

/-- The seam behind the lookup. -/
@[reducible] def seamOut (c : LookupCCaller) {Kc' St' : Type}
    (C : IOR.Rels Kc' St' c.Ex (c.Sg.Msg × c.Wp))
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option St') :
    StepD ((kLookupC [c]).toKind.dst c) (jOver c.Sg C) :=
  stepSame c.Sg (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) C f

theorem seamOut_ok (c : LookupCCaller) {Kc' St' : Type}
    (C : IOR.Rels Kc' St' c.Ex (c.Sg.Msg × c.Wp))
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option St') (h : CarryOut c C f) :
    (seamOut c C f).OK :=
  stepSame_ok c.Sg _ C f h.on h.rel

theorem carryOut_self (c : LookupCCaller) :
    CarryOut c (forOut Cb.Gl.E c.h c.L c.R0 c.msg₀) some :=
  ⟨fun _ _ _ h e => by obtain rfl := Option.some.inj e; exact h,
    fun _ _ _ _ _ e h => by obtain rfl := Option.some.inj e; exact h⟩

#print axioms VerifiableInference.OnPublicFiles.stepSame_ok
#print axioms VerifiableInference.OnPublicFiles.seamIn_ok
#print axioms VerifiableInference.OnPublicFiles.seamOut_ok

end VerifiableInference.OnPublicFiles
