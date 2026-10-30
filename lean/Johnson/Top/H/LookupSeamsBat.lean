-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupSeamsBat.lean: the seam behind a sub-proof's lookup where the next block is the
batching of rows.

The library's batching inside a body (Cb/Req1/LdSegRefPartBat.lean, LdPbD) begins at a base joint
that says: every row of a family sl holds of the entries of the committed messages, each at its own
target and state, beside a carried joint A₀. Behind a lookup (Johnson/Top/H/LookupSeams.lean) the
seam owes CarryOut: that joint's relation must give the lookup's output relation.

What the file states, for every caller c.
 - batIn c Sb sl A₀: that base joint, in the words of LdPbD.src (that it is LdPbD.src's own is not
   shown here).
 - Members c Sb sl A₀ f: the state map f lays what the lookup puts out among the family's rows: the
   condition of the caller's own joint R0 at the caller's old state gives the carried joint's at
   the laid state; the carried joint's relation gives the caller's own; for every row that the
   lookup puts out there is a member of the family whose claim, at the target and state that f
   lays, gives that row; the same for the masked claim on the joint shifted keys.
 - carryOut_members, seamBat_ok: then CarryOut holds and the seam is in order.
 - rowSl c pos: the family's member for a row that the lookup puts out: the row is its own state;
   its coefficients stand at the places pos j of the entries. rowSl_holds: its claim at the row's
   own target IS the row, if msg₀ reads entry j at the place pos j. So Members' clause on the rows
   can be met: by an f that lays each row of the lookup, with its own target, under a member rowSl.
   Johnson/Top/H/LookupSeamsKey.lean has such a map and shows Members of it (layRows, members_lay).

Limits. Members is a hypothesis on f and the family. All four of its clauses stand under f x = some
s': of a map that refuses everywhere Members holds, and the seam is in order, for nothing; the
place's verifier then refuses everything. The clause on the keys' claim is met by nothing here:
that claim reads the keys through the layout, and is a row on entries only where the layout's keys
are linear in the entries. Whether a member lies among the rows that are batched or among those
that are copied is not said; a row's state is part of the statement before the seed is drawn.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupSeamsAt
import Cb.Ld.LdBatSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp

section
variable (c : LookupCCaller) {Kc' B St₀' : Type} (Sb : B → Type)
  (sl : ∀ b, Slf Cb.Gl.E (Sb b) c.Sg.Ent) (A₀ : IOR.Rels Kc' St₀' c.Ex (c.Sg.Msg × c.Wp))

/-- The base joint at which the batching of rows begins. -/
@[reducible] def batIn :
    IOR.Rels Kc' (((B → Cb.Gl.E) × (∀ b, Sb b)) × St₀') c.Ex (c.Sg.Msg × c.Wp) :=
  claimRels (fun x m => Slf.All sl x (c.Sg.ents m)) A₀

/-- What the lookup puts out lies among the family's rows. -/
structure Members
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) →
      Option (((B → Cb.Gl.E) × (∀ b, Sb b)) × St₀')) : Prop where
  on : ∀ x y s', c.R0.on (x.1.1, y) → f x = some s' → A₀.on (s'.2, y)
  rider : ∀ x y s' w, c.R0.on (x.1.1, y) → f x = some s' → A₀.relR (s'.2, y) w →
    c.R0.relR (x.1.1, y) w
  rows : ∀ x s', f x = some s' → ∀ r ∈ x.2.2, ∃ b, ∀ m : c.Sg.Msg,
    (sl b).Holds (s'.1.1 b, s'.1.2 b) (c.Sg.ents m) → r.Holds (zext (c.msg₀ m))
  key : ∀ x s', f x = some s' → ∃ b, ∀ m : c.Sg.Msg,
    (sl b).Holds (s'.1.1 b, s'.1.2 b) (c.Sg.ents m) →
      x.2.1.Holds ((forA Cb.Gl.E c.h c.L).v' + 1)
        ((forA Cb.Gl.E c.h c.L).key x.1 (zext (c.msg₀ m))) (zext (c.msg₀ m))

theorem carryOut_members
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) →
      Option (((B → Cb.Gl.E) × (∀ b, Sb b)) × St₀'))
    (h : Members c Sb sl A₀ f) : CarryOut c (batIn c Sb sl A₀) f :=
  carryOut_of c (batIn c Sb sl A₀) f (fun x y s' ho hf => h.on x y s' ho hf)
    fun x y s' w ho hf hw => by
      refine ⟨h.rider x y s' w ho hf hw.2, ?_, fun r hr => ?_⟩
      · obtain ⟨b, hb⟩ := h.key x s' hf
        exact hb w.1 (hw.1 b)
      · obtain ⟨b, hb⟩ := h.rows x s' hf r hr
        exact hb w.1 (hw.1 b)

/-- The seam between the lookup and the batching of rows. -/
theorem seamBat_ok
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) →
      Option (((B → Cb.Gl.E) × (∀ b, Sb b)) × St₀'))
    (h : Members c Sb sl A₀ f) : (seamOut c (batIn c Sb sl A₀) f).OK :=
  seamOut_ok c _ f (carryOut_members c Sb sl A₀ f h)

end

section
variable (c : LookupCCaller) [DecidableEq c.Sg.Ent] (pos : c.J₀ → c.Sg.Ent)

/-- A row that the lookup puts out, as a form on all entries: the row is its own state. -/
def rowSl : Slf Cb.Gl.E (Row Cb.Gl.E (Option c.J₀)) c.Sg.Ent :=
  fun r n => ∑ j, if pos j = n then r.cf (some j) else 0

/-- Its claim at the row's own target is the row. -/
theorem rowSl_holds (hpos : ∀ m j, c.msg₀ m j = c.Sg.ents m (pos j))
    (r : Row Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) :
    (rowSl c pos).Holds (r.tg, r) (c.Sg.ents m) ↔ r.Holds (zext (c.msg₀ m)) := by
  have e : ∑ n, (∑ j, if pos j = n then r.cf (some j) else 0) * c.Sg.ents m n =
      ∑ j, r.cf (some j) * c.Sg.ents m (pos j) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (pos j)]
    · rw [if_pos rfl]
    · intro n _ hn
      rw [if_neg (Ne.symm hn), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  unfold Slf.Holds Row.Holds rowSl
  rw [e, Fintype.sum_option]
  simp only [zext, mul_zero, zero_add, hpos]

end

#print axioms VerifiableInference.OnPublicFiles.carryOut_members
#print axioms VerifiableInference.OnPublicFiles.seamBat_ok
#print axioms VerifiableInference.OnPublicFiles.rowSl_holds

end VerifiableInference.OnPublicFiles
