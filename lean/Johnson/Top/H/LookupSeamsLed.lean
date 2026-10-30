-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupSeamsLed.lean: the seam behind a sub-proof's lookup on the digits, where the
next block is the draw that batches a ledger of claims.

That draw (Cb/Pv/Att/BatchRide.lean) begins at the base joint ledInA A0 n msg: a carried joint A0,
and every claim of the ledger in the statement holds of the entries; on the statements whose ledger
has at most n claims. Behind a lookup (Johnson/Top/H/LookupSeams.lean) the seam owes CarryOut: that
joint's relation must give the lookup's output relation. Every theorem here that says that a seam
is in order stands under KeysAre (Johnson/Top/H/LookupSeamsKey.lean): each key of the layout is one
entry or none. That holds at the lookups on the digits and fails at the lookups of the calls.

What the file states, for a caller c, at the ledger's entries J := c.J₀ read by msg := c.msg₀.
 - rowForm r: a row that the lookup puts out, as a claim of a ledger: its coefficients at the
   entries, its target. rowForm_holds: the claim holds of the entries ν if and only if the row
   holds of ν with the entry that is no cell read as 0.
 - MembersLed c kp A0 n f: the state map f lays what the lookup puts out into the ledger: the
   carried joint's condition and the bound n on the ledger's length are met; the carried joint's
   relation together with the ledger's claims, all holding of the entries, gives the caller's own;
   each row that the lookup puts out, and the row keyRow c kp x of the masked claim on the keys
   (Johnson/Top/H/LookupSeamsKey.lean), is a member of the ledger.
 - carryOut_led, seamLed_ok: under MembersLed and KeysAre, CarryOut holds and the seam is in order.
 - ledOf c kp more x: the ledger: the keys' row, then the rows that the lookup puts out, then any
   further claims more x that the caller gives. layLed c kp n g more: the state map that lays it;
   it refuses if that is more than n claims. membersLed_lay, seamLed_lay_ok: MembersLed holds of
   layLed if the carried joint at g, together with the further claims more x, all holding, gives
   the caller's own back. So MembersLed can be met. The statement allows that what rides through
   the lookup is paid by claims of the ledger; no instance here uses it.
 - layLed_isSome: layLed does not refuse where 1 + the number of rows put out + the number of
   further claims is at most n. seamLed_self_ok: the two premises on the carried joint are met by
   the caller's own joint, by the identity; the further claims pay nothing there.
 - seamLed_dig5_ok: the same at a caller whose layout is digL5, the layout of the lookup on the
   digits: KeysAre is paid by keysAre_dig5.

Limits. A seam whose state map refuses says nothing there: n must be at least the ledger's length
at every statement that the lookup's block can put out, and by type the list of rows in such a
statement has any length. Johnson/Top/H/LookupCRows.lean has the seam along a state map that never
refuses, with the number of rows from the block's own joint. That the written row's block behind
the lookup begins at ledInA A0 n c.msg₀ with these arguments, and that its ledger is layLed's, is
said nowhere here. The claims' order in the ledger is ledOf's own; no statement here ties it to the
order in which the byte-level verifier adds its claims. KeysAre holds at the lookup on the digits
(keysAre_dig5, Johnson/Top/H/LookupSeamsKey.lean); at the lookups of the calls the keys are not
single entries: no theorem here says so.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupSeamsKey
import Cb.Pv.Att.BatchRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole Cb.Pv.Att

section
variable {E J : Type} [Field E] [Fintype J]

/-- A row on the entries and the place that is no cell, as a claim of a ledger on the entries. -/
def rowForm (r : Row E (Option J)) : Form E J := ⟨fun j => r.cf (some j), r.tg⟩

theorem rowForm_holds (r : Row E (Option J)) (ν : J → E) :
    (rowForm r).Holds ν ↔ r.Holds (zext ν) := by
  unfold Form.Holds Form.gap Row.Holds rowForm
  rw [Fintype.sum_option, sub_eq_zero]
  show _ ↔ r.cf none * 0 + ∑ j, r.cf (some j) * ν j = r.tg
  rw [mul_zero, zero_add]

end

section
variable (c : LookupCCaller) (kp : ℕ → ℕ → Option c.J₀) {K' P : Type}
  (A0 : IOR.Rels K' P c.Ex (c.Sg.Msg × c.Wp)) (n : ℕ)

/-- What the lookup puts out lies in the ledger. -/
structure MembersLed
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option (P × Ledger Cb.Gl.E c.J₀)) :
    Prop where
  on : ∀ x y s', c.R0.on (x.1.1, y) → f x = some s' → A0.on (s'.1, y) ∧ s'.2.length ≤ n
  rider : ∀ x y s' w, c.R0.on (x.1.1, y) → f x = some s' → A0.relR (s'.1, y) w →
    Ledger.Holds s'.2 (c.msg₀ w.1) → c.R0.relR (x.1.1, y) w
  rows : ∀ x s', f x = some s' → ∀ r ∈ x.2.2, rowForm r ∈ s'.2
  key : ∀ x s', f x = some s' → rowForm (keyRow c kp x) ∈ s'.2

theorem carryOut_led
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option (P × Ledger Cb.Gl.E c.J₀))
    (hL : KeysAre c.L kp) (h : MembersLed c kp A0 n f) :
    CarryOut c (ledInA A0 n c.msg₀) f :=
  carryOut_of c _ f h.on fun x y s' w ho hf hw =>
    ⟨h.rider x y s' w ho hf hw.1 hw.2,
      (keyRow_holds c kp hL x _).1 ((rowForm_holds _ _).1 (hw.2 _ (h.key x s' hf))),
      fun r hr => (rowForm_holds _ _).1 (hw.2 _ (h.rows x s' hf r hr))⟩

/-- The seam between the lookup and the draw that batches the ledger. -/
theorem seamLed_ok
    (f : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Option (P × Ledger Cb.Gl.E c.J₀))
    (hL : KeysAre c.L kp) (h : MembersLed c kp A0 n f) :
    (seamOut c (ledInA A0 n c.msg₀) f).OK :=
  seamOut_ok c _ f (carryOut_led c kp A0 n f hL h)

variable (g : c.St₀ × Cb.Gl.E → P)
  (more : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Ledger Cb.Gl.E c.J₀)

/-- The ledger: the keys' row, the rows put out, then the caller's further claims. -/
noncomputable def ledOf (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :
    Ledger Cb.Gl.E c.J₀ :=
  rowForm (keyRow c kp x) :: (x.2.2.map rowForm ++ more x)

/-- The map of states. It refuses a ledger of more than n claims. -/
noncomputable def layLed (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :
    Option (P × Ledger Cb.Gl.E c.J₀) :=
  if (ledOf c kp more x).length ≤ n then some (g x.1, ledOf c kp more x) else none

theorem layLed_some {x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)}
    {s' : P × Ledger Cb.Gl.E c.J₀} (hf : layLed c kp n g more x = some s') :
    (ledOf c kp more x).length ≤ n ∧ s' = (g x.1, ledOf c kp more x) := by
  unfold layLed at hf
  split at hf
  · exact ⟨‹_›, (Option.some.inj hf).symm⟩
  · exact absurd hf (by simp)

/-- It does not refuse a ledger of at most n claims. -/
theorem layLed_isSome (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (hn : 1 + x.2.2.length + (more x).length ≤ n) : (layLed c kp n g more x).isSome = true := by
  have hl : (ledOf c kp more x).length ≤ n := by
    unfold ledOf
    rw [List.length_cons, List.length_append, List.length_map]
    omega
  unfold layLed
  rw [if_pos hl]
  rfl

theorem membersLed_lay (hon : ∀ x y, c.R0.on (x.1, y) → A0.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1.1, y) → A0.relR (g x.1, y) w →
      Ledger.Holds (more x) (c.msg₀ w.1) → c.R0.relR (x.1.1, y) w) :
    MembersLed c kp A0 n (layLed c kp n g more) where
  on := fun x y s' ho hf => by
    obtain ⟨hl, rfl⟩ := layLed_some c kp n g more hf
    exact ⟨hon x.1 y ho, hl⟩
  rider := fun x y s' w ho hf hw hl => by
    obtain ⟨_, rfl⟩ := layLed_some c kp n g more hf
    exact hrd x y w ho hw fun fm hm =>
      hl _ (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
  rows := fun x s' hf r hr => by
    obtain ⟨_, rfl⟩ := layLed_some c kp n g more hf
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hr))
  key := fun x s' hf => by
    obtain ⟨_, rfl⟩ := layLed_some c kp n g more hf
    exact List.mem_cons_self

theorem seamLed_lay_ok (hL : KeysAre c.L kp)
    (hon : ∀ x y, c.R0.on (x.1, y) → A0.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1.1, y) → A0.relR (g x.1, y) w →
      Ledger.Holds (more x) (c.msg₀ w.1) → c.R0.relR (x.1.1, y) w) :
    (seamOut c (ledInA A0 n c.msg₀) (layLed c kp n g more)).OK :=
  seamLed_ok c kp A0 n _ hL (membersLed_lay c kp A0 n g more hon hrd)

/-- The two premises on the carried joint can be met: by the caller's own joint. -/
theorem seamLed_self_ok (hL : KeysAre c.L kp)
    (more : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Ledger Cb.Gl.E c.J₀) :
    (seamOut c (ledInA c.R0 n c.msg₀) (layLed c kp n Prod.fst more)).OK :=
  seamLed_lay_ok c kp c.R0 n Prod.fst more hL (fun _ _ h => h) fun _ _ _ _ h _ => h

end

section
open OnBytes OnBytes.Model OnBytes.DgP
variable (c : LookupCCaller) {K' P : Type} (A0 : IOR.Rels K' P c.Ex (c.Sg.Msg × c.Wp)) (n : ℕ)
  (g : c.St₀ × Cb.Gl.E → P)
  (more : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Ledger Cb.Gl.E c.J₀)

/-- At the layout digL5 of the lookup on the digits. -/
theorem seamLed_dig5_ok (tl : HTailF2) (en : Ent3 → c.J₀) (mk : ℕ → c.J₀) (jLK : ℕ)
    (hc : c.L = digL5 Cb.Gl.E tl en mk jLK c.St₀)
    (hon : ∀ x y, c.R0.on (x.1, y) → A0.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1.1, y) → A0.relR (g x.1, y) w →
      Ledger.Holds (more x) (c.msg₀ w.1) → c.R0.relR (x.1.1, y) w) :
    (seamOut c (ledInA A0 n c.msg₀) (layLed c (digKp tl en) n g more)).OK :=
  seamLed_lay_ok c (digKp tl en) A0 n g more (hc ▸ keysAre_dig5 tl en mk jLK c.St₀) hon hrd

end

#print axioms VerifiableInference.OnPublicFiles.layLed_isSome
#print axioms VerifiableInference.OnPublicFiles.seamLed_self_ok
#print axioms VerifiableInference.OnPublicFiles.seamLed_dig5_ok
#print axioms VerifiableInference.OnPublicFiles.rowForm_holds
#print axioms VerifiableInference.OnPublicFiles.seamLed_ok
#print axioms VerifiableInference.OnPublicFiles.seamLed_lay_ok

end VerifiableInference.OnPublicFiles
