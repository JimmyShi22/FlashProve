-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/RoundIs.lean: what it means that a typed round of the library is the round of a plan's
entry, as far as a typed round can say it.

For rounds that send an oracle or draw values of more than one kind use OnBytes/G4/RoundIsAll.lean.

Where the text of part 1 comes from, and what is to be said with it, is in a paper
[not in this library].

Why. A round of the library (Iop.Round, Iop/Shape.lean) holds types: no function computes a number
or a name from it. A plan's entry (Fmt.Entry, Fmt/Plan.lean) is a name and eleven numbers. To say
that a typed protocol has the rounds of a plan, a list of entries is laid beside its shape and tied
to it.

THE STATEMENT TO USE. That a shape has the rounds of a list of entries is `ShapeIs Cb.Gl.E shape
ds`, and no other: with ds a list of entries (Fmt.Entry) and the challenge field Cb.Gl.E. RoundIs
takes a field and three numbers (RSh) as letters; whoever states it over a list of RSh of its own,
with a map of its own to the entries, or over another field, has made a second definition.

Part 1. `RSh`: the three numbers of an entry that a typed round can bear: scalars (the message's
bytes divided by 24), drawE, drawNZ. `drawT E n nz`: the set drawn from: nz = 0: n elements of E; n
= nz = 1: one element that is not 0; every other pair: the empty type. `RoundIs E r s`: the round's
plain part is, up to a bijection, s.scalars elements of E; its challenges are, up to a bijection,
drawT E s.drawE s.drawNZ; it has no oracle position. One round bears one number of scalars (over a
finite E with two elements or more) and one pair (drawE, drawNZ) (more than two elements).
Part 2. `EntryIs E r e`: RoundIs at the three numbers of an entry: msg = 24 times the scalars,
drawE, drawNZ. `ShapeIs E s ds`: the same of a list of rounds and a list of entries, one by one. An
entry in which one of the three numbers is changed is refuted (`EntryIs.not_of_msg_ne` and its two
fellows). The size of the challenge set (`RoundIs.card_chal`, `EntryIs.card_chal`). That the
definition is met: `bareRound`, `bareRoundNZ`.
Part 3. The same laws at the challenge field Cb.Gl.E, without a premise on its size.

What it lets through. IT COUNTS: two sizes, three equations, and no oracle position.
 - "There is a bijection" pins the size of a message, not which scalar is which: a round whose plain
   part is any type of q^k elements is k scalars, and the bijection is chosen nowhere. So the order
   of the scalars inside a message is tied by nothing here.
 - The same of the challenges: a set of as many elements as there are elements that are not 0 (the
   elements that are not 1, say) passes at drawNZ = 1.
 - The oracle part itself. "No oracle position" is not "no oracle part": a round with Orc := Fin 5 →
   E and Pos := Empty passes, and msg does not count these five elements. By its type a verifier's
   function on whole transcripts can read them; what forbids it is that the reduction is local
   (IOR.IsLocal, Ior/Ior.lean), which is asked elsewhere, not here.
 - The name and the other eight numbers of an entry (count, work, roots, answers, poss, logN, trits,
   rows).

Where the reading is the format's. In the format the roots of a message are among its bytes, 32
each, and a round may also draw positions or matrix entries. So "msg = 24 times the scalars" and
"the challenge is drawE elements" are the format's reading only of an entry with roots = 0, poss = 0
and trits = 0, and with drawNZ = 0 or drawE = drawNZ = 1. At every other pair (drawE, drawNZ), such
as a round of seeds, drawT is empty, and since every round has a challenge NO round is EntryIs of
such an entry: it errs by refusing. All 65 entries of the lookup for which this file was made meet
the four conditions.

Main definitions: RSh, drawT, RoundIs, RSh.IsOf, EntryIs, ShapeIs, bareRound, bareRoundNZ.
Main theorems: RoundIs.scalars_eq, RoundIs.draw_eq, RoundIs.card_chal, EntryIs.unique,
EntryIs.not_of_msg_ne, EntryIs.not_of_drawE_ne, EntryIs.not_of_drawNZ_ne, EntryIs.card_chal,
roundIs_bareRound, roundIs_bareRoundNZ, two_lt_card_gl, EntryIs.unique_gl.
Not claimed. Nothing on any protocol.

-/
import Iop.Shape
import Cb.Gl.GlField
import Fmt.Plan
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Forall2
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.G4
open Iop

/-! ## Part 1 -/

/-- what a typed round can bear of a plan's entry -/
structure RSh where
  scalars : ℕ
  drawE : ℕ
  drawNZ : ℕ
  deriving DecidableEq, Repr

/-- the set drawn from -/
def drawT (E : Type) [Zero E] (n nz : ℕ) : Type :=
  match nz with
  | 0 => Fin n → E
  | 1 =>
    match n with
    | 1 => {x : E // x ≠ 0}
    | _ => Empty
  | _ => Empty

/-- The round r sends s.scalars elements of E, draws from drawT E s.drawE s.drawNZ, each up to a
bijection, and has no oracle position. -/
def RoundIs (E : Type) [Zero E] (r : Round) (s : RSh) : Prop :=
  Nonempty (r.Plain ≃ (Fin s.scalars → E)) ∧ Nonempty (r.Chal ≃ drawT E s.drawE s.drawNZ) ∧
    IsEmpty r.Pos

section
variable {E : Type} [Zero E] [Finite E]

omit [Zero E] [Finite E] in
theorem card_fun (n : ℕ) : Nat.card (Fin n → E) = Nat.card E ^ n := by
  rw [Nat.card_fun, Nat.card_fin]

theorem card_nz : Nat.card {x : E // x ≠ 0} = Nat.card E - 1 := by
  classical
  haveI := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq (0 : E)

/-- the size of the set drawn from -/
theorem card_drawT (n nz : ℕ) : Nat.card (drawT E n nz) =
    if nz = 0 then Nat.card E ^ n else if nz = 1 ∧ n = 1 then Nat.card E - 1 else 0 := by
  rcases nz with _ | _ | nz
  · exact card_fun n
  · rcases n with _ | _ | n
    · exact Nat.card_of_isEmpty (α := Empty)
    · exact card_nz
    · show Nat.card Empty = _
      simp
  · show Nat.card Empty = _
    simp

omit [Finite E] in
theorem RoundIs.scalars_eq (hq : 2 ≤ Nat.card E) {r : Round} {s s' : RSh} (h : RoundIs E r s)
    (h' : RoundIs E r s') : s.scalars = s'.scalars := by
  obtain ⟨e⟩ := h.1
  obtain ⟨e'⟩ := h'.1
  have hc := Nat.card_congr (e.symm.trans e')
  rw [card_fun, card_fun] at hc
  exact Nat.pow_right_injective hq hc

theorem RoundIs.draw_eq (hq : 2 < Nat.card E) {r : Round} [Nonempty r.Chal] {s s' : RSh}
    (h : RoundIs E r s) (h' : RoundIs E r s') : s.drawE = s'.drawE ∧ s.drawNZ = s'.drawNZ := by
  obtain ⟨e⟩ := h.2.1
  obtain ⟨e'⟩ := h'.2.1
  have hc := Nat.card_congr (e.symm.trans e')
  have fin : ∀ n nz, Finite (drawT E n nz) := by
    intro n nz
    rcases nz with _ | _ | nz
    · exact inferInstanceAs (Finite (Fin n → E))
    · rcases n with _ | _ | n
      · exact inferInstanceAs (Finite Empty)
      · exact inferInstanceAs (Finite {x : E // x ≠ 0})
      · exact inferInstanceAs (Finite Empty)
    · exact inferInstanceAs (Finite Empty)
  have pos : ∀ t : RSh, Nonempty (r.Chal ≃ drawT E t.drawE t.drawNZ) →
      0 < Nat.card (drawT E t.drawE t.drawNZ) := by
    rintro t ⟨f⟩
    haveI := fin t.drawE t.drawNZ
    haveI : Nonempty (drawT E t.drawE t.drawNZ) := ⟨f (Classical.arbitrary _)⟩
    exact Nat.card_pos
  have p1 := pos s h.2.1
  have p2 := pos s' h'.2.1
  rw [card_drawT] at hc p1
  rw [card_drawT] at hc p2
  have big : ∀ n : ℕ, Nat.card E ^ n ≠ Nat.card E - 1 := by
    intro n hn
    rcases n with _ | n
    · simp at hn
      omega
    · have : Nat.card E ≤ Nat.card E ^ (n + 1) := Nat.le_self_pow (by omega) _
      omega
  by_cases a : s.drawNZ = 0 <;> by_cases b : s'.drawNZ = 0
  · rw [if_pos a, if_pos b] at hc
    exact ⟨Nat.pow_right_injective (by omega) hc, a.trans b.symm⟩
  · rw [if_pos a, if_neg b] at hc
    rw [if_neg b] at p2
    split at hc
    · exact absurd hc (big _)
    · rename_i hb
      rw [if_neg hb] at p2
      exact absurd p2 (lt_irrefl 0)
  · rw [if_neg a, if_pos b] at hc
    rw [if_neg a] at p1
    split at hc
    · exact absurd hc.symm (big _)
    · rename_i ha
      rw [if_neg ha] at p1
      exact absurd p1 (lt_irrefl 0)
  · rw [if_neg a] at p1
    rw [if_neg b] at p2
    by_cases ha : s.drawNZ = 1 ∧ s.drawE = 1
    · by_cases hb : s'.drawNZ = 1 ∧ s'.drawE = 1
      · exact ⟨ha.2.trans hb.2.symm, ha.1.trans hb.1.symm⟩
      · rw [if_neg hb] at p2
        exact absurd p2 (lt_irrefl 0)
    · rw [if_neg ha] at p1
      exact absurd p1 (lt_irrefl 0)

end

/-! ## Part 2: entries, lists, and that it is met -/

section
variable {E : Type} [Zero E]

/-- The three numbers are those of the entry. -/
def RSh.IsOf (s : RSh) (e : Fmt.Entry) : Prop :=
  e.msg = 24 * s.scalars ∧ e.drawE = s.drawE ∧ e.drawNZ = s.drawNZ

variable (E) in
/-- The round sends and draws what the entry says, in the three numbers that a typed round can
bear. -/
def EntryIs (r : Round) (e : Fmt.Entry) : Prop := ∃ s : RSh, RoundIs E r s ∧ s.IsOf e

variable (E) in
/-- The rounds of a shape are the rounds of the entries, one by one. -/
def ShapeIs (s : Shape) (ds : List Fmt.Entry) : Prop := List.Forall₂ (EntryIs E) s ds

variable [Finite E]

/-- The size of the challenge set. -/
theorem RoundIs.card_chal {r : Round} {s : RSh} (h : RoundIs E r s) :
    Nat.card r.Chal =
      if s.drawNZ = 0 then Nat.card E ^ s.drawE
      else if s.drawNZ = 1 ∧ s.drawE = 1 then Nat.card E - 1 else 0 := by
  obtain ⟨e⟩ := h.2.1
  rw [Nat.card_congr e, card_drawT]

/-- The three numbers that EntryIs ties are determined by the round. -/
theorem EntryIs.unique (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry} (h : EntryIs E r e)
    (h' : EntryIs E r e') : e.msg = e'.msg ∧ e.drawE = e'.drawE ∧ e.drawNZ = e'.drawNZ := by
  obtain ⟨s, hs, h1, h2, h3⟩ := h
  obtain ⟨s', hs', h1', h2', h3'⟩ := h'
  have a := hs.scalars_eq (by omega) hs'
  obtain ⟨b, c⟩ := hs.draw_eq hq hs'
  exact ⟨by rw [h1, h1', a], by rw [h2, h2', b], by rw [h3, h3', c]⟩

/-- An entry with another number of bytes is refuted. -/
theorem EntryIs.not_of_msg_ne (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIs E r e) (hne : e'.msg ≠ e.msg) : ¬ EntryIs E r e' :=
  fun h' => hne (h'.unique hq h).1

/-- An entry with another number of elements drawn is refuted. -/
theorem EntryIs.not_of_drawE_ne (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIs E r e) (hne : e'.drawE ≠ e.drawE) : ¬ EntryIs E r e' :=
  fun h' => hne (h'.unique hq h).2.1

/-- An entry with another number of elements that are not 0 is refuted. -/
theorem EntryIs.not_of_drawNZ_ne (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIs E r e) (hne : e'.drawNZ ≠ e.drawNZ) : ¬ EntryIs E r e' :=
  fun h' => hne (h'.unique hq h).2.2

/-- The size of the challenge set, in the entry's own numbers. -/
theorem EntryIs.card_chal {r : Round} {e : Fmt.Entry} (h : EntryIs E r e) :
    Nat.card r.Chal =
      if e.drawNZ = 0 then Nat.card E ^ e.drawE
      else if e.drawNZ = 1 ∧ e.drawE = 1 then Nat.card E - 1 else 0 := by
  obtain ⟨s, hs, _, h2, h3⟩ := h
  rw [h2, h3]
  exact hs.card_chal

end

section
variable (E : Type) [Zero E] [Fintype E]

/-- The round without an oracle part that sends k elements and draws n elements. -/
def bareRound (k n : ℕ) : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Fin k → E
  Chal := Fin n → E
  dOrc := ()
  dPlain := fun _ => 0
  finChalT := fun _ => by classical exact inferInstance
  neChal := ⟨fun _ => 0⟩

theorem roundIs_bareRound (k n : ℕ) : RoundIs E (bareRound E k n) ⟨k, n, 0⟩ :=
  ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty)⟩

/-- The round without an oracle part that sends k elements and draws one element that is not 0. one:
an element that is not 0. -/
noncomputable def bareRoundNZ (k : ℕ) (one : {x : E // x ≠ 0}) : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Fin k → E
  Chal := {x : E // x ≠ 0}
  dOrc := ()
  dPlain := fun _ => 0
  finChalT := fun _ => by classical exact inferInstance
  neChal := ⟨one⟩

theorem roundIs_bareRoundNZ (k : ℕ) (one : {x : E // x ≠ 0}) :
    RoundIs E (bareRoundNZ E k one) ⟨k, 1, 1⟩ :=
  ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty)⟩

end

/-! ## Part 3: at the challenge field -/

/-- The challenge field has more than two elements. -/
theorem two_lt_card_gl : 2 < Nat.card Cb.Gl.E := by
  rw [Nat.card_eq_fintype_card, Cb.Gl.gl_card.2.1]
  exact lt_trans (by norm_num) Cb.Gl.gl_card.2.2.1

/-- At the challenge field the three numbers are determined by the round. -/
theorem EntryIs.unique_gl {r : Round} {e e' : Fmt.Entry} (h : EntryIs Cb.Gl.E r e)
    (h' : EntryIs Cb.Gl.E r e') : e.msg = e'.msg ∧ e.drawE = e'.drawE ∧ e.drawNZ = e'.drawNZ :=
  h.unique two_lt_card_gl h'

end OnBytes.G4

#print axioms OnBytes.G4.RoundIs.scalars_eq
#print axioms OnBytes.G4.RoundIs.draw_eq
#print axioms OnBytes.G4.RoundIs.card_chal
#print axioms OnBytes.G4.EntryIs.card_chal
#print axioms OnBytes.G4.EntryIs.unique_gl
#print axioms OnBytes.G4.roundIs_bareRound
#print axioms OnBytes.G4.roundIs_bareRoundNZ
