-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/NzRead.lean: what the strict reader's rounds have drawn: each round of a chain
that was read has drawn what the format's rule gives at the round's entry and kind; and at an entry
all of whose elements are drawn by the rule that never gives 0, each drawn triple has words below
the prime and is not the triple of zeros.

Definitions, statements and proofs, on Fmt/Rules6.lean, Fmt/Rules6Round.lean and Fmt/Rules8X.lean.
Main names:
  `DrawnAt f r ro`: the round ro as it was read has drawn `drawRound f r.entry r.kind` of some row
    of words.
  `roundX_out`, `foldRoundsX_out`, `readChainX_out`: the reader's step, its fold, and the reader:
    the rounds that were read stand one by one against the description's rounds, with `DrawnAt`.
  `GoodNZ x`: the triple's words are below the prime of the second field, and it is not the triple
    of zeros.
  `drawNZ_good`, `drawElems_good`, `drawRound_good`: at an entry with drawNZ = drawE every drawn
    element is `GoodNZ`.
Limits: the second field alone. Nothing on how the words are distributed, or on any hash function.
-/
import Fmt.FieldE
import Fmt.Rules8X
import Mathlib.Data.List.Forall2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Nz

open Fmt

/-- The round as it was read has drawn what the format's rule gives at the round's entry and
kind. -/
def DrawnAt (f : Fld) (r : Round) (ro : RoundOut) : Prop :=
  ∃ row, ro.drawn = drawRound f r.entry r.kind row

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- One step of the reader. -/
theorem roundX_out (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s s' : St)
    (r : Round) (ts : List Stored)
    (e : roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro, s'.out = s.out.push ro ∧ DrawnAt P.field r ro := by
  unfold roundX at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e
      · cases e
      · simp only [idBind] at e
        split at e
        · cases e
        · rename_i c vb hq
          split at e
          · cases e
          · split at e
            · cases e
            · split at e
              · cases e
              · cases e
                exact ⟨_, rfl, _, rfl⟩

/-- The reader's fold. -/
theorem foldRoundsX_out (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s s' : St),
      foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
      ∃ outs : List RoundOut, s'.out.toList = s.out.toList ++ outs ∧
        List.Forall₂ (fun (r : Round × List Stored) ro => DrawnAt P.field r.1 ro) rs outs
  | [], s, s', e => by
    cases e
    exact ⟨[], by simp, List.Forall₂.nil⟩
  | r :: rs, s, s', e => by
    simp only [foldRoundsX, idBind] at e
    cases hst : roundX (m := Id) h cfg statement P run b s r.1 r.2 with
    | none => simp [hst] at e
    | some s1 =>
      simp only [hst] at e
      obtain ⟨ro, e1, d1⟩ := roundX_out h cfg statement P run b s s1 r.1 r.2 hst
      obtain ⟨outs, e2, d2⟩ := foldRoundsX_out h cfg statement P run b rs s1 s' e
      exact ⟨ro :: outs, by rw [e2, e1]; simp, List.Forall₂.cons d1 d2⟩

/-- The reader: the rounds that were read stand one by one against the description's rounds; the
description has passed the reader's own test. -/
theorem readChainX_out (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : SpecX)
    (seen : Seen) (b : ByteArray) (i : Nat) (o : ChainOut) (j : Nat)
    (e : readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧
      List.Forall₂ (fun (r : Round × List Stored) ro => DrawnAt S.base.plan.field r.1 ro)
        (S.base.rounds.zip S.stored) o.rounds.toList := by
  unfold readChainX at e
  split at e
  · cases e
  · rename_i hok
    refine ⟨by simpa using hok, ?_⟩
    dsimp only at e
    split at e
    · cases e
    · simp only [idBind] at e
      split at e
      · cases e
      · split at e
        · cases e
        · rename_i s hs
          obtain ⟨outs, e1, d⟩ := foldRoundsX_out h _ _ _ _ b _ _ s hs
          cases e
          have e2 : s.out.toList = outs := by simpa using e1
          rw [e2]
          exact d

/-! ## What the rule that never gives 0 gives -/

/-- The words are below the prime of the second field, and the triple is not the triple of zeros. -/
def GoodNZ (x : Ext) : Prop := Fld.two.okE x = true ∧ x ≠ Fld.zeroE

theorem drawFN_ok (row : Row) : ∀ (n c : Nat), Fld.two.ok (drawFN .two n row c).1 = true
  | 0, _ => by
    show Fld.two.ok (0 : UInt64) = true
    decide
  | n + 1, c => by
    unfold drawFN Dr.bind Dr.word
    dsimp only
    cases hw : Fld.two.tryWord (row c) with
    | none => exact drawFN_ok row n (c + 1)
    | some x =>
      have hw' : (if (row c).toNat < Fld.two.p then some (row c) else none) = some x := hw
      split at hw'
      · rename_i hlt
        cases hw'
        show Fld.two.ok (row c) = true
        unfold Fld.ok
        exact decide_eq_true hlt
      · cases hw'

theorem drawE_ok (row : Row) (c : Nat) : Fld.two.okE (drawE .two row c).1 = true := by
  unfold drawE Dr.bind Dr.pure Fld.okE drawF
  simp only [drawFN_ok, Bool.and_self]

theorem drawNZ_eq (row : Row) (c : Nat) : (drawNZ .two row c).1 =
    if (drawE .two row c).1 = (0, 0, 0) then
      (if (drawE .two row (drawE .two row c).2).1 = (0, 0, 0) then (1, 0, 0)
        else (drawE .two row (drawE .two row c).2).1)
    else (drawE .two row c).1 := by
  unfold drawNZ Dr.bind
  dsimp only
  split <;> rfl

theorem drawNZ_good (row : Row) (c : Nat) : GoodNZ (drawNZ .two row c).1 := by
  rw [drawNZ_eq]
  split
  · split
    · exact ⟨by decide, by decide⟩
    · rename_i h2
      exact ⟨drawE_ok row _, h2⟩
  · rename_i h1
    exact ⟨drawE_ok row c, h1⟩

/-- What holds of every value of a draw holds of every member of the draw, n times. -/
theorem times_each {α : Type} (x : Dr α) (P : α → Prop) (row : Row) (h : ∀ c, P (x row c).1) :
    ∀ (n c : Nat), ∀ a ∈ ((x.times n) row c).1, P a
  | 0, _, a, ha => absurd ha (List.not_mem_nil)
  | n + 1, c, a, ha => by
    have ha' : a ∈ (x row c).1 :: ((x.times n) row (x row c).2).1 := ha
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h c
    · exact times_each x P row h n _ a ha'

/-- At an entry all of whose elements are drawn by the rule that never gives 0. -/
theorem drawElems_good (e : Entry) (k : Kind) (he : e.drawNZ = e.drawE) (row : Row) (c : Nat) :
    ∀ x ∈ (drawElems .two e k row c).1, GoodNZ x := by
  have h0 : e.drawE - e.drawNZ = 0 := by omega
  unfold drawElems
  rw [h0, Nat.zero_div, Nat.zero_mod]
  split
  · intro x hx
    have hx' : x ∈ (((drawSeedL .two 0).times e.drawNZ) row c).1.flatten ++ [] := hx
    rw [List.append_nil] at hx'
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx'
    have hP := times_each (drawSeedL .two 0) (fun l => ∀ y ∈ l, GoodNZ y) row (fun c' y hy => by
      have hy' : y ∈ [] ++ [(drawNZ .two row c').1] := hy
      rw [List.nil_append, List.mem_singleton] at hy'
      rw [hy']
      exact drawNZ_good row c') e.drawNZ c l hl
    exact hP x hxl
  · intro x hx
    have hx' : x ∈ [] ++ (((drawNZ .two).times e.drawNZ) row c).1 := hx
    rw [List.nil_append] at hx'
    exact times_each (drawNZ .two) GoodNZ row (drawNZ_good row) e.drawNZ c x hx'

theorem drawRound_good (e : Entry) (k : Kind) (he : e.drawNZ = e.drawE) (row : Row) :
    ∀ x ∈ (drawRound .two e k row).elems, GoodNZ x :=
  drawElems_good e k he row _

end OnBytes.Tie.Pv.Keeps.Nz

#print axioms OnBytes.Tie.Pv.Keeps.Nz.readChainX_out
#print axioms OnBytes.Tie.Pv.Keeps.Nz.drawNZ_good
#print axioms OnBytes.Tie.Pv.Keeps.Nz.drawRound_good
#print axioms OnBytes.Tie.Pv.Keeps.Nz.roundX_out
#print axioms OnBytes.Tie.Pv.Keeps.Nz.foldRoundsX_out
