-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PlStd.lean: where all own mask entries of a lookup with parts stand, as a function
of the
public record and of two numberings of mask entries: a value of the record `Pl`.

The record `Pl A` (Cb/Pv/KeyLookup/Lam1.lean) names the places of the lookup's own mask entries as
letters.
Here it gets a value, by this rule (a definition: that the program takes its entries so is not
claimed here). The sumchecks take their entries one behind the other, in the order of the chain:
the tie's steps, the parts' steps, the key levels part by part, the table's levels, the closing, the
bits. A sumcheck takes: for each round of a variable, in the order of the rounds, the coefficients
of
the powers from the first upward; in the last round the constant first; then one entry for each
shown
value. The two shown values of the last level of part i are the entries 2 i and 2 i + 1 of the
second
numbering.

It imports Cb/Pv/KeyLookup/Lam1Short.lean, Cb/Pv/KeyLookup/PartsStd.lean,
Cb/Pv/KeyLookup/LevStd.lean; no file of the
port.

  `pNum l i`      the number of the name i among the coefficients of a hiding polynomial with the
                  variables l.
  `Pub.bParts`, `bKeys`, `bTable`, `bClo`, `bBits`, `ownMasks`   where each stretch's entries begin
                    in the first
                  numbering, and how many there are in all: functions of the public record.
  `TiePl.std`, `ClPl.std`   the tie's and the closing stretches' places.
  `Pl.std A ms ix`   THE VALUE: ms and ix number the mask entries.
  `Pl.std_in`     if every entry that ms and ix name, and every cell of a live plane, lies in G,
                  then
                  `(Pl.std A ms ix).In G`.
Not claimed: that the places are apart; that this is the order in which the program takes its
entries (no test of it is in this library).

-/
import Cb.Pv.KeyLookup.Lam1Short
import Cb.Pv.KeyLookup.PartsStd
import Cb.Pv.KeyLookup.LevStd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E]

/-- The number of a name among the coefficients: by round, powers upward; in the last round the
constant first. -/
def pNum : (l : List (PFmt E)) → PIdx l → ℕ
  | [], _ => 0
  | [f], i =>
    match (i : Fin f.n ⊕ Unit) with
    | .inr _ => 0
    | .inl t => 1 + t.val
  | f :: g :: l, i =>
    match (i : Fin f.n ⊕ PIdx (g :: l)) with
    | .inl t => t.val
    | .inr n => f.n + pNum (g :: l) n

end

namespace Pub
variable (S : Pub)

/-- the first entry of the parts' steps -/
def bParts : ℕ := 7 + 6 * (S.pl - 2)
/-- of the key levels -/
def bKeys : ℕ := S.bParts + 5 * (S.m - 1)
/-- of the table's levels -/
def bTable : ℕ := S.bKeys + Lev.partSum S S.m
/-- of the closing -/
def bClo : ℕ := S.bTable + Lev.grp S.mu S.d
/-- of the bits' test -/
def bBits : ℕ := S.bClo + (1 + S.mu + 2 * S.d)
/-- The number of entries of the first numbering. -/
def ownMasks : ℕ := S.bBits + (2 * (S.mu + S.d) + 4)

end Pub

variable {E : Type} [Field E] [Fintype E]

/-- The first entry of the tie's step l. -/
def tieBase (l : ℕ) : ℕ := if l = 0 then 0 else 7 + 6 * (l - 1)

/-- The tie's places. -/
def TiePl.std {J : Type} (ms : ℕ → J) : TiePl E J where
  wAt := fun l i =>
    match (i : Fin 3 ⊕ Unit) with
    | .inr _ => ms (tieBase l)
    | .inl t => ms (tieBase l + 1 + t.val)
  cZ := ms 4
  cAt := fun l b =>
    if l = 0 then ms (if b then 6 else 5) else ms (tieBase l + (if b then 5 else 4))

/-- The places of the closing and of the bits' test. -/
def ClPl.std (A : Dat E) (ms : ℕ → A.J) : ClPl A where
  wE := fun i => ms (A.bClo + pNum _ i)
  wB := fun i => ms (A.bBits + Lev.offW (A.mu + A.d) i)
  cB := ms (A.bBits + (2 * (A.mu + A.d) + 3))

/-- All places. -/
def Pl.std (A : Dat E) (ms ix : ℕ → A.J) : Pl A where
  tie := TiePl.std ms
  wP  := Parts.wStd ms A.bParts
  cP  := Parts.cStd ms A.bParts
  lev := LevPl.std A ms ix A.bKeys 0 A.bTable
  cl  := ClPl.std A ms

theorem Pl.std_in (A : Dat E) (ms ix : ℕ → A.J) (G : A.J → Prop) (hm : ∀ k, G (ms k))
    (hx : ∀ k, G (ix k)) (hc : ∀ u j, j < A.pl → G (A.bAt u j)) : (Pl.std A ms ix).In G where
  cells := hc
  tie := ⟨fun l i => by
      rcases (i : Fin 3 ⊕ Unit) with t | _
      · exact hm _
      · exact hm _, hm _, fun l b => by
      show G (if l = 0 then _ else _)
      split
      · exact hm _
      · exact hm _⟩
  wP := fun l i => by
    rcases (i : Fin 2 ⊕ Unit) with t | _
    · exact hm _
    · exact hm _
  cP := fun _ _ => hm _
  lev := ⟨fun _ _ _ => hm _, fun i l b => by
      show G (if l + 1 = A.v i then _ else _)
      split
      · exact hx _
      · exact hm _, fun _ _ => hm _, fun _ _ => hm _⟩
  cl := ⟨fun u _ j hj => hc u j hj, fun _ => hm _, fun _ => hm _, hm _⟩

end Lk6

#print axioms Lk6.Pl.std_in
