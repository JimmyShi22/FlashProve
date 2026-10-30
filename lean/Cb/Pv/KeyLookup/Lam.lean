-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Lam.lean: the list Λ of a lookup with parts: round by round, what is sent, how many
values the draw has,
and the count of bad values.

It imports Cb/Pv/KeyLookup/Letters.lean alone (no file of the port).

`Lam q S` is a computable list, a function of the public record S (of its parts, d, mu, pl alone)
    and of q, the
number of elements of the field. A row: the round's kind; how many scalars the prover sends in it;
n, the number of
values of the verifier's draw (1: no draw); c, the count of bad values among them. The order is the
order of the ten
stretches: draw · fused tie · the parts' steps · join point · the key sides · table · closing · zero
point · bits.
The read-out has no round. The list is the eight stretches' shares in a row (`lamHead` … `lamBits`).

A sumcheck's rows (`psc`): ε (1 scalar; q; 1) · for each variable whose round polynomial has a
degree below g:
(g scalars; q; g - 1) · if there is a further variable Y of degree dY: (dY + 1 scalars; q - 1; dY)
and the end values
(no draw). SCALARS ARE COUNTED AS THE LIBRARY's SUMCHECK SENDS THEM: ALL coefficients. The port does
not send the one
coefficient that the verifier's check fixes: `short` turns a row into the port's count (one less in
each round with a
polynomial).

Main names: `Kind`, `LRow`, `psc`, `tree`, `lamHead` … `lamBits`, `Lam`, `LRow.short`, `rounds` (a
closed formula), `lam_length` (under 2 ≤ pl the
list has `rounds S` rows), `pub119` (a small public record, for tests).
Not claimed here: that the chain's shape and errors are this list (that is the assembly's theorem);
anything on the
port's plan (a file of its own).

-/
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6

/-- The kinds of rounds. -/
inductive Kind
  | lkp | eps | var | y | vals | join | line | zero
  deriving DecidableEq, Repr

/-- A row of the list. -/
structure LRow where
  kind : Kind
  /-- scalars that the prover sends in the round -/
  sent : ℕ
  /-- the number of values of the draw; 1: there is none -/
  n : ℕ
  /-- the count of bad values -/
  c : ℕ
  deriving DecidableEq, Repr

/-- One coefficient less in a round with a polynomial. -/
def LRow.short (r : LRow) : LRow :=
  match r.kind with
  | .var | .y => { r with sent := r.sent - 1 }
  | _ => r

/-- A sumcheck: the bounds on the variables' degrees; Y's degree and the number of end values, if
there is a Y. -/
def psc (q : ℕ) (deg : List ℕ) (y : Option (ℕ × ℕ)) : List LRow :=
  ⟨.eps, 1, q, 1⟩ :: deg.map (fun g => ⟨.var, g, q, g - 1⟩) ++
    match y with
    | none => []
    | some (dY, vals) => [⟨.y, dY + 1, q - 1, dY⟩, ⟨.vals, vals, 1, 0⟩]

/-- The levels l = 0, …, levels - 1 of a product tree: a sumcheck in more + l variables, two values,
a line's draw. -/
def tree (q more levels : ℕ) : List LRow :=
  (List.range levels).flatMap fun l =>
    psc q (List.replicate (more + l) 3) (some (2, 2)) ++ [⟨.line, 0, q, 1⟩]

/-! the shares of the eight stretches that have rounds -/
def lamHead (q : ℕ) (S : Pub) : List LRow :=
  [⟨.lkp, 0, q, S.allKeys - 1⟩] ++ psc q [] (some (3, 3)) ++
    (List.range (S.pl - 2)).flatMap fun _ => psc q [] (some (3, 2))
def lamParts (q : ℕ) (S : Pub) : List LRow :=
  (List.range (S.m - 1)).flatMap fun _ => psc q [] (some (2, 2))
def lamJoin (q : ℕ) (S : Pub) : List LRow := [⟨.join, 0, q ^ S.mu, S.mu * q ^ (S.mu - 1)⟩]
def lamKeys (q : ℕ) (S : Pub) : List LRow := S.parts.flatMap fun v => tree q 0 v
def lamTable (q : ℕ) (S : Pub) : List LRow := tree q S.mu S.d
def lamClo (q : ℕ) (S : Pub) : List LRow :=
  psc q (List.replicate S.d 3 ++ List.replicate S.mu 2) none
def lamZero (q : ℕ) (S : Pub) : List LRow :=
  [⟨.zero, 0, q ^ (S.mu + S.d), (S.mu + S.d) * q ^ (S.mu + S.d - 1)⟩]
def lamBits (q : ℕ) (S : Pub) : List LRow := psc q (List.replicate (S.mu + S.d) 3) (some (2, 1))

/-- The list: the shares in the order of the stretches, bracketed as the chain is. -/
def Lam (q : ℕ) (S : Pub) : List LRow :=
  ((((((lamHead q S ++ lamParts q S) ++ lamJoin q S) ++ lamKeys q S) ++ lamTable q S) ++ lamClo q S)
      ++
    lamZero q S) ++ lamBits q S

/-- The number of rounds, as a closed formula. -/
def rounds (S : Pub) : ℕ :=
  1 + 3 * (S.pl - 1) + 3 * (S.m - 1) + 1 + (S.parts.map fun v => ((List.range v).map fun l => l +
      4).sum).sum +
    ((List.range S.d).map fun l => S.mu + l + 4).sum + (1 + S.d + S.mu) + 1 + (S.mu + S.d + 3)

theorem psc_length_y (q : ℕ) (deg : List ℕ) (y : ℕ × ℕ) : (psc q deg (some y)).length = deg.length +
    3 := by
  simp [psc]

theorem psc_length_none (q : ℕ) (deg : List ℕ) : (psc q deg none).length = deg.length + 1 := by
  simp [psc]

theorem tree_length (q more levels : ℕ) :
    (tree q more levels).length = ((List.range levels).map fun l => more + l + 4).sum := by
  simp [tree, List.length_flatMap, psc_length_y, Function.comp_def]
  omega

theorem const_length {α : Type} (n : ℕ) (l : List α) :
    ((List.range n).flatMap fun _ => l).length = n * l.length := by
  simp [List.length_flatMap, Function.comp_def]

theorem const_sum (n k : ℕ) : ((List.range n).map fun _ => k).sum = n * k := by
  simp

/-- The list has as many rows as the closed formula says. -/
theorem lam_length (q : ℕ) (S : Pub) (hp : 2 ≤ S.pl) : (Lam q S).length = rounds S := by
  simp only [Lam, lamHead, lamParts, lamJoin, lamKeys, lamTable, lamClo, lamZero, lamBits, rounds,
    List.length_append, List.length_cons, List.length_nil, const_length, psc_length_y,
        psc_length_none,
    tree_length, List.length_flatMap, List.length_replicate, Function.comp_def, Nat.zero_add,
        const_sum]
  omega

/-- A small public record, for tests: three parts of 16 keys, four rows, six live planes of eight;
its list has 119 rows. -/
def pub119 : Pub :=
  { parts := [4, 4, 4], d := 2, mu := 3, pl := 6, runs := [⟨2, 12, 0, 4⟩], padRow := 1, order := [1]
      }

end Lk6

#print axioms Lk6.lam_length
