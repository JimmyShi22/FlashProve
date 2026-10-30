-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Lists/TwErr.lean.
The errors of a lookup's rounds as lists of numbers.

Definitions alone; the file proves nothing. Computable, and general in four sizes: 2^(v'+1) keys,
2^d rows of the table, 2^w slots for planes of bits, n + 2 planes that count. q: the field's size.
Main definitions. epsN v' d w n q: for each round the number c of bad challenges (0 where nothing is
drawn). nN: the size n of the round's challenge set (1 where nothing is drawn). ratN: the quotient
of the planner (OnBytes/Params/Planner.lean) as a pair (a, kind): kind 1: a of q; kind 2: a of
q - 1; kind 0: no draw. bOf q kind: the divisor b. rule: round by round, 0 if c · b = a · n, 1 if
less, 2 if more.
Limits: in the closing's part of each list the d variables of degree 2 come first, then the w of
degree 1. So the lists are those of a typed lookup A : LkAsmH only where A.oE = Fin.revPerm.
That epsN is then a typed lookup's list of errors and nN its challenge sets' sizes:
OnBytes/Tie/Pv/Lookup/Lists/TwLetter.lean (asmV_eps_port, asmV_sizes),
OnBytes/Tie/Pv/Lookup/Port/TwFour.lean (entN_sizes). That ratN is the planner's, and that
c · b = a · n at every round for all sizes: OnBytes/Tie/Pv/Lookup/Lists/TwPlanOne.lean (rule_all).

-/
set_option autoImplicit false

namespace TwErr

/-- a sumcheck with k variables of degree g (the round polynomial's degree), the further variable Y
of degree gY, and the round of the end values -/
def pscC (k g gY : Nat) : List Nat := [1] ++ List.replicate k g ++ [gY, 0]
def pscV (q k : Nat) : List Nat := [q] ++ List.replicate k q ++ [q - 1, 1]
def pscR (k g gY : Nat) : List (Nat × Nat) :=
  [(1, 1)] ++ List.replicate k (g, 1) ++ [(gY, 2), (0, 0)]

def epsN (v' d w n q : Nat) : List Nat :=
  [2 ^ (v' + 1) - 1] ++ (List.range (n + 1)).flatMap (fun _ => pscC 0 0 3) ++ [w * q ^ (w - 1)] ++
  (List.range (v' + 1)).flatMap (fun l => pscC l 2 2 ++ [1]) ++
  (List.range d).flatMap (fun l => pscC (w + l) 2 2 ++ [1]) ++
  ([1] ++ List.replicate d 2 ++ List.replicate w 1) ++
  [(w + d) * q ^ (w + d - 1)] ++ pscC (w + d) 2 2

def nN (v' d w n q : Nat) : List Nat :=
  [q] ++ (List.range (n + 1)).flatMap (fun _ => pscV q 0) ++ [q ^ w] ++
  (List.range (v' + 1)).flatMap (fun l => pscV q l ++ [q]) ++
  (List.range d).flatMap (fun l => pscV q (w + l) ++ [q]) ++
  ([q] ++ List.replicate d q ++ List.replicate w q) ++
  [q ^ (w + d)] ++ pscV q (w + d)

def ratN (v' d w n : Nat) : List (Nat × Nat) :=
  [(2 ^ (v' + 1) - 1, 1)] ++ (List.range (n + 1)).flatMap (fun _ => pscR 0 0 3) ++ [(w, 1)] ++
  (List.range (v' + 1)).flatMap (fun l => pscR l 2 2 ++ [(1, 1)]) ++
  (List.range d).flatMap (fun l => pscR (w + l) 2 2 ++ [(1, 1)]) ++
  ([(1, 1)] ++ List.replicate d (2, 1) ++ List.replicate w (1, 1)) ++
  [(w + d, 1)] ++ pscR (w + d) 2 2

def bOf (q kind : Nat) : Nat := if kind == 1 then q else if kind == 2 then q - 1 else 1

/-- The rule at one round, three-valued: 0: c · b = a · n; 1: c · b < a · n; 2: c · b > a · n. -/
def ruleAt (q : Nat) (c n : Nat) (r : Nat × Nat) : Nat :=
  if c * bOf q r.2 == r.1 * n then 0 else if c * bOf q r.2 < r.1 * n then 1 else 2

def rule (v' d w n q : Nat) : List Nat :=
  (((epsN v' d w n q).zip (nN v' d w n q)).zip (ratN v' d w n)).map fun x => ruleAt q x.1.1 x.1.2
      x.2

def sameLengths (v' d w n q : Nat) : Bool :=
  (epsN v' d w n q).length == (nN v' d w n q).length && (epsN v' d w n q).length ==
      (ratN v' d w n).length

end TwErr
