-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/Points.lean: the point that each sumcheck of a lookup hands on, from the plain data.

Lkp.run (OnBytes/Iop/Lkp.lean) returns none of these points by itself: each goes into the next
claim. This file computes them from the elements drawn. A SECOND TYPING: `orders` says once more
which order of binding belongs to which sumcheck, which Lkp.levelChain and Lkp.run say in their own
text. It uses the program's own functions for the orders (Lkp.defaultOrder, Lkp.orderBeginning) and
for putting a challenge back at its variable's place (Lkp.byVariable).

Main definitions: orders, challenges, points.
Not claimed. That `orders` is the program's at any lookup. No theorem.

-/
import OnBytes.G4.Flat

namespace OnBytes.G4

/-- For each sumcheck of the lookup, in the order of the rounds: the variables that its rounds bind,
in that order. The steps of the tie and of the parts' roots bind none. -/
def orders (S : Lkp.Public) : List (List Nat) :=
  List.replicate (S.planes - 1) [] ++ List.replicate (S.parts.length - 1) [] ++
  (S.parts.flatMap fun v => (List.range v).map fun l =>
    if l + 1 == v then Lkp.orderBeginning S.lastKeyLevelOrder l else Lkp.defaultOrder l) ++
  ((List.range S.d).map fun l => Lkp.defaultOrder (S.mu + l)) ++
  [Lkp.defaultOrder (S.mu + S.d), Lkp.defaultOrder (S.mu + S.d)]

/-- For each sumcheck, in the order of the rounds: the elements drawn in its rounds "PSC round". A
sumcheck begins at a round "PSC epsilon". -/
def challenges (S : Lkp.Public) (t : Flat) : List (List E) :=
  (((entries S).zip t.rounds).foldl (fun (acc : List (List E)) p =>
    if p.1.name == "PSC epsilon" then [] :: acc
    else if p.1.name == "PSC round" then
      match acc with
      | c :: rest => (c ++ p.2.drawn) :: rest
      | [] => acc
    else acc) []).reverse

/-- For each sumcheck, in the order of the rounds: the point that it hands on, each challenge at its
variable's place. Nothing unless the lookup is served, the plain data fit it, and each sumcheck has
as many challenges as its order has variables. -/
def points (S : Lkp.Public) (t : Flat) : Option (List (List E)) :=
  let cs := challenges S t
  if served S && t.fits S && cs.map (·.length) == (orders S).map (·.length) then
    some ((cs.zip (orders S)).map fun p => Lkp.byVariable p.1 p.2)
  else none

end OnBytes.G4
