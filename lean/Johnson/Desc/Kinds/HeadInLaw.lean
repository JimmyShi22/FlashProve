-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/HeadInLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE LAW OF WHAT COMES IN FROM THE
LOOKUP (HeadIn.lean's fromLookup): STATED HERE, proved in Law/FromLookup.lean. Definitions and
nothing else.

WHY. The head's lemmas (HeadLaw.lean) take an entry's weight from a point: by definition it is the
block's weight times the equality weight inside the block, and wsum, wx, below are sums of such
weights. The block that runs takes these letters from fromLookup: arrays made of each call's key
point. That the arrays hold what the lemmas take them for is said here. No chance in it.

THE PREMISE ON THE POINTS (PointsOk) is the third test of HeadFrame.lean's given, as a proposition:
each call's key point has lJ + lt coordinates and ends in the lookup's last ls + lt coordinates. IT IS
K6's OWN TEST, ON THE CARRIED RECORD, OF WHAT THE LOOKUP's FILES CALL K3CallsShareThePoint (Johnson/Top/H/K3LawKind.lean): where given
returns it holds (Law/FromGiven.lean: given_ok); that the lookup lays its points so is the lookup's law.

WHAT IT SAYS (LettersOk), of all nine keys of the place, the normalization's four and the head's five:
  column   below a key's length an entry's weight is the equality weight of ITS COLUMN at its call's
           point on the columns: what the lookup's own law will speak of;
  beyond   from a key's length on the letter is 0;
  block    for a key whose length is a multiple of S2: below the length an entry's weight is its
           block's times the equality weight of zl at its place in the block;
  wsum     the sum of the weights below the length;
  wx       (the head's five) the sum over the entries that stand for a vocabulary entry below V;
  below    (the top digit's) AT v <= V ALONE the sum over the entries below v: the letter is an array
           of V + 1 sums and gives 0 beyond;
  zt, zl   have lt and ls coordinates; tail: every key point is its point on the columns, then zt.

WHAT IT DOES NOT SAY. That two entries take two columns, that a column lies below 2^lJ, what the
padding's term is: a law of its own (not yet stated). That the points are the lookup's: they are
letters. Nothing on a verifier's yes, on probabilities or on what a proof hides.
EVERY = IS AN EQUALITY OF RECORDS OF THREE WORDS. No natural number is laid into the field here but 0
and 1.

-/
import Johnson.Desc.Kinds.HeadIn
import Johnson.Desc.Kinds.HeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Norm (lt ls d S2)

/-- A key's call in callList, and its number in that call. -/
def placeOf : PlaceKey → Nat × Nat
  | .inl .remLow => (0, 0)
  | .inl .remHigh => (0, 1)
  | .inr .marginTop => (0, 2)
  | .inr .marginMid => (1, 0)
  | .inl .digits => (2, 0)
  | .inr .marginLow => (2, 1)
  | .inr .tableA => (3, 0)
  | .inr .tableB => (4, 0)
  | .inl .clamp => (5, 0)

/-- The keys of a key's call. -/
def keysOf (k : PlaceKey) : List PlaceKey := callList.getD (placeOf k).1 []

/-- The letters of a key of the place. -/
def ewOf (i : FromLookup) : PlaceKey → Nat → E
  | .inl k => i.norm.ew k
  | .inr k => i.head.ew k
@[inherit_doc ewOf] def ewhOf (i : FromLookup) : PlaceKey → Nat → E
  | .inl k => i.norm.ewh k
  | .inr k => i.head.ewh k
@[inherit_doc ewOf] def wsumOf (i : FromLookup) : PlaceKey → E
  | .inl k => i.norm.wsum k
  | .inr k => i.head.wsum k

variable [Sizes]

/-- A key's call's point on its columns. -/
def onColumns (floor : Nat) (zk : Nat → Point) (k : PlaceKey) : Point :=
  (zk (placeOf k).1).extract 0 (lJ floor (keysOf k))

/-- The column of entry x of a key. -/
def columnOf (k : PlaceKey) (x : Nat) : Nat := column ((keysOf k).map lenOf) (placeOf k).2 x

/-- The third test of HeadFrame.lean's given. -/
def PointsOk (floor : Nat) (zx : Point) (zk : Nat → Point) : Prop :=
  ∀ c keys, callList[c]? = some keys →
    (zk c).size = lJ floor keys + lt ∧ (zk c).last (ls + lt) = zx.last (ls + lt)

/-- The letters are the weights that they are taken for. -/
structure LettersOk (floor : Nat) (zk : Nat → Point) (i : FromLookup) : Prop where
  column : ∀ k x, x < lenOf k → ewOf i k x = eq (onColumns floor zk k) (columnOf k x)
  beyond : ∀ k x, lenOf k ≤ x → ewOf i k x = 0
  block : ∀ k, S2 ∣ lenOf k → ∀ x, x < lenOf k →
    ewOf i k x = ewhOf i k (x / S2) * eq i.norm.zl (x % S2)
  wsum : ∀ k, wsumOf i k = ∑ x < lenOf k, ewOf i k x
  wx : ∀ k : Key, i.head.wx k = ∑ x < len k, if first k + x < V then i.head.ew k x else 0
  below : ∀ v, v ≤ V → i.head.below v = ∑ x < v, i.head.ew .marginTop x
  zt : i.norm.zt.size = lt
  zl : i.norm.zl.size = ls
  tail : ∀ c keys, callList[c]? = some keys →
    (zk c).toList = ((zk c).extract 0 (lJ floor keys)).toList ++ i.norm.zt.toList

/-- **THE LAW OF fromLookup.** At points that pass the test, with at least one vocabulary entry and
every key's length below 2^41 (column looks for a piece among 41 bits). WHO PAYS: the test: given;
0 < V and the lengths: the tests on the plan (2 <= V; the rows "Z" and "no-wrap-ledger"). -/
def FromLookupStatement : Prop :=
  ∀ [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point),
    0 < V → (∀ k, lenOf k < 2 ^ 41) → PointsOk floor zx zk →
    LettersOk floor zk (fromLookup floor zx zk)

end VerifiableInference.Desc.Kinds.Head.Law
