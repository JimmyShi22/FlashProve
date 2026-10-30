-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadCallLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE LAW OF A CALL'S KEY VECTOR:
STATED HERE, proved in Law/Call.lean. Definitions and nothing else.

WHY. The lookup is paid BY THE CALL: for each of its six calls the head hands it one form, the call's
key vector at the call's key point zk c = (zj, zt): the padding's term and the call's keys, added
(HeadFrame.lean: keyVector). The lookup's law speaks of a table of 2^lJ columns of T keys that is fixed
before its draws. Here: IF each key of the call has a value that is spread over its entries and the
positions under the letters that come in (v k = the sum over x, t of ew k x * eq zt t * G k x t: what
Lemma 2a says of the head's five keys), THEN the padding's term and these values add up to THE
MULTILINEAR EXTENSION, AT THE CALL'S KEY POINT, OF THE CALL'S TABLE: at the column of entry x of key k
and the position t it holds G k x t; at a column that no entry takes, the call's padding key. No
chance in it. All is read in the field K (Law/Base.lean: rd).

  slot, callTable     key number s of a list of keys; a call's table.
  CallStatement       as a sum over columns and positions.
  CallPointStatement  the same as one sum over the 2^(lJ + lt) places under eq (zk c).

WHAT IT DOES NOT SAY. That a key's value is so spread (the head's five: Lemma 2a with the glue; the
normalization's four: owed). What G is. That the table is fixed before the lookup's draws: G is a
letter. Nothing on a verifier's yes, on probabilities, on what a proof hides.

-/
import Johnson.Desc.Kinds.HeadInLaw
import Johnson.Desc.Kinds.HeadColumnsLaw
import Johnson.Desc.Kinds.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Norm (lt ls d S2 T)

/-- Key number s of a list of keys. -/
def slot (keys : List PlaceKey) (s : Nat) : PlaceKey := keys.getD s (.inl .remLow)

/-- The keys of call number c. -/
def callKeys (c : Nat) : List PlaceKey := callList.getD c []

variable [Sizes]

/-- A call's table: G k x t: the value of entry x of key k at position t; pad: the padding's. -/
def callTable {α : Type} (c : Nat) (G : PlaceKey → Nat → Nat → α) (pad : α) (col t : Nat) : α :=
  tableOf ((callKeys c).map lenOf) (fun s x => G (slot (callKeys c) s) x t) pad col

/-- A key's value is spread over its entries and the positions, under the letters that come in. -/
def SpreadAt (i : FromLookup) (G : PlaceKey → Nat → Nat → K) (k : PlaceKey) (v : K) : Prop :=
  v = (Finset.range (lenOf k)).sum fun x => (Finset.range T).sum fun t =>
    rd (ewOf i k x) * rd (eq i.norm.zt t) * G k x t

/-- **THE LAW OF A CALL'S KEY VECTOR**, over columns and positions. -/
def CallStatement : Prop :=
  ∀ [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point),
    0 < V → (∀ k, lenOf k < 2 ^ 41) → PointsOk floor zx zk →
    ∀ c, c < 6 → ∀ (v : PlaceKey → K) (G : PlaceKey → Nat → Nat → K),
      (∀ k ∈ callKeys c, SpreadAt (fromLookup floor zx zk) G k (v k)) →
      rd ((fromLookup floor zx zk).calls.getD c (0, [])).1 + ((callKeys c).map v).sum
        = (Finset.range (2 ^ lJ floor (callKeys c))).sum fun col => (Finset.range T).sum fun t =>
            rd (eq ((zk c).extract 0 (lJ floor (callKeys c))) col)
              * rd (eq (fromLookup floor zx zk).norm.zt t) * callTable c G (padKey c : K) col t

/-- **The same at the call's key point**: place T * col + t of the call holds column col, position t.
-/
def CallPointStatement : Prop :=
  ∀ [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point),
    0 < V → (∀ k, lenOf k < 2 ^ 41) → PointsOk floor zx zk →
    ∀ c, c < 6 → ∀ (v : PlaceKey → K) (G : PlaceKey → Nat → Nat → K),
      (∀ k ∈ callKeys c, SpreadAt (fromLookup floor zx zk) G k (v k)) →
      rd ((fromLookup floor zx zk).calls.getD c (0, [])).1 + ((callKeys c).map v).sum
        = (Finset.range (2 ^ (zk c).size)).sum fun i =>
            rd (eq (zk c) i) * callTable c G (padKey c : K) (i / T) (i % T)

end VerifiableInference.Desc.Kinds.Head.Law
