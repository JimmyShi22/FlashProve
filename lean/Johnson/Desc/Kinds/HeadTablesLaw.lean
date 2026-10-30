-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadTablesLaw.lean: THE OUTPUT HEAD's PLACE: THE TIE OF THE SIX CALLS' LOOKUP TABLES, AND WHAT THE
FOUR PARTS OF THE HEAD's RELATION MEAN: STATED HERE, proved in Law/TableTie.lean. Definitions and nothing else.

WHY. The lookup's law leaves: every place of a call's key table is, read in the field, the image of A ROW OF
THE CALL's TABLE IN THE VERIFIER's RECORD: a number. HeadOutLaw.lean's BackCallStatement asks: every place is a
row IN THE SENSE OF InTable tab call. Between the two stands what the record's tables hold: HeadTables.lean's
test rowsOk, on the rows as numbers.
  TablesStatement  where the test passes: every row of every call is a row in InTable's sense, at the table
                   tabOf row, and TableOk (tabOf row).
  TieStatement     THE TIE: where the test passes: a place of keyTable that is read in the field as the image
                   of a row of its call's table IS a row in InTable's sense: so the lookup's law gives
                   BackCallStatement's premise.
  HeadParts        THE HEAD's RELATION ON CELLS IN FOUR PARTS, as the table of joints cuts it: idn (mean, count;
                   the normalization's 17 row forms at every corner) · lookCalls (every place of every call's
                   key table is a row) · rider (clip, table at every corner) · small.
  HeadMeansStatement  the four parts, under the tests on the plan and the request, a token, TableOk and the
                   bound on the weights: the claim under the policy and the final normalization (Says, SaysN).
                   No chance in it. It is backCall (Law/OutCall.lean) and lemma1_whole, laid together.

WHAT IT DOES NOT SAY. That the test passes at any record (a run's, at the written examples). That row is the
record's. Who pays the bound on the weights: no test and no kind: it ends as a condition on the commitment.
Nothing on a verifier's yes, on probabilities, on what a proof hides.
EVERY NATURAL THAT IS LAID INTO THE FIELD: a row: below 2^16 + 2^16 2^F, or 2^16 + 2^28 2^12, under the test.

-/
import Johnson.Desc.Kinds.HeadTables
import Johnson.Desc.Kinds.HeadOutLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Norm (lt T)

/-- **Where the test passes the rows are rows.** -/
def TablesStatement : Prop :=
  ∀ [Sizes] (row : Nat → Nat → Nat), rowsOk row = true →
    TableOk (tabOf row) ∧
    ∀ call, call < 6 → ∀ u, u < 2 ^ bitsOf call → InTable (tabOf row) call ((row call u : Nat) : E)

/-- **THE TIE.** -/
def TieStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT : Nat) (row : Nat → Nat → Nat) (c : NCells),
    planOk sT = true → rowsOk row = true →
    ∀ call, call < 6 → ∀ col t u, u < 2 ^ bitsOf call →
      rd (keyTable c call col t) = ((row call u : Nat) : K) →
      InTable (tabOf row) call (keyTable c call col t)

/-- **The head's relation on cells, in four parts.** -/
structure HeadParts [Sizes] [Policy] [Request] [Token] (floor : Nat) (tab : Nat → Nat) (c : NCells) :
    Prop where
  idnSums : meanAt c.toCells = 0 ∧ countAt c.toCells = 0
  idnRows : ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0
  lookCalls : ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
    InTable tab call (keyTable c call col t)
  rider : ∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 ∧ tableAt c.toCells (corner 0 t) = 0
  small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18
  smallS : ∀ f t, (c.stream f t).natAbs < 2 ^ 18

/-- **WHAT THE FOUR PARTS MEAN.** -/
def HeadMeansStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT floor : Nat) (tab : Nat → Nat) (c : NCells),
    planOk sT = true → Request.ok = true → y < V → TableOk tab →
    (∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) →
    HeadParts floor tab c → Says c.toCells ∧ SaysN c

end VerifiableInference.Desc.Kinds.Head.Law
