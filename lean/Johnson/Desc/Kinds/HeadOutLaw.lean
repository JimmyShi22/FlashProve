-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadOutLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS: WHAT THE PLACE HANDS THE LOOKUP, AND WHAT
IT TAKES BACK, BY THE CALL: STATED HERE, proved in Law/OutCall.lean. Definitions and nothing else.

WHY. The lookup is paid by the call (HeadFrame.lean: keyVector; the lookup's run "join" takes one form a
call: the call's key vector at the call's key point). Three of the six calls hold keys of both halves of
the place: the final normalization's and the head's. So what the lookup takes, and what it gives back,
can be said only of both halves together.

  cornerKey c k x t   key k of the place at the corner of entry x and position t: HeadLaw.lean's keyAt,
                      HeadNormLaw.lean's keyNAt: a function of the committed cells and public data.
  keyTable c call     THE CALL's TABLE: column, position: the corner key of the entry that takes the
                      column; the call's padding key where no entry takes it.
  OutCallStatement    OUT, no chance in it: in a world in which the head's five keys are spread over their
                      corner keys (the head's half: K06OutStatement concludes just that), three
                      reads of the normalization and the claimed sum of its sumcheck "normed" are true:
                      THE VALUE OF EACH CALL's KEY VECTOR IS THE MULTILINEAR EXTENSION OF THE CALL's TABLE AT
                      THE CALL's KEY POINT.
  BackCallStatement   BACK, no chance in it: if every place of every call's table is a row of the call's
                      lookup table, then each of the nine keys, at every entry and position, is a row of
                      its table: the six fields of CellRel and the four of CellRelN that speak of keys.
  PadsStatement       a guard: each call's padding key is a row of the call's table: so BACK's premise is
                      not shut by the padding.

WHAT IT DOES NOT SAY. That the claimed sum of "normed" is true: a law of that sumcheck, with chance in it:
Law/Normed.lean's. That keyTable holds the padding key at the places that the lookup COUNTS as padding: it holds
it at the columns that no entry takes, and nowhere else: at the column of an entry that stands for a vocabulary
entry from V on it holds that entry's corner key. That the reads are true (the range check's). That the lookup gives BACK's premise from
OUT's conclusion (the lookup's law). That cells and table are fixed before the lookup's draws: c is a
letter. Nothing on a verifier's yes, on probabilities, on what a proof hides.
EVERY NATURAL THAT IS LAID INTO THE FIELD HERE: padKey call: at most 2^40 + 2^15 under F = 24.

-/
import Johnson.Desc.Kinds.HeadFrame
import Johnson.Desc.Kinds.HeadCallLaw
import Johnson.Desc.Kinds.HeadNormLaw
import Johnson.Desc.Kinds.Law.Val

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (World)
open Norm (lt ls d S2 T)
open Came (val)

variable [Sizes] [Policy] [Request] [Token]

/-- A key of the place at the corner of entry x and position t. -/
def cornerKey (c : NCells) : PlaceKey → Nat → Nat → E
  | .inl k, x, t => keyNAt c (cornerN x t) k
  | .inr k, x, t => keyAt c.toCells (corner x t) k

/-- THE CALL's TABLE, of the cells. -/
def keyTable (c : NCells) (call col t : Nat) : E :=
  callTable call (cornerKey c) ((padKey call : Nat) : E) col t

/-- A row of call number call's lookup table: two ranges of 16 bits; the range of 8 bits; the table in
two halves; the clamp's table. -/
def InTable (tab : Nat → Nat) : Nat → E → Prop
  | 0 => InBits 16
  | 1 => InBits 16
  | 2 => InBits 8
  | 3 => IsRow tab
  | 4 => IsRow tab
  | _ => IsClampRow

/-- What is asked of a world for the normalization's four keys: three reads, each below the length that
the keys spend, and the claimed sum of "normed". -/
structure NormTrue [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] (W : World K)
    (c : NCells) : Prop where
  act : ∀ i, i < 2 * d → val W (FinalNorm.entry .actAtKeys i)
    = rd (readAtN c (.act, .short (eq FinalNorm.zt)) i)
  row : ∀ i, i < NR + 21 → val W (FinalNorm.entry .rowAtKeys i)
    = rd (readAtN c (.row, .short (eq FinalNorm.zt)) i)
  wide : ∀ i, i < 4 * d / S2 → val W (FinalNorm.wide i)
    = rd (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) i)
  claimed : val W FinalNorm.normed.claimed.var = rd (trueNormed c)

/-- **OUT, BY THE CALL.** -/
def OutCallStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] [Norm.Heard] [FinalNorm.Heard]
    [Heard] [FinalNorm.Reads] [Reads] (sT floor : Nat) (zx : Point) (zk : Nat → Point) (c : NCells)
    (W : World K),
    planOk sT = true → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    (∀ k : Key, val W (key k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      rd (In.ew k x) * rd (eq FinalNorm.zt t) * rd (keyAt c.toCells (corner x t) k)) →
    NormTrue W c →
    ∀ call, call < 6 →
      val W (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call))
        = (Finset.range (2 ^ (zk call).size)).sum fun i =>
            rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))

/-- **BACK, BY THE CALL.** -/
def BackCallStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT floor : Nat) (tab : Nat → Nat) (c : NCells),
    planOk sT = true →
    (∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable tab call (keyTable c call col t)) →
    (∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c.toCells (corner x t) .marginTop)) ∧
    (∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c.toCells (corner x t) .marginMid)) ∧
    (∀ t, t < T → ∀ x, x < JV → InBits 8 (keyAt c.toCells (corner x t) .marginLow)) ∧
    (∀ t, t < T → ∀ x, x < len .tableA → IsRow tab (keyAt c.toCells (corner x t) .tableA)) ∧
    (∀ t, t < T → ∀ x, x < len .tableB → IsRow tab (keyAt c.toCells (corner x t) .tableB)) ∧
    (∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remLow)) ∧
    (∀ t, t < T → ∀ x, x < d → InBits 16 (keyNAt c (cornerN x t) .remHigh)) ∧
    (∀ t, t < T → ∀ x, x < d → IsClampRow (keyNAt c (cornerN x t) .clamp)) ∧
    (∀ t, t < T → ∀ j, j < NR + 21 → InBits 8 (keyNAt c (cornerN j t) .digits))

/-- **The padding keys are rows.** -/
def PadsStatement : Prop :=
  ∀ [Sizes] (tab : Nat → Nat), tab 0 = 2 ^ F → ∀ call, call < 6 →
    InTable tab call ((padKey call : Nat) : E)

end VerifiableInference.Desc.Kinds.Head.Law
