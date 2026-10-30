-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/Statement.lean: THE DECISION OF THE MERGE OF THE CLAIMS ON THE WEIGHTS
RETURNS: `headMergeDecide` (Johnson/Desc/First/Fork/MergeKind.lean): STATEMENTS ALONE: two, each a
definition of a proposition, and four definitions that they need. NOTHING IS PROVED IN THIS FILE,
and neither is one of the library's goals: they are lemmas' statements. The text is the verifier's;
no prover is named, and no frame of a prover.

The form: premises on fields of the state that hold no field element (which arm, flags, whether
something is laid, numbers that the plan fixes, lengths, the ledger's marks), and the step's own
test on the rounds (`roundsFit`, Johnson/Desc/Block.lean): then the decision returns, and the like
fields of the state behind are written out, each of the fields in front.

  `MergeRoundsForm`          rounds of the merge's form: the batching round; the beginning; a round
                             for each column bit; the round in the further variable; the end value
  `HeadMergeRoundsFit`       rounds that pass `roundsFit` at the kind's declared rounds have it
  `mergeEndSlot`             the end value's slot
  `LedgerBehind`             the ledger behind, of the ledger in front
  `MergeBehind`              what the merge leaves, as far as it holds no field element
  `HeadMergeDecideReturns`   the decision returns; the state behind

NO TEST ON A VALUE STANDS AMONG THE PREMISES BUT ONE THAT `roundsFit` HOLDS: that the element drawn
in the round of the further variable is not 0 as raw words (`drawsMarkedNonzeroHaveNonzeroWords`); the decision itself does not
ask it. So the statement stands at all values that pass `roundsFit`: whether what was sent is true
does not enter.

Limits. ONE PREMISE IS WIDER THAN THE TEXT: `Sized` asks the size of all three of the ledger's
arrays; the decision itself tests that of the marks alone; the two others are asked because the
library's laws on the ledger take them, and they are handed on behind. The kind's own decision, not
the description's member at the place, which tests beside it that the state bears no mark of failure
and that the reply stands. The state behind is written out whole, so both can be read off it.
Nothing on the run of claims "the merge" (`headMergeClaim`). Nothing on any property.
-/
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Desc.Part.MaskedSumShape
import OnBytes.Tie.Pv.Psc.PscFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E)
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork WsLay WsClaim WsForkOut wsRowPart)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Part.MaskedSum (Sent)

/-- Rounds of the merge's form. Each draws elements alone. The batching round sends nothing and
draws one element; the beginning sends one scalar and draws one; each of the lk rounds in a column
bit sends two and draws one; the round in the further variable sends one and draws one; the last
sends one and draws nothing. -/
def MergeRoundsForm (lk : Nat) (rs : List Fmt.RoundView) : Prop :=
  (∀ r ∈ rs, r.drawn.poss = [] ∧ r.drawn.trits = []) ∧
  ∃ (r₀ r1 rY rv : Fmt.RoundView) (u : List Fmt.RoundView), rs = r₀ :: r1 :: (u ++ [rY, rv]) ∧ u.length = lk ∧
    r₀.vals = [] ∧ r₀.drawn.elems.length = 1 ∧
    (∃ s d, Sent r1 1 1 s d) ∧ (∀ r ∈ u, ∃ s d, Sent r 2 1 s d) ∧ (∃ s d, Sent rY 1 1 s d) ∧
    ∃ s, Sent rv 1 0 s []

/-- The statement that rounds which pass the step's own test at the kind's declared rounds have the
merge's form, with the sealed digest or without. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeRoundsFit : Prop :=
  ∀ (P : HeadMergeP) (rs : List Fmt.RoundView), roundsFit (headClaimMergeKind P).rounds rs = true →
    MergeRoundsForm P.lay.lk (rs.map noDigest)

/-- The end value's slot: behind the slot of the hiding polynomial's sum, two for each column bit
and one for the further variable. -/
def mergeEndSlot (lk : Nat) (F : Fork) : Nat := F.next + 2 * lk + 2

/-- The ledger behind the merge, of the ledger F in front: 2 lk + 3 slots are taken; one mark more,
at the end value's slot; the two arrays of values keep their sizes; every other field stands. -/
def LedgerBehind (lk : Nat) (F G : Fork) : Prop :=
  G = { F with next := F.next + 2 * lk + 3, vp := G.vp, mf := G.mf
               gotF := F.gotF.set! (mergeEndSlot lk F) true } ∧
    G.vp.size = F.vp.size ∧ G.mf.size = F.mf.size

/-- What the merge leaves, as far as it holds no field element. sv: the slot of the claim's value.
F: the ledger in front. The sumcheck's variables are written out, since the run of claims lays as
many slots as their numbers of coefficients say; the claimed form's slots by number, since later
tests read a form's slots. -/
def MergeBehind (lay : WsLay) (claim : WsClaim) (sv : Nat) (F : Fork) (wo : WsForkOut) : Prop :=
  wo.p.started = true ∧ wo.p.rowMade = false ∧ wo.p.ended = true ∧ wo.p.first = F.next ∧
    wo.p.vars.toList = List.replicate lay.lk (Weight.plain 3) ++ [Weight.atZero 2] ∧
    wo.p.r.size = lay.lk + 1 ∧
    wo.p.start.slots.toList.map (·.1) = [sv] ∧ wo.p.start.ents = #[] ∧
    wo.rm.size = lay.lk ∧ wo.sFv = mergeEndSlot lay.lk F ∧
    ∃ ka : E, wo.recs = [wsRowPart lay claim ka]

/-- The statement that the decision returns. The head's link is open, nothing is owed by the round
in front, the claim and what the head heard are laid; the claim's sizes fit its unit; the ledger's
arrays have their size, the claim's value is laid under its slot, the end value's slot is there and
free, and the slots come out at the plan's number; the rounds pass the step's own test. Then the
decision returns on the rounds without the sealed digest; the state behind is written out. Not
proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeDecideReturns : Prop :=
  ∀ (P : HeadMergeP) (s : S) (a : HeadOwn) (claim : WsClaim) (x : OnBytes.Model.Head.Heard)
    (rs : List Fmt.RoundView),
    s.here = .head a → a.opened = true → s.noneWaits = true → a.claim = some claim →
    a.x = some x → claimFits P.lay claim = true →
    Sized a.F → Filled a.F x.sV →
    mergeEndSlot P.lay.lk a.F < a.F.ns → ¬ Filled a.F (mergeEndSlot P.lay.lk a.F) →
    a.F.next + 2 * P.lay.lk + 3 = P.nMsg →
    roundsFit (headClaimMergeKind P).rounds rs = true →
    ∃ (wo : WsForkOut) (G : Fork),
      headMergeDecide P s (rs.map noDigest) =
        .ok { s with
          rowsOwed := none
          here := .head { a with
            wo := some wo, F := { G with planClaimsF := P.nLin }, Fm := a.F
            slot := some G.next } } ∧
      LedgerBehind P.lay.lk a.F G ∧ MergeBehind P.lay claim x.sV a.F wo

end Johnson.Desc.First.ForkMerge.Returns
