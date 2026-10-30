-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Statement.lean: WHAT IS OWED OF THE HONEST SIDE OF THE MERGE
OF THE CLAIMS ON THE WEIGHTS (Honest/K11/Part.lean) AGAINST THE KIND's OWN TEXT
(Johnson/Desc/First/Fork/MergeKind.lean): STATEMENTS ALONE: five, each a definition of a
proposition. NOTHING IS PROVED IN THIS FILE (the proofs: Chain.lean, Hears.lean, Passes.lean and
Whole.lean of this folder), and none of the five is one of the library's goals: they are lemmas'
statements.

The prover's text is `sumPart` at `headMergeJob`, played alone (`alone`, Honest/SumLaw/Terms.lean).
The law of the masked sumcheck's honest part for all callers is stated in Honest/SumLaw/
Statement.lean, against the part's text of the verifier's sumcheck; the tie from that text to the
flat text, which this kind's text calls, in Johnson/Desc/Part/MaskedSumFlat.lean. What is stated
here is what this kind owes beside the two.

  `HeadMergeCall`      the call as it stands in a session is `headMergeShape`: it has no point
  `HeadMergeSummand`   at its two ends what is summed is the function on which the merge's sumcheck
                       runs (`fmAt`, Johnson/Road/FormsKeysMerge.lean): the sum over all columns
                       reads as that function's sum over the points that spell the columns; the end
                       value as the function at the challenges. (Between the ends the rounds' lists
                       are tied to each other, not to `fmAt`:
                       Johnson/Desc/K11/Honest/Law/Tables.lean.)
  `HeadMergeSumsTo`    the same in the form in which the law for all callers takes a caller
                       (`SumsTo`): round by round the job's own lists sum from the function's sum
                       over all columns to its value at the challenges plus beta times the end
                       value's coin
  `HeadMergeHears`     where the part's `hear` returns on the sumcheck's rounds, the kind's maker of
                       the tape returns on all rounds and its `mergeHear` returns on that tape: the
                       same ledger; the same letters; what it hands on
  `HeadMergeInner`     at true claims, on the rounds of the part played alone behind a batching
                       round: the kind's maker of the tape and its hearing return; (1) the form that
                       its run of claims then makes is worth 0 in the world of the ledger behind and
                       the mask entries; (2) the weights for the rows are made, and under them the
                       matrix, read at the merge's point, plus beta times the coin is the end value
                       as it was shown

The field's words are read by a reading (`Reading K`, OnBytes/Model/HideLaws.lean). `HeadMergeInner`
stands at the release's own (`Reading.gl`), as the law for all callers does; the two statements on
the summand at every reading into a field.

Premises, and where they can be met. `UnitOK` and "the unit lies within the matrix": theorems for
every unit of a layout that the verifier builds (`unitOK_of_layout`,
Johnson/Road/FormsKeysWLay.lean). `LedgerReady` (Johnson/Desc/Part/MaskedSumReady.lean): the promise
that the law for all callers asks too. "Each claim is true" is what stands in front of the merge.
VALUES AT WHICH ALL PREMISES OF `HeadMergeInner` HOLD TOGETHER are typed in Member.lean of this
folder; Honest/K11/Toy.lean evaluates its conclusion at a layout, claims, a ledger and coins that
pass the premises' tests with code.

Limits. `HeadMergeInner` speaks of the kind's maker of the tape, of its hearing and of the function
that its run of claims calls, not of the block's decision on a state. (2) is not the text that lays
the pending row (`wsPending`) by name: it is that text's fold over what the merge hands on. Nothing
on how the claims are made, nor on which entries of which messages the coins are. The part stands
unlifted and is played alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms
import Johnson.Desc.Part.MaskedSumFlat
import Johnson.Desc.Part.MaskedSumReady
import Johnson.Road.FormsKeysMerge
import Johnson.Road.FormsKeysWOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E mulE zeroE oneE)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading Aff Fork Psc WsLay WsClaim WsForkOut wsClaimShape wsForkStart wsGammaAdd
  wsRowPart wsEpsT powers)
open OnBytes.Road (Wm UnitOK claimVal rowAt fmAt bitsOf)
open OnBytes.K.Kc (Fl Tape)
open VerifiableInference.Desc.Part.MaskedSum (Heard hear LedgerReady SameLetters)
open Johnson.Desc.First.ForkMerge (mergeHear mergeTapeE mergeEntries claimFits)
open Johnson.Desc.First.ForkMerge.Honest (termsOf claimedSum endAt)
open ProofFile.Honest.SumLaw (alone SumCoins firstRun endRun frontOf drawsOk varsOf jobPoly SumsTo)

/-- The statement that the call as it stands in a session is the shape itself. Proved as
`headMergeCall` (Chain.lean of this folder), not here; a lemma's statement, none of the library's
goals. -/
def HeadMergeCall : Prop :=
  ∀ (lay : WsLay) (w : HeadMergeAsk) (fr : Front Unit),
    (headMergeJob lay).callAt w fr = headMergeShape lay.lk

/-- The statement that, at its two ends, what is summed is the function on which the merge's
sumcheck runs. Proved as `headMergeSummand` (Chain.lean of this folder), not here; a lemma's
statement, none of the library's goals. -/
def HeadMergeSummand : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (lay : WsLay) (entry : Nat → Nat → E) (x : E)
    (cl : Array WsClaim),
    (∀ q ∈ cl, ∃ u, lay.U[q.ui]? = some u ∧ wsClaimShape lay q = .ok () ∧ UnitOK lay.lk u) →
    ρ.val (claimedSum (termsOf lay entry x cl.toList)) =
      ∑ C ∈ Finset.range (2 ^ lay.lk),
        fmAt ρ lay (fun r c => ρ.val (entry r c)) (cl.zip (powers x cl.size)).toList
          (bitsOf lay.lk C) ∧
    ∀ rs : List E, rs.length = lay.lk →
      ρ.val (endAt (termsOf lay entry x cl.toList) rs) =
        fmAt ρ lay (fun r c => ρ.val (entry r c)) (cl.zip (powers x cl.size)).toList rs.toArray

/-- The statement that the job's own lists sum, round by round, from the function's sum over all
columns to its value at the challenges plus beta times the end value's coin. cl: the claims; x: the
element that batches them: both as `headMergeTerms` reads them off what was heard. m: the end
values' coins. Proved as `headMergeSumsTo` (Chain.lean of this folder), not here; a lemma's
statement, none of the library's goals. -/
def HeadMergeSumsTo : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (lay : WsLay) (w : HeadMergeAsk) (fr : Front Unit)
    (cl : Array WsClaim) (x beta : E) (m rs : List E),
    cl = (w.claims fr.heard.dropLast).toArray → x = (drawnE fr.heard).getLastD zeroE →
    (∀ q ∈ cl, ∃ u, lay.U[q.ui]? = some u ∧ wsClaimShape lay q = .ok () ∧ UnitOK lay.lk u) →
    rs.length = lay.lk →
    SumsTo ρ (headMergeShape lay.lk).all (jobPoly (headMergeJob lay) w fr m) [] (rs ++ [beta])
      (∑ C ∈ Finset.range (2 ^ lay.lk),
        fmAt ρ lay (fun r c => ρ.val (w.entry r c)) (cl.zip (powers x cl.size)).toList
          (bitsOf lay.lk C))
      (fmAt ρ lay (fun r c => ρ.val (w.entry r c)) (cl.zip (powers x cl.size)).toList rs.toArray +
        ρ.val beta * ρ.val (m.headD zeroE))

/-- The statement that, where the part's hearing returns on the sumcheck's rounds, the kind's maker
of the tape and its hearing return. r₀: the batching round: nothing sent, one element x drawn. rs:
the sumcheck's rounds, which draw elements alone. The ledger's arrays have their sizes. Proved as
`headMergeHears` (Hears.lean of this folder), not here; a lemma's statement, none of the library's
goals. -/
def HeadMergeHears : Prop :=
  ∀ (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (F G : Fork) (work : Nat) (r₀ : Fmt.RoundView)
    (rs : List Fmt.RoundView) (x : Fmt.Ext) (h : Heard),
    cl.size ≠ 0 → cl.size ≤ 4096 → sv.size = cl.size →
    (∀ q ∈ cl, q.ui < lay.U.size ∧ claimFits lay q = true) → OnBytes.PscRun.Sized F →
    r₀.vals = [] → r₀.drawn.elems = [x] → r₀.drawn.poss = [] → r₀.drawn.trits = [] →
    (∀ r ∈ rs, r.drawn.poss = [] ∧ r.drawn.trits = []) →
    hear (wsForkStart sv (powers (E.ofTriple x) sv.size)) (headMergeShape lay.lk) F rs =
      some (h, G) →
    ∃ (tp : Tape) (wo : WsForkOut),
      mergeTapeE (r₀ :: rs) (mergeEntries lay.lk cl.size work) = .ok tp ∧
      mergeHear lay cl sv F tp = .ok (wo, G, []) ∧ SameLetters wo.p h ∧
      wo.p.started = true ∧ wo.p.rowMade = false ∧ wo.p.vars.isEmpty = false ∧
      wo.p.r.size = wo.p.vars.size ∧
      wo.sFv = h.sEnd ∧ wo.rm.toList = h.r.take lay.lk ∧ wo.beta = h.r.getLastD zeroE ∧
      G.shown h.sEnd = some wo.fvp ∧
      wo.recs = (cl.zip (powers (E.ofTriple x) sv.size)).toList.map fun y =>
        wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))

/-- The statement that the honest rounds pass. n₁, n₂: the two runs' names. c: the coins. t: the
state in front of the sumcheck's part: the last challenge that it has heard is the batching round's.
ds: the sumcheck's challenges. rounds: the part's, played alone. cl, sv: the claims and the slots of
their values. F: the ledger in front. W: the committed matrix, as the part's input reads inside it.
mask: the segment's mask row, by slot; ent: the arrays' entries, which no form here names. Proved as
`headMergeInner` (Whole.lean of this folder), not here; a lemma's statement, none of the library's
goals. -/
def HeadMergeInner : Prop :=
  ∀ (n₁ n₂ : String) (lay : WsLay) (c : SumCoins n₁ n₂ (headMergeJob lay))
    (t : State HeadMergeAsk Unit) (seen : Seen) (ds : List Fmt.Drawn)
    (rounds : List Fmt.RoundView) (r₀ : Fmt.RoundView) (x : Fmt.Ext) (work : Nat) (cl : Array WsClaim)
    (sv : Array Nat) (F : Fork) (W : Wm GE) (mask : Nat → GE) (ent : Nat → Nat → Nat → GE),
    -- the batching round
    r₀.vals = [] → r₀.drawn.elems = [x] → r₀.drawn.poss = [] → r₀.drawn.trits = [] →
    t.heard.getLast? = some r₀.drawn →
    -- the sumcheck's challenges: as many elements as the call's entries state, and elements alone
    drawsOk (headMergeShape lay.lk) ds = true → (∀ d ∈ ds, d.poss = [] ∧ d.trits = []) →
    -- the part's rounds
    alone (sumPart (V := Unit) n₁ n₂ (headMergeJob lay)) c t seen ds = some rounds →
    -- the claims: as the part makes them; their number; each on a unit of the layout that is in
    -- order and lies within the matrix, with fitting sizes
    cl = (t.input.claims t.heard.dropLast).toArray →
    cl.size ≠ 0 → cl.size ≤ 4096 → sv.size = cl.size →
    (∀ q ∈ cl, ∃ un, lay.U[q.ui]? = some un ∧ wsClaimShape lay q = .ok () ∧ UnitOK lay.lk un ∧
      un.off + un.rows ≤ lay.m0) →
    -- the matrix
    (∀ r k, r < lay.m0 → k < 2 ^ lay.lk → Reading.gl.val (t.input.entry r k) = W r k) →
    -- the ledger is ready for the call at the merge's claimed form
    LedgerReady (wsForkStart sv (powers (E.ofTriple x) sv.size)) (headMergeShape lay.lk) F →
    -- the claims' values are laid under their slots: the ready ledger's second clause, said of sv
    (∀ j ∈ sv, OnBytes.PscRun.Filled F j) →
    -- the mask entries under the sumcheck's own slots are the coins of the first run
    (∀ i, i < 2 * lay.lk + 2 →
      mask (F.next + i) = Reading.gl.val ((firstRun c).getD i zeroE)) →
    -- EACH CLAIM IS TRUE: the hidden value under its slot is what the claim speaks of
    (∀ a, a < cl.size → (F.worldOf Reading.gl mask ent).slot (sv.getD a 0) =
      claimVal Reading.gl lay W (cl.getD a default)) →
    ∃ (tp : Tape) (wo : WsForkOut) (F' : Fork),
      -- the kind's maker of the tape and its hearing return; the tape is used up
      mergeTapeE (r₀ :: rounds) (mergeEntries lay.lk cl.size work) = .ok tp ∧
      mergeHear lay cl sv F tp = .ok (wo, F', []) ∧ F'.next = F.next + 2 * lay.lk + 3 ∧
      wo.rm.toList = (varsOf (headMergeShape lay.lk) ds).take lay.lk ∧
      wo.beta = (varsOf (headMergeShape lay.lk) ds).getLastD zeroE ∧
      -- (1) at whatever number of claims the decision writes into the ledger
      (∀ n : Nat, ∃ (G : Fork) (p' : Psc),
        Fl.pscRow wo.p wo.fvp {} { F' with planClaimsF := n } [] =
          some ((wo.p.rowForm wo.fvp {}, p'), G, []) ∧
        (wo.p.rowForm wo.fvp {}).value Reading.gl (G.worldOf Reading.gl mask ent) = 0) ∧
      -- (2)
      ∃ Gam : Array E,
        wo.recs.foldlM (fun A r => wsGammaAdd A lay r oneE) (Array.replicate lay.m0 zeroE) =
          .ok Gam ∧
        ∑ y ∈ Finset.range lay.m0, Reading.gl.val (Gam.getD y zeroE) *
            rowAt Reading.gl lay.lk wo.rm W y +
          Reading.gl.val wo.beta * Reading.gl.val ((endRun c).headD zeroE) =
            Reading.gl.val wo.fvp

end ProofFile.Honest.K11
