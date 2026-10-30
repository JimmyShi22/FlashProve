-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/InnerStatement.lean: THE LAW ON THE HONEST ROUNDS OF THE
MERGE OF THE CLAIMS ON THE WEIGHTS (`HeadMergeInner`, Honest/K11/Inner/Statement.lean) AT THE VERY
ROUNDS THAT THE ROW PLAYS (`HeadMergePlays`, Honest/K11/Plays/Statement.lean): STATEMENTS ALONE:
two, each a definition of a proposition, and one definition that they need. NOTHING IS PROVED IN
THIS FILE, and neither is one of the library's goals: they are lemmas' statements.

Why. That law has eighteen premises. Its first eight speak of the batching round, of the state at
the sumcheck's part's entry, of the challenges, and of the part's rounds played alone. Where the row
is played at challenges that fit the declared rounds, all eight hold.

  `InnerTail`              that law from its ninth premise on: its own text, copied, under the
                           letters of the first eight. THAT IT IS THAT LAW's TAIL IS LEAN's WORD
                           ONLY WITH THE PROOF OF THE SECOND STATEMENT, which hands the law these
                           eight
  `HeadMergeFront`         at all challenges that fit the declared rounds: the eight premises, at
                           the batching round as played, the state `headMergeEntry`, and the
                           sumcheck's rounds as played
  `HeadMergeInnerPlayed`   so there the law stands from its ninth premise on

Limits. The ten premises that stay (the claims; the matrix; the ledger; the mask entries; each claim
is true) are premises still. The tail is general in the number of claims; that there is one at the
head's merge is among the ten, through the claims. Nothing on the verifier's step at a seat. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.Statement
import Johnson.Desc.ProofFile.Honest.K11.Inner.Statement

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
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- `HeadMergeInner` from its ninth premise on, its own text. The letters: as there. -/
def InnerTail (n₁ n₂ : String) (lay : WsLay) (c : SumCoins n₁ n₂ (headMergeJob lay))
    (t : State HeadMergeAsk Unit) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (r₀ : Fmt.RoundView)
    (x : Fmt.Ext) : Prop :=
  ∀ (work : Nat) (cl : Array WsClaim) (sv : Array Nat) (F : Fork) (W : Wm GE) (mask : Nat → GE)
    (ent : Nat → Nat → Nat → GE),
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

/-- The statement that the first eight premises hold where the row is played. Not proved here; a
lemma's statement, none of the library's goals. -/
def HeadMergeFront : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X),
    drawsFit ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) (d₀ :: ds) = true →
    ∃ x : Fmt.Ext, (⟨[], d₀⟩ : Fmt.RoundView).vals = [] ∧ (⟨[], d₀⟩ : Fmt.RoundView).drawn.elems = [x] ∧
      (⟨[], d₀⟩ : Fmt.RoundView).drawn.poss = [] ∧ (⟨[], d₀⟩ : Fmt.RoundView).drawn.trits = [] ∧
      (headMergeEntry claims weights m d₀).heard.getLast? = some (⟨[], d₀⟩ : Fmt.RoundView).drawn ∧
      drawsOk (headMergeShape P.lay.lk) ds = true ∧ (∀ d ∈ ds, d.poss = [] ∧ d.trits = []) ∧
      alone (sumPart (V := Unit) (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
          (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)) c
          (headMergeEntry claims weights m d₀) (m.shown.plus [⟨[], d₀⟩]) ds =
        some (headMergeSaid P claims weights c m d₀ ds).tail

/-- The statement that the law stands, from its ninth premise on, at the rounds that the row plays.
x: the one element that the batching round draws. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeInnerPlayed : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X),
    drawsFit ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) (d₀ :: ds) = true →
    ∃ x : Fmt.Ext, d₀.elems = [x] ∧
      InnerTail (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
        (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") P.lay c
        (headMergeEntry claims weights m d₀) ds (headMergeSaid P claims weights c m d₀ ds).tail
        ⟨[], d₀⟩ x

end ProofFile.Honest.K11
