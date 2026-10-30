-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Statement.lean: THE ROW OF THE MERGE OF THE CLAIMS ON THE
WEIGHTS (Honest/K11/Part.lean) IS PLAYED: what the frame's `play` returns on the row's rounds,
whole: STATEMENTS ALONE: three, each a definition of a proposition, and three definitions that they
need. NOTHING IS PROVED IN THIS FILE, and none of the three is one of the library's goals: they are
lemmas' statements.

The sub-protocol at whose place the row stands is a letter: of it the statements ask its declared
rounds (those of the kind's own block) and that it states no oracle message; ITS NAME AND ITS PLACE
ARE FREE: the description's member bears the place's name, not the kind's.

  `headMergeWit`      how the sumcheck's part reads its input off the row's
  `headMergeEntry`    the state at the sumcheck's part's entry, as that part is handed it
  `headMergeSaid`     the rounds that the row says: the batching round, in which nothing is sent;
                      then the sumcheck's, as the law for all callers writes them out (`sumOut`,
                      Honest/SumLaw/Out.lean)
  `HeadMergePlays`    at all coins of both parts, every input, all challenges that fit the rounds:
                      `play` returns; the rounds as played, one by one; where the run stands behind
  `HeadMergeAlone`    the sumcheck's rounds among them are those of the part played alone
                      (`alone`, Honest/SumLaw/Terms.lean) from `headMergeEntry`, behind the rounds
                      shown so far and the batching round
  `HeadMergeNoRead`   the row's rounds send no table and read no column

THE RUNS' NAMES IN THE COINS' TYPE HANG ON THE KIND's OWN PLACE (`headMergePlace P`), while the
sub-protocol's place is free: the statements hold at every place, but the book can lend these coins
only where the two places are one.

Limits. Not said: that the half of a side (`Side.half`, Honest/Side.lean) at this row has
`headMergeHalf`'s parts (through the zip of `headMergeSided`); that the description's member at the
place has the kind's declared rounds and states no oracle message. Nothing on the book's lending of
the coins: they are letters. Nothing on the verifier's step. Nothing on what the scalars are worth.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block OpenedColumn)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open ProofFile.Honest.SumLaw (alone SumCoins sumOut saidPlayed)

/-- How the sumcheck's part reads its input off the row's: as `headMergeSum` lays it. -/
def headMergeWit {W₀ Rc Xi Tr : Type} (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (i : Local W₀ Rc Xi Tr) : HeadMergeAsk :=
  ⟨claims i.x, fun r c => eOfF ((weights i.w₀).entry r c)⟩

/-- The state at the sumcheck's part's entry, as that part is handed it. m: where the run stands in
front of the row. d₀: the batching round's challenge. -/
def headMergeEntry {W₀ Rc Xi Tr X : Type} (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (m : Mid (Local W₀ Rc Xi Tr) X) (d₀ : Fmt.Drawn) :
    State HeadMergeAsk Unit :=
  ⟨headMergeWit claims weights m.st.input, m.st.heard ++ [d₀], ()⟩

/-- The rounds that the row says, as a view shows them. c: the coins of the sumcheck's part. -/
def headMergeSaid {W₀ Rc Xi Tr X : Type} (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (m : Mid (Local W₀ Rc Xi Tr) X) (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) : List Fmt.RoundView :=
  ⟨[], d₀⟩ ::
    sumOut (headMergeJob P.lay) c (headMergeEntry claims weights m d₀) (m.shown.plus [⟨[], d₀⟩]) ds

/-- The statement that the row is played. blk: the sub-protocol at whose place the row stands. v:
what a second stop may read. q: what the first part is handed for its coins: none. back: a stored
run's rounds. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergePlays : Prop :=
  ∀ (W₀ Rc Xi Tr X S Cl : Type) (blk : Block S Cl) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (v : Option (Local W₀ Rc Xi Tr)) (q : Cs ⟨0, 0⟩)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid (Local W₀ Rc Xi Tr) X),
    blk.rounds = (mergeEntries P.lay.lk 1 P.work).map (fun e => { entry := e }) →
    blk.oracles = List.replicate (P.lay.lk + 4) [] →
    drawsFit blk.rounds (d₀ :: ds) = true →
    play ((headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).steps blk v
        ((q, (), ()), c, ())) (d₀ :: ds) back m =
      .ok (⟨blk.name, blk.place, 0, true, [], [], d₀⟩ ::
          (headMergeSaid P claims weights c m d₀ ds).tail.map
            (saidPlayed blk.name ⟨blk.place, 1⟩),
        ⟨⟨m.st.input, m.st.heard ++ d₀ :: ds, m.st.own⟩, m.loc ++ d₀ :: ds,
          m.seen ++ headMergeSaid P claims weights c m d₀ ds, m.opened⟩)

/-- The statement that the sumcheck's rounds are those of the part played alone. Not proved here; a
lemma's statement, none of the library's goals. -/
def HeadMergeAlone : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : SumCoins (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay))
    (d₀ : Fmt.Drawn) (ds : List Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X),
    drawsFit ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) (d₀ :: ds) = true →
    alone (sumPart (V := Unit) (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
        (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)) c
        (headMergeEntry claims weights m d₀) (m.shown.plus [⟨[], d₀⟩]) ds =
      some (headMergeSaid P claims weights c m d₀ ds).tail

/-- The statement that the row's rounds send no table and read no column. out: the sumcheck's
rounds, any list. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeNoRead : Prop :=
  ∀ (P : HeadMergeP) (name : String) (a : VerifiableInference.Desc.Place) (d₀ : Fmt.Drawn)
    (out : List Fmt.RoundView) (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (ds : List Fmt.Drawn)
    (back : List OpenedColumn),
    tablesOf ((⟨name, a, 0, true, [], [], d₀⟩ : Played) :: out.map (saidPlayed name ⟨a, 1⟩)) = [] ∧
      fillCols (readsOf chain firstTree stored tree
        ((mergeEntries P.lay.lk 1 P.work).map fun e => { entry := e }) ds) back = .ok []

end ProofFile.Honest.K11
