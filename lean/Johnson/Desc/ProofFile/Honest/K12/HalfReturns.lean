-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HalfReturns.lean: the frame's play of a proximity test's half
returns, at every coins that the half's two parts are handed on which their readers agree, at every
list of as many challenges as the test has rounds, from wherever a run stands: under the two clauses
on the plan of FitsAll.lean in this folder. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean.
Its `play` runs a list of rounds (`Step`) at a list of challenges, from a state between two rounds
(`Mid`); it returns where its value is `.ok y` and not an error. A job J (`TestJob`, Test.lean in
this folder) is what a caller supplies for its test: `J.p` holds the test's parameters, among them
its place (`J.p.place`) and its stages (`J.p.nums.stages`). The half is `proverSideOfProximityTest J` (Parts.lean in
this folder): that place with the two parts (`Part`, the frame) `firstPart J` and `restPart J`. The
statements are written at this place and this list of two parts and do not name `proverSideOfProximityTest`. The two
readers are `firstRd J` (HalfSteps.lean in this folder) and `restCoins J` (Parts.lean): each maps
what its part is given (`Part.Coins`) to a family of coins (`TestCoins`, Test.lean). General in the
job and in the types V, W and X. Theorems only.

  `half_returns`: under the hypotheses below there is a y with `play l ds back m = .ok y`, where l
    is the list of rounds that `rowSteps` (the frame) builds for the two parts, at the coins c, from
    the place's declared rounds with their oracle messages (`laidOf J.p`,
    Johnson/Desc/K12/Law/ReadsK.lean). At every `name`, `v` and `back`
  `first_quiet`, `rest_quiet`, `steps_quiet`: neither part has a stop that speaks; so no round of
    the half's has one. In Lean: the fields `bad` and `hid` (the two stops of a `Part` and of a
    `Step`) of `firstPart J`, of `restPart J` and of every round that `rowSteps` builds for the two
    parts, at every list of declared rounds and all coins, return `none` at all arguments
  `part_quiet`: for every part p whose `bad` and `hid` return `none` at all arguments: so do `bad`
    and `hid` of every round in `p.steps` (the frame), at all its arguments

By what. `half_returns` is `play_returns` (PlayReturns.lean in this folder) from round number 0 on.
What that theorem needs comes from: `half_steps` (HalfSteps.lean): l has as many rounds as
`laidOf J.p`, and round number i holds the move `moveU J (coinsAtRound J c i) i`; `steps_quiet`;
`rowSteps_rows` (Johnson/Desc/ProofFile/Honest/Law/Steps.lean), with `first_moves` and `rest_moves`
(HalfSteps.lean) for the number of moves: round number i of l has the declared round and the oracle
messages of `laidOf J.p` at i; `msgAt_first` (CoinsAgree.lean in this folder), under hst, hA and hk:
at a round below `firstLen` the message at `firstRd J c.1` is the message at `restCoins J c.2.1`;
`fits_all` (FitsAll.lean), under hst, hS and hT: that message has the shape that the declared round
states (`Sending.fits`, the frame); `frontBy_zero` (PlayedTerm.lean in this folder). `steps_quiet`
is `part_quiet` at `first_quiet` and at `rest_quiet`; these three unfold the definitions.

Hypotheses of `half_returns`. hst: the job's list of stages is s :: t :: rest: two stages or more.
hk: k = h + g at the first: `s.k` is the sum of the fields h and g of `sgOf s`
(Johnson/Desc/K12/Law/ChainOf.lean, where g is k - h). hrs: `laidOf J.p` has `firstLen` (Parts.lean)
plus `restLen` (HalfSteps.lean) rounds: as many as the two parts have moves. hA: `Agree`
(CoinsAgree.lean) of the two families of coins `firstRd J c.1` and `restCoins J c.2.1`, at the
input in m, at `frontOf m` (PlayedTerm.lean: what precedes the test, read off m) and at s. hS: the
declared rounds ask the sorts that the term shows: `(laidOf J.p).map asked` is
`[] :: bodyItems s (t :: rest)` (`asked`, Johnson/Prover/Link/BodySorts.lean; `bodyItems`,
Johnson/Prover/Link/LinkItems.lean); the term is `testAll` (Test.lean). hT: `tablesFitB J = true`
(FitsAll.lean): each declared oracle message has the depth and the width of the tree that the term
sends. hl: ds has as many challenges as `laidOf J.p` has rounds. hS and hT are the two clauses of
FitsAll.lean; the others are further hypotheses.

Limits. All these hypotheses are assumed: none is proved here of any job. At the two readers `Agree`
(hA) has no value that meets it in the library yet; the two files that the limits of CoinsAgree.lean
name for it treat only a job whose fresh table has come earlier (`J.fresh` is `some _`).
`half_returns` states that the play returns some y: what y is, is not stated. Nothing on the
columns, on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlayReturns
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.K12.FitsAll
import Johnson.Desc.ProofFile.Honest.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

theorem first_quiet (J : TestJob W X) : (∀ f o, (firstPart J : Part V W X).bad f o = none) ∧
    ∀ u f o, (firstPart J : Part V W X).hid u f o = none := by
  unfold firstPart
  cases J.fresh <;> exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem rest_quiet (J : TestJob W X) : (∀ f o, (restPart J : Part V W X).bad f o = none) ∧
    ∀ u f o, (restPart J : Part V W X).hid u f o = none :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem part_quiet (p : Part V W X) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ u f o, p.hid u f o = none) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V)
    (c : p.Coins) : ∀ s ∈ p.steps name a rs v c,
      (∀ f o, s.bad f o = none) ∧ ∀ f o, s.hid f o = none := by
  intro s hs
  unfold Part.steps at hs
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
  refine ⟨fun f o => hb f o, fun f o => ?_⟩
  show (v.bind fun u => p.hid u f o) = none
  cases v with
  | none => rfl
  | some u => exact hh u f o

/-- No round of the half's has a stop that speaks. -/
theorem steps_quiet (J : TestJob W X) (name : String) (v : Option V)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) :
    ∀ s ∈ rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c,
      (∀ f o, s.bad f o = none) ∧ ∀ f o, s.hid f o = none := by
  intro s hs
  simp only [rowSteps, List.append_nil, List.mem_append] at hs
  rcases hs with hs | hs
  · exact part_quiet _ (first_quiet J).1 (first_quiet J).2 _ _ _ _ _ s hs
  · exact part_quiet _ (rest_quiet J).1 (rest_quiet J).2 _ _ _ _ _ s hs

/-- **The play of the half returns.** -/
theorem half_returns (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g) (name : String)
    (v : Option V)
    (hrs : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X)
    (hA : Agree J m.st.input (frontOf m) s (firstRd J c.1) (restCoins J c.2.1))
    (hS : (laidOf J.p).map asked = [] :: bodyItems s (t :: rest)) (hT : tablesFitB J = true)
    (hl : ds.length = (laidOf J.p).length) :
    ∃ y, play (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 (laidOf J.p)
      c) ds back m = .ok y := by
  obtain ⟨n1, n2⟩ := half_steps J s t rest hst name v (laidOf J.p) hrs c
  have hsum : ([(firstPart J : Part V W X), restPart J].map (·.moves.length)).sum =
      (laidOf J.p).length := by
    have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
      rw [first_moves]
      simp [movesFrom]
    have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
      rw [rest_moves J s t rest hst]
      exact (List.length_map _).trans List.length_range
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, l1, l2, hrs, Nat.add_zero]
  have hrows := rowSteps_rows name J.p.place v [(firstPart J : Part V W X), restPart J] 0
    (laidOf J.p) c hsum
  refine play_returns J (coinsAtRound J c) (byNo ds) _ 0 ds back m
    (fun i hi => by
      rw [Nat.zero_add]
      exact n2 i hi)
    (steps_quiet J name v _ c) (fun i hi => ?_) ⟨Nat.zero_le _, Nat.zero_le _, fun n hn => by
      omega⟩ (hl.trans n1.symm) fun n hn => by
      rw [Nat.zero_add]
      unfold byNo
      rw [List.getD_eq_getElem _ _ hn]
  -- the message of round i fits
  rw [Nat.zero_add, frontBy_zero]
  have hi' : i < (laidOf J.p).length := n1 ▸ hi
  have e := congrArg (·[i]?) hrows
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
    Option.map_some] at e
  have e' := Option.some.inj e
  have d1 : (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 (laidOf J.p)
      c)[i].decl = ((laidOf J.p)[i]).1 := congrArg (·.1) e'
  have d2 : (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 (laidOf J.p)
      c)[i].oracles = ((laidOf J.p)[i]).2 := congrArg (·.2.1) e'
  rw [d1, d2]
  have hmsg : msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i =
      msgAt J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds) i := by
    unfold coinsAtRound
    split
    · rename_i ci
      refine msgAt_first J _ _ _ _ _ s t rest hst hA i ?_
      rw [hst] at ci
      have : firstLen (s :: t :: rest) = 2 + s.k := rfl
      omega
    · rfl
  rw [hmsg]
  exact fits_all J _ _ _ _ s (t :: rest) hst hS hT i _ (List.getElem?_eq_getElem hi')

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.first_quiet
#print axioms ProofFile.Honest.K12.rest_quiet
#print axioms ProofFile.Honest.K12.part_quiet
#print axioms ProofFile.Honest.K12.steps_quiet
#print axioms ProofFile.Honest.K12.half_returns
