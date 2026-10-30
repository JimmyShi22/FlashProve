-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FormDraws.lean: the seven clauses on the form of a proximity
test's own challenges (`FormAsks`, PlanB.lean in this folder) hold at every list of challenges that
the test's declared rounds can sample, under four clauses on the plan. That a list can be sampled
means that `drawsFit`, a test of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean), is true of
the declared rounds and the list. `FormAsks` is one of the four hypotheses of `accepts_of_plan`
(PlanB.lean), a theorem on the acceptance of the test's block (`proximityTestKind guardedProximityTestParts p`,
Johnson/Desc/K12/Frame.lean). The job, the prover's input, the front and the coins are free
parameters of the main theorem. Statements and proofs.

In the list: the plan is p, the test's parameters (`P12`, Johnson/Desc/K12/Frame.lean; also called
the place), with the list of stages `p.nums.stages`. A stage (`Fmt.M1.Stage`) has a main code C, a
mask code Z and the numbers k, h and t. `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean; type `Laid`)
pairs each declared round (`Fmt.DeclaredRound`) with its oracle messages, so the declared rounds are
`(laidOf p).map (·.1)`. Round 0 is the batching's round "BAT"; `laidS p` is the list without it. Of
`laidS p`, `FormAsks` takes the first 1 + k rounds for the first stage's fold, the next two for the
first switch, which leads from the first stage to the second, and the others for the later stages.
The switch's two are `dS`, the round of the seed, and `dC`, the round of positions (`lettersOf`,
AllB.lean in this folder). A challenge (`Fmt.Drawn`) is what one round samples: elements, positions,
matrix entries and optionally a digest. `byNo ds` (PlayedTerm.lean in this folder) reads a list of
challenges by the round's number; beyond the list's end it gives the empty challenge. The term is
`testAll` (Test.lean in this folder): it defines a test's rounds, each round's tree and the opened
columns as a function of a job (`TestJob`: what a caller supplies for its test), the prover's input,
the front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test), the coins
(`TestCoins`) and the challenges by number. `asked` (Johnson/Prover/Link/BodySorts.lean) lists a
declared round's items without the roots; `sortsOf` (Johnson/Prover/Link/LinkItems.lean) lists the
sorts of the items in a round (`Fmt.RoundView`: items and a challenge).

  `formAsks_of_draws`: under the three hypotheses below, `FormAsks J w fr C (byNo ds)` holds. Its
    seven clauses: `roundsFit` (Johnson/Desc/Block.lean) passes at "BAT" (`bat`), at the term's
    rounds of the first fold (`fold`) and at the term's rounds of the first switch, each without its
    digest (`switch`); `FitFrom` (Johnson/Prover/Link/BodyFit.lean) holds from the second stage on
    (`later`); the positions in the challenge of `dC` are below 2 ^ C.a (`range`) and are t in
    number (`count`), at the first stage's C and t; the element that is read as the seed's factor
    passes `okE` (OnBytes/Field/Ext.lean): its three words are below the prime (`words`)
  `FormPub p a next rest`: a structure of propositions: the four clauses on the plan. `hk`: h ≤ k at
    the first stage. `sorts`: the declared rounds ask just the sorts of items that the term shows
    ("BAT": none). `cutSw`: the test on the switch's two declared rounds (`switchCut`,
    Johnson/Prover/Link/FormSwitch.lean), at the first stage's C.a. `poss`: the entry of `dC` states
    as many positions as the first stage's t. As Lean has it, `sorts` equates `asked` of the
    declared rounds with `[] :: bodyItems a (next :: rest)` (Johnson/Prover/Link/LinkItems.lean);
    that the term's rounds have these sorts is `test_sorts` (FitsAll.lean in this folder). The first
    stage is the parameter a: that a, next and rest are the plan's stages is no clause of `FormPub`
  `fitOne_of_draw`, `fitFromB_of_draws`, `fitFrom_of_draws`: the frame's test on challenges gives
    what `FitFrom` says. For one declared round d: `drawFit d x` gives `fitOneB d x`
    (Johnson/Desc/K12/Honest/FitFromB.lean). For a list l of type `Laid`: `drawsFit` at a list whose
    element number n is D (o + n) gives `fitFromB D l o`, and `drawsFit` at ds gives
    `FitFrom (byNo ds) l 0`
  `FitFrom.take`: `FitFrom D l o` goes over to the first m rounds of l
  `roundsFit_sorts`: where `FitFrom D l o` holds, a list rs of rounds passes `roundsFit` at the
    declared rounds of l if its round number n has the challenge D (o + n) and `sortsOf` of rs is
    `asked` of l. Johnson/Prover/Link/BodySorts.lean has lemmas of these two names in its own
    namespace: `FitFrom.take` with the same statement, `roundsFit_sorts` with the equation turned
    round
  `aFold_sorts`: `sortsOf` of a fold's rounds (`aFold`, Johnson/Desc/K12/Honest/Stages.lean) is
    `[.e]`, then h + g times `[.e, .e]`, with h and g of `sgOf` of the stage
    (Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. No hypothesis

By what. `fitOne_of_draw` unfolds the two tests: `drawFit` has the clauses of `fitOneB` and one
more, on the digest. `fitFrom_of_draws` calls `fitFrom_of_B`
(Johnson/Desc/K12/Honest/FitFromB.lean). `roundsFit_sorts` calls `roundsFit_of`
(Johnson/Prover/Link/BodyFit.lean). `aFold_sorts` calls `showRV_items`
(Johnson/Prover/Link/LinkItems.lean). `formAsks_of_draws` takes `FitFrom` at all declared rounds
from `fitFrom_of_draws` and cuts it by `FitFrom.drop` (BodyFit.lean) and `FitFrom.take`; it cuts the
clause `sorts` in the same way, with h + g = k from `kk_eq` (BodySorts.lean). `bat`, `fold` and
`switch` follow by `roundsFit_sorts`, with `drawn_fold` (PlayedTerm.lean), `two_of_length`
(Johnson/Prover/Link/StepPlanOk.lean) and `H2K.Onto.roundsFit_noDigest`
(Johnson/Desc/K12/Law/TrOnto.lean). `later` is a cut of `FitFrom`. `range` and `count` are read off
`roundsFit` at the switch's rounds by `roundsFit_iff` (Johnson/Top/H0/StepLaws/RoundsFit.lean), with
`cutSw` and `poss`. `words` follows from the second half of `FitFrom`, on the elements' words, and
`K1.okE_ofTriple` (Johnson/Desc/K1/Law/OkView.lean).

Hypotheses of `formAsks_of_draws`. hst: the list of stages of the job's plan is a :: next :: rest:
two stages or more. P: `FormPub J.p a next rest`. hd: `drawsFit` is true of the declared rounds and
ds; it is false where the two lists differ in length.

Limits.
- `FormPub` is a hypothesis: it is shown of no place here. It reads no state, no coin and no
  challenge. FormPubAt.lean in this folder writes it as a test with code (`formPubB`) and evaluates
  that test at four written places.
- `formAsks_of_draws` does not say that the test accepts at every list that can be sampled: the
  other two structures that the theorem on the acceptance (`accepts_of_plan`) has as hypotheses,
  `ShapeAsks` and `DataAsks`, are stated at the same challenges (the state after the batching and
  after the first fold; what the rows say), and nothing here carries them from one list to all.
- The list of declared rounds is `(laidOf p).map (·.1)`. That it is the block's own list, where the
  block's test on the plan (`planOk`) passes: FormRounds.lean (not in the library yet) in this
  folder.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.K12.Law.TrOnto
import Johnson.Desc.K1.Law.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

theorem fitOne_of_draw (d : Fmt.DeclaredRound) (x : Fmt.Drawn) (h : drawFit d x = true) :
    fitOneB d x = true := by
  unfold drawFit at h
  unfold fitOneB
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, -⟩ := h
  refine ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, fun t ht => ?_⟩, a6⟩, fun y hy => ?_⟩
  · rcases a5 t ht with (u | u) | u
    · exact Or.inl u
    · exact Or.inr (Or.inl u)
    · exact Or.inr (Or.inr u)
  · obtain ⟨⟨b1, b2⟩, b3⟩ := a7 y hy
    unfold ltE
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨b1, b2⟩, b3⟩

theorem fitFromB_of_draws (D : ℕ → Fmt.Drawn) : ∀ (l : Laid) (Rs : List Fmt.Drawn) (o : ℕ),
    drawsFit (l.map (·.1)) Rs = true → (∀ n R, Rs[n]? = some R → R = D (o + n)) →
    fitFromB D l o = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by cases h
  | d :: l, R :: Rs, o, h, hD => by
    have h' : (drawFit d.1 R && drawsFit (l.map (·.1)) Rs) = true := h
    rw [Bool.and_eq_true] at h'
    rw [fitFromB, Bool.and_eq_true]
    refine ⟨?_, fitFromB_of_draws D l Rs (o + 1) h'.2 fun n R' hn => ?_⟩
    · have e : R = D o := hD 0 R rfl
      rw [← e]
      exact fitOne_of_draw _ _ h'.1
    · rw [hD (n + 1) R' hn]
      congr 1
      omega

/-- Where `drawsFit` is true of the declared rounds of l and the list ds, `FitFrom (byNo ds) l 0`
holds. -/
theorem fitFrom_of_draws (l : Laid) (ds : List Fmt.Drawn)
    (h : drawsFit (l.map (·.1)) ds = true) : FitFrom (byNo ds) l 0 :=
  fitFrom_of_B _ _ _ (fitFromB_of_draws (byNo ds) l ds 0 h fun n R hn => by
    rw [Nat.zero_add]
    unfold byNo
    rw [List.getD_eq_getElem?_getD, hn]
    rfl)

theorem FitFrom.take {D : ℕ → Fmt.Drawn} {l : Laid} {o : ℕ} (h : FitFrom D l o) (m : ℕ) :
    FitFrom D (l.take m) o := fun n d hd => by
  rw [List.getElem?_take] at hd
  split at hd
  · exact h n d hd
  · cases hd

/-- Where `FitFrom D l o` holds, rounds rs pass `roundsFit` at the declared rounds of l if round
number n has the challenge D (o + n) and `sortsOf` of rs is `asked` of l. -/
theorem roundsFit_sorts {D : ℕ → Fmt.Drawn} (l : Laid) (o : ℕ) (rs : List Fmt.RoundView)
    (hF : FitFrom D l o) (hd : ∀ (n : ℕ) (r : Fmt.RoundView), rs[n]? = some r → r.drawn = D (o + n))
    (hs : rs.map sortsOf = l.map asked) : roundsFit (l.map (·.1)) rs = true := by
  refine roundsFit_of l o rs hF ?_ hd fun n r d h1 h2 => ?_
  · have := congrArg List.length hs
    rwa [List.length_map, List.length_map] at this
  · have e := congrArg (·[n]?) hs
    simp only [List.getElem?_map, h1, h2, Option.map_some] at e
    exact Option.some.inj e

/-- The four clauses on the plan. p: the test's parameters. a, next, rest: stages; that they are the
stages of p is no clause here. `hk`: h ≤ k at a. `sorts`: `asked` of the declared rounds is
`[] :: bodyItems a (next :: rest)`. `cutSw`: `switchCut` is true of the first switch's two declared
rounds, at the C.a of a. `poss`: the entry of the second of the two states a.t positions. -/
structure FormPub (p : P12) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Prop where
  hk : a.h ≤ a.k
  sorts : (laidOf p).map asked = [] :: bodyItems a (next :: rest)
  cutSw : switchCut (sgOf a).C.a (lettersOf p a next).dS (lettersOf p a next).dC = true
  poss : (lettersOf p a next).dC.entry.poss = a.t

theorem aFold_sorts (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (P : PS) (row : GroupRow)
    (D : ℕ → Fmt.Drawn) : (aFold K j cur o P row D).map sortsOf =
      [.e] :: List.replicate ((sgOf cur).h + (sgOf cur).g) [.e, .e] := by
  unfold aFold foldShown
  rw [List.map_cons, showRV_items]
  rfl

/-- **The seven clauses on the challenges' form hold at every list that can be sampled.** hst: two
stages or more. P: the four clauses on the plan. hd: the list ds can be sampled. -/
theorem formAsks_of_draws (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (P : FormPub J.p a next rest)
    (hd : drawsFit ((laidOf J.p).map (·.1)) ds = true) : FormAsks J w fr C (byNo ds) := by
  have hA : stA J.p = a := by
    unfold stA
    rw [hst]
    rfl
  have hN : stN J.p = next := by
    unfold stN
    rw [hst]
    rfl
  have hR : J.p.nums.stages.drop 2 = rest := by
    rw [hst]
    rfl
  have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq P.hk
  have F0 := fitFrom_of_draws (laidOf J.p) ds hd
  have F1 : FitFrom (byNo ds) (laidS J.p) 1 := by
    have := F0.drop 1
    rwa [Nat.zero_add] at this
  have S1 : (laidS J.p).map asked = ([.e] :: List.replicate a.k [.e, .e]) ++
      ([[], [.answer]] ++ bodyItems next rest) := by
    have e := congrArg (List.drop 1) P.sorts
    rw [← List.map_drop] at e
    refine e.trans ?_
    show bodyItems a (next :: rest) = _
    rw [bodyItems, kk, List.append_assoc]
  have hlenF : ([Fmt.Item.e] :: List.replicate a.k [Fmt.Item.e, Fmt.Item.e]).length = 1 + a.k := by
    rw [List.length_cons, List.length_replicate, Nat.add_comm]
  -- the switch's two declared rounds
  have S2 : (((laidS J.p).drop (1 + a.k)).take 2).map asked = [[], [.answer]] := by
    rw [List.map_take, List.map_drop, S1, List.drop_left' hlenF]
    rfl
  have h2 : ((((laidS J.p).drop (1 + a.k)).take 2).map (·.1)).length = 2 := by
    have := congrArg List.length S2
    rw [List.length_map] at this ⊢
    exact this
  have two : [(lettersOf J.p a next).dS, (lettersOf J.p a next).dC] =
      (((laidS J.p).drop (1 + a.k)).take 2).map (·.1) := (two_of_length _ h2).symm
  have hsw : roundsFit [(lettersOf J.p a next).dS, (lettersOf J.p a next).dC]
      (rsAt J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
        (J.recB w fr (byNo ds 0)) (J.first w fr C) (byNo ds)) = true := by
    rw [two]
    refine roundsFit_sorts _ (1 + (1 + a.k)) _ ((F1.drop (1 + a.k)).take 2) (fun n r h => ?_) ?_
    · match n, h with
      | 0, h =>
        obtain rfl := Option.some.inj h
        show byNo ds (1 + 1 + ((sgOf a).h + (sgOf a).g)) = _
        rw [kk]
        congr 1
        omega
      | 1, h =>
        obtain rfl := Option.some.inj h
        show byNo ds (1 + 2 + ((sgOf a).h + (sgOf a).g)) = _
        rw [kk]
        congr 1
        omega
    · rw [S2]
      rfl
  obtain ⟨-, fC⟩ : RoundFits (lettersOf J.p a next).dS _ ∧ RoundFits (lettersOf J.p a next).dC
      ⟨_, byNo ds (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩ := by
    have k := (roundsFit_iff _ _).1 hsw
    cases k with
    | cons k1 k2 =>
      cases k2 with
      | cons k3 _ => exact ⟨k1, k3⟩
  have hlog : (lettersOf J.p a next).dC.entry.logN = (sgOf a).C.a := by
    have c := P.cutSw
    unfold switchCut at c
    simp only [Bool.and_eq_true, beq_iff_eq] at c
    exact c.1.1.1.1.1.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [tFold, hA, hN, hR]
  · -- `bat`: the round "BAT"
    refine roundsFit_sorts ((laidOf J.p).take 1) 0 _ (F0.take 1) (fun n r h => ?_) ?_
    · match n, h with
      | 0, h =>
        obtain rfl := Option.some.inj h
        rfl
    · rw [List.map_take, P.sorts]
      rfl
  · -- `fold`: the first fold's rounds
    refine roundsFit_sorts ((laidS J.p).take (1 + a.k)) 1 _ (F1.take _)
      (fun n r h => drawn_fold _ _ _ _ _ _ _ n r h) ?_
    rw [aFold_sorts, kk, List.map_take, S1, List.take_left' hlenF]
  · -- `switch`: the first switch's two rounds
    rw [H2K.Onto.roundsFit_noDigest]
    exact hsw
  · -- `later`: from the second stage on
    have := F1.drop (a.k + 3)
    rw [kk]
    rwa [show 1 + (a.k + 3) = 1 + a.k + 3 from by omega] at this
  · intro x hx
    have := fC.below x hx
    rwa [hlog] at this
  · exact fC.count.trans P.poss
  · -- `words`: the seed's factor
    rw [List.getD_eq_getElem?_getD]
    cases he : ((byNo ds (1 + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple)[bitsAt J.p 0
        next (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1
          (J.recB w fr (byNo ds 0)) (J.first w fr C) (byNo ds))]? with
    | none => rfl
    | some e =>
      rw [List.getElem?_map] at he
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 he
      obtain ⟨d, hdd⟩ : ∃ d, (laidS J.p)[1 + a.k]? = some d := by
        have hl : 1 + a.k < (laidS J.p).length := by
          have := congrArg List.length S1
          rw [List.length_map, List.length_append, hlenF] at this
          simp only [List.length_append, List.length_cons, List.length_nil] at this
          omega
        exact ⟨_, List.getElem?_eq_getElem hl⟩
      have hx' := (F1 (1 + a.k) d hdd).2 x (by
        rw [kk] at hx
        rw [show 1 + (1 + a.k) = 1 + 1 + a.k from by omega]
        exact List.mem_of_getElem? hx)
      exact K1.okE_ofTriple x hx'

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.aFold_sorts
#print axioms ProofFile.Honest.K12.formAsks_of_draws
#print axioms ProofFile.Honest.K12.fitOne_of_draw
#print axioms ProofFile.Honest.K12.fitFromB_of_draws
#print axioms ProofFile.Honest.K12.fitFrom_of_draws
#print axioms ProofFile.Honest.K12.FitFrom.take
#print axioms ProofFile.Honest.K12.roundsFit_sorts
#print axioms ProofFile.Honest.K12.FormPub
