-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Text.lean: the text of a proximity test's second part, cut off
the whole test's text: all that a prover shows from the first switch on, as a function of the
verifier's state behind the first fold, of the first stage's rows, of the trees that hold them, of
coins and of the sampled challenges. The whole test's text is `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean); the second part's is `restText`. Definitions, none marked
`noncomputable`, and equations between texts. General in every argument; `restText`, `restEnd` and
`stagesAll_cut` are written for a first stage with the number 0.

Why. `stagesAll` begins at the first fold and computes the verifier's state after that fold from its
own fold's rounds. The book (`ProverCoinCounts`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean: public
data that goes with a description) says how many rounds each part of a prover's side has. By the
numbers that `cutsOf` (Johnson/Desc/ProofFile/Honest/BookOf.lean) computes for it, a proximity
test's rounds are divided after the first fold; the two parts are in
Johnson/Desc/ProofFile/Honest/K12/Parts.lean. Whoever wants the second part's rounds at other rows
than those from which the first fold's rounds were computed needs the state after the fold as a
parameter.

In the list: a text is a value of `BOut` (Johnson/Prover/Link/BodyAll.lean): the rounds (`rs`), for
each round the written column of the tree that it sends (`tr`), and the groups of opened columns
(`gs`). A test has a list of stages (`Fmt.M1.Stage`), numbered from 0. Every stage but the last has
a fold and then a switch, which leads to the next stage; both have the stage's number, so the second
fold has the number 1. "Behind" a round means after it. p holds the numbers of the test's place
(`P12`, Johnson/Desc/K12/Frame.lean), l the declared rounds with their oracle messages (`Laid`, same
file). o is the number of the first fold's first round. D gives the sampled challenges by the
round's number. t and t₁ are states of the verifier (`T12`, Johnson/Desc/K12/Join.lean). P is a
state of the prover (`PS`, Johnson/Prover/Link/BodyState.lean), which holds the stage's rows. The
coins are K (`BCoins`, BodyAll.lean), and the coins' letters are its three fields: `W s j` holds the
coefficients from which fold number j computes its rounds, and which the switch before that fold
packs into the prover's next state; `new j` and `fr j` go into switch number j. The trees in front
are the argument trees (`Tree`, Stages.lean: a depth, and a written column at each position). The
groups of columns at the first round of positions are `aGroups cur o trees D` (Stages.lean): for
each of these trees, its columns at the positions sampled in the first switch's second round.

  `stagesAll_cut`: `stagesAll` at the stage number 0 and at a list of two stages or more is the
    first fold's rounds (`aFold`), and then `restText` at the state that these rounds leave
    (`aRec1`). In `tr` each of the fold's rounds has the empty column; `gs` is that of `restText`.
    No hypothesis
  `restText_congr`: the text from the first switch on reads the coins' letters from the second fold
    on alone: the first fold's coefficients are read by no term of it. The Lean has less than the
    first clause: `restText` reads `K.new 0` and `K.fr 0`, the first switch's coins (`aNext` at the
    number 0), and `SameFrom 1` asks that `new` and `fr` agree as whole functions. What is proved:
    the text is the same whatever `K.W s 0` is
  `restText_trees`: and the trees in front through the groups of columns at the first round of
    positions alone. As stated in Lean, the two theorems are equations, each for `restText` and for
    `restEnd`: `restText_congr` between K and K' where `SameFrom 1 K K'` holds; `restText_trees`
    between two lists of trees at which `aGroups cur o` returns the same groups
  `stagesAll_congr`, `stagesEnd_congr`: where `SameFrom j K K'` holds, `stagesAll` from the stage
    number j on is the same at K and at K'; so is `stagesEnd`
  `SameFrom n K K'`: a definition: K and K' agree from fold number n on: in `W s j` at every s and
    every j with `n ≤ j`, and in `new` and `fr` as whole functions, so at switch number 0 too. "The
    coins' letters from the second fold on" are what `SameFrom 1` compares
  `restText`: a definition: the first switch, piece by piece as in `stagesAll` (`aNext`, `aCol`,
    `aAns`, `aSwitch`, `aRec3`, `aGroups`, all in Stages.lean), then `stagesAll` from the second
    stage on. The state t₁ is an argument
  `EndAt`: a structure: the values at the last stage: its number `j`, the stage `cur` with its
    sizes, the number `o` of its first round, the verifier's state `t` and the prover's state `P`
    there
  `stagesEnd`, `restEnd`: definitions: the `EndAt` of a list of stages, by the recursion of
    `stagesAll`; the same from the first switch on, at the arguments at which `restText` calls
    `stagesAll`
  `claimAtEnd`: a definition: the claim that is left at the last stage, by the expression that
    `lastOut` (BodyAll.lean) has for it. No theorem of this file compares the two

By what. Every proof unfolds definitions of this file and of Stages.lean. `stagesAll_cut`:
`stagesAll` and `restText`, with `List.append_assoc`. `stagesAll_congr` and `stagesEnd_congr`: by
recursion on the list of stages; at each stage `aFold` and `aNext` are unfolded and rewritten by the
fields of `SameFrom`. `restText_congr` calls these two at the stage number 1. `restText_trees`:
`aRec3` is unfolded and rewritten by the hypothesis.

Limits. Texts only; the equations hold at all arguments, also at such as no run reaches. t₁ is any
value of `T12`, nothing ties the trees to P, and no distribution on K is stated. Where a part of the
description (`guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) rejects, the state in hand is kept, as in
`stagesAll`. For the whole folder Johnson/Desc/ProofFile/Honest/K12/Sim/, said once, here, in its
lowest file: no file of this folder states a security property by itself: each holds definitions,
lemmas, guards and tests. No property is claimed. Nothing on completeness or on soundness.
-/
import Johnson.Desc.K12.Honest.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Prox (BaseClaim)
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- **All that is shown from the first switch on.** t₁: the verifier's state after the first fold.
P: the prover's state at the first stage. trees: the trees that hold P's rows. o: the number of the
first fold's first round. All four are arguments: nothing ties one to another. -/
def restText (p : P12) (K : BCoins) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t₁ : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn) : BOut :=
  let Q := aNext K rest.isEmpty 0 cur next o P D
  let col := aCol rest.isEmpty next Q
  let rs := aSwitch cur o D (aAns p 0 cur next o D t₁ Q)
  let R := stagesAll p K rest 1 next (l.drop (cur.k + 3))
    (o + ((sgOf cur).h + (sgOf cur).g) + 3) (aRec3 p rest.isEmpty 0 cur next l o trees D t₁ rs) Q
    [((sgOf next).C.a, col)] D
  ⟨rs ++ R.rs, [col, fun _ => []] ++ R.tr, aGroups cur o trees D ++ R.gs⟩

/-- **The whole text is the first fold's rounds, and then the text from the first switch on**, at
the state that these rounds leave: `aRec1` at `aFold`. At the stage number 0. In `tr` each of the
fold's rounds has the empty column; the fold adds no group to `gs`. -/
theorem stagesAll_cut (p : P12) (K : BCoins) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn) :
    stagesAll p K (next :: rest) 0 cur l o t P trees D =
      ⟨aFold K 0 cur o P (rowOf t) D ++
          (restText p K cur next rest l o (aRec1 p 0 cur l t (aFold K 0 cur o P (rowOf t) D)) P
            trees D).rs,
        (aFold K 0 cur o P (rowOf t) D).map (fun _ _ => []) ++
          (restText p K cur next rest l o (aRec1 p 0 cur l t (aFold K 0 cur o P (rowOf t) D)) P
            trees D).tr,
        (restText p K cur next rest l o (aRec1 p 0 cur l t (aFold K 0 cur o P (rowOf t) D)) P
          trees D).gs⟩ := by
  simp only [stagesAll, restText, List.append_assoc]

/-- The values at the last stage: its number, the stage, the number of its first round, the
verifier's state and the prover's state there. -/
structure EndAt where
  j : ℕ
  cur : Fmt.M1.Stage
  o : ℕ
  t : T12
  P : PS

/-- The values at the last stage, by the recursion of `stagesAll`. -/
def stagesEnd (p : P12) (K : BCoins) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS →
    List Tree → (ℕ → Fmt.Drawn) → EndAt
  | [], j, cur, _, o, t, P, _, _ => ⟨j, cur, o, t, P⟩
  | next :: rest, j, cur, l, o, t, P, trees, D =>
    let rf := aFold K j cur o P (rowOf t) D
    let Q := aNext K rest.isEmpty j cur next o P D
    let col := aCol rest.isEmpty next Q
    let t₁ := aRec1 p j cur l t rf
    let rs := aSwitch cur o D (aAns p j cur next o D t₁ Q)
    stagesEnd p K rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3) (aRec3 p rest.isEmpty j cur next l o trees D t₁ rs) Q
      [((sgOf next).C.a, col)] D

/-- The same from the first switch on: `stagesEnd` at the arguments at which `restText` calls
`stagesAll`. -/
def restEnd (p : P12) (K : BCoins) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t₁ : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn) : EndAt :=
  let Q := aNext K rest.isEmpty 0 cur next o P D
  let col := aCol rest.isEmpty next Q
  let rs := aSwitch cur o D (aAns p 0 cur next o D t₁ Q)
  stagesEnd p K rest 1 next (l.drop (cur.k + 3))
    (o + ((sgOf cur).h + (sgOf cur).g) + 3) (aRec3 p rest.isEmpty 0 cur next l o trees D t₁ rs) Q
    [((sgOf next).C.a, col)] D

/-! ## The first fold's coefficients are read by no term behind the first fold -/

/-- Two values of `BCoins` agree from the fold number n on: in `W s j` at every s and every j with
`n ≤ j`, and in `new` and `fr` as whole functions. -/
structure SameFrom (n : ℕ) (K K' : BCoins) : Prop where
  W : ∀ s j, n ≤ j → K.W s j = K'.W s j
  new : K.new = K'.new
  fr : K.fr = K'.fr

theorem stagesAll_congr (p : P12) {K K' : BCoins} : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), SameFrom j K K' →
    stagesAll p K rest j cur l o t P trees D = stagesAll p K' rest j cur l o t P trees D
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, trees, D, h => by
    have hn : SameFrom (j + 1) K K' := ⟨fun s i hi => h.W s i (by omega), h.new, h.fr⟩
    simp only [stagesAll, aFold, aNext, h.W _ j le_rfl, h.W _ (j + 1) (by omega), h.new, h.fr,
      stagesAll_congr p rest (j + 1) next _ _ _ _ _ D hn]

theorem stagesEnd_congr (p : P12) {K K' : BCoins} : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), SameFrom j K K' →
    stagesEnd p K rest j cur l o t P trees D = stagesEnd p K' rest j cur l o t P trees D
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, trees, D, h => by
    have hn : SameFrom (j + 1) K K' := ⟨fun s i hi => h.W s i (by omega), h.new, h.fr⟩
    simp only [stagesEnd, aFold, aNext, h.W _ j le_rfl, h.W _ (j + 1) (by omega), h.new, h.fr,
      stagesEnd_congr p rest (j + 1) next _ _ _ _ _ D hn]

/-- **The text from the first switch on reads the coins' letters from the second fold on alone.** As
stated: where `SameFrom 1 K K'` holds, `restText` is the same at K and K', and so is `restEnd`.
`SameFrom 1` asks that `new` and `fr` agree as whole functions, and the text reads `K.new 0` and
`K.fr 0`, the first switch's coins: what is proved is that it is the same whatever `K.W s 0` is. -/
theorem restText_congr (p : P12) {K K' : BCoins} (h : SameFrom 1 K K') (cur next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (o : ℕ) (t₁ : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) :
    restText p K cur next rest l o t₁ P trees D = restText p K' cur next rest l o t₁ P trees D ∧
      restEnd p K cur next rest l o t₁ P trees D = restEnd p K' cur next rest l o t₁ P trees D := by
  constructor
  · simp only [restText, aNext, h.W _ 1 le_rfl, h.new, h.fr,
      stagesAll_congr p rest 1 next _ _ _ _ _ D h]
  · simp only [restEnd, aNext, h.W _ 1 le_rfl, h.new, h.fr,
      stagesEnd_congr p rest 1 next _ _ _ _ _ D h]

/-- **The text from the first switch on reads the trees in front through the groups of columns at
the first round of positions alone.** As stated: at two lists of trees at which `aGroups cur o`
returns the same groups, `restText` is the same, and so is `restEnd`. -/
theorem restText_trees (p : P12) (K : BCoins) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t₁ : T12) (P : PS) (trees trees' : List Tree) (D : ℕ → Fmt.Drawn)
    (h : aGroups cur o trees D = aGroups cur o trees' D) :
    restText p K cur next rest l o t₁ P trees D = restText p K cur next rest l o t₁ P trees' D ∧
      restEnd p K cur next rest l o t₁ P trees D = restEnd p K cur next rest l o t₁ P trees' D := by
  constructor
  · simp only [restText, aRec3, h]
  · simp only [restEnd, aRec3, h]

/-- The claim that is left at the last stage, by the expression that `lastOut`
(Johnson/Prover/Link/BodyAll.lean) has for it, at the row `rowOf e.t`. Where the stage or its claim
is not found: `⟨#[], #[], (0, 0, 0)⟩`, a claim without a coefficient and with the target 0. At that
value `EndTrue` (Sim/Spec.lean) reads 0 + 0 = 0: it holds whatever the prover's state is. -/
def claimAtEnd (p : P12) (e : EndAt) : BaseClaim :=
  ((stageAt p e.j e.cur).bind fun c => claimAt e.t.st.codes c (rowOf e.t)).getD
    ⟨#[], #[], (0, 0, 0)⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stagesAll_cut
#print axioms ProofFile.Honest.K12.stagesAll_congr
#print axioms ProofFile.Honest.K12.stagesEnd_congr
#print axioms ProofFile.Honest.K12.restText_congr
#print axioms ProofFile.Honest.K12.restText_trees
#print axioms ProofFile.Honest.K12.restText
#print axioms ProofFile.Honest.K12.EndAt
#print axioms ProofFile.Honest.K12.stagesEnd
#print axioms ProofFile.Honest.K12.restEnd
#print axioms ProofFile.Honest.K12.SameFrom
#print axioms ProofFile.Honest.K12.claimAtEnd
