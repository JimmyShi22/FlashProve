-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CoinsAgree.lean: the messages of a proximity test's first part
read of the coins the hiding polynomial's coefficients and what the first stage's message holds of
the members' stretches, and, where the first fold sends its own fresh table, that table's tails:
nothing else. As a theorem this is `msgAt_first`: two families of coins that agree on these
(`Agree`) give the same message in the round "BAT" and in each round of the first fold. It is proved
where the test has two stages or more, at every job, input, front and challenges. The test's two
parts read their coins by two readers (Parts.lean in this folder), and the term (`testAll`,
Test.lean) is written at one family of coins. So: where the two readers agree on these, all rounds
as played are the rounds of one term. This file proves the step on the first part's messages only;
the conclusion on all rounds as played is `played_term` (PlayedTerm.lean in this folder), under
further hypotheses. Definitions and theorems.

In the list: a proximity test is the kind `KindName.K12`. A job J (`TestJob`, Test.lean in this
folder) is what a caller supplies for its test. w is the prover's input. A front fr (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean) is what the job's functions are given of the run before the
test. D gives the sampled challenges by the round's number; "BAT", the batching round, is round 0. A
family of coins K (`TestCoins`, Test.lean) has four fields, each a function of numbers: `hide` (the
hiding polynomial's coefficients), `tails` (the fresh table's rows' tails), `mem` (the members'
stretches, by the member's number) and `rest` (the switches' coins). A stretch (`Stretch`,
Coins.lean in this folder) is a run of coins, read by number. The members are the group's oracle
messages (`J.members`). The term is `testAll J w fr K D`: its field `rs` lists the rounds, its field
`tr` has a tree's column for each round. The message of round number i is `msgAt J w fr K D i`
(Parts.lean), taken from the term. The stages are the list `J.p.nums.stages`. k is a stage's field
`k`; h and g are those of `sgOf s` (Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. The first
stage's state is `J.first w fr K` (of type `PS`, Johnson/Prover/Link/BodyState.lean). The first fold
sends its own fresh table where `J.fresh` is `none`; where it is `some _`, the table has come
earlier. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A part (`Part`, the frame) is the
prover's side of some rounds in a row: the first part is `firstPart J` ("BAT" and the first fold),
the second is `restPart J` (both Parts.lean). A part's reader makes a family of coins of what the
part is given: the first part's is written inside `firstPart J` (by name: `firstRd J`,
HalfSteps.lean in this folder), the second's is `restCoins J` (Parts.lean). A book (`ProverCoinCounts`, the
frame) is public data; an entry of it (`Ahead`) is a block of its owner's coins, from a start on,
that one other part is given too, marked as spent or as carried.

  `msgAt_first`: under the hypotheses below, `msgAt J w fr K₁ D i` is `msgAt J w fr K₂ D i`: the
    message of round i is the same at both families
  `Agree J w fr s K₁ K₂`: two families of coins give the same coefficients under the library's names
    (`hideAt`), and the same message of the first stage (`μOf`: the main table beside the carried
    mask table, on the stage's own finite index); and the same tails of the fresh table, where the
    first fold sends it itself. A structure of three statements: `hide`, `table`, `tails`. `hideAt`
    (Coins.lean), here at h + g, indexes the coefficients by the library's type `HIdx`; `μOf`
    (Johnson/Prover/Link/BodyState.lean) is applied to `J.first w fr K₁` and `J.first w fr K₂`;
    `tails` compares the two fields `tails` as whole functions. s is a free parameter; `msgAt_first`
    takes it as the first of the job's stages
  `test_cut`: where the stages are s :: t :: rest: the term's `rs` is the round "BAT" (no item, the
    challenge D 0), then `foldOf J w fr K D s`, then a further list. Its `tr` is the empty column
    for "BAT", then the empty column for each round of `foldOf`, then a further list; where
    `J.fresh` is `none`, the column at the fold's first round is instead `freshCol` (Test.lean) at
    the first stage's state
  `foldOf J w fr K D s`: a definition: the first fold's rounds at the family K: `aFold`
    (Johnson/Desc/K12/Honest/Stages.lean) at stage number 0, the stage s and 1 as the number of its
    first round; at `coinsOf` (Coins.lean) of `K.hide` and `K.rest`, at the state `J.first w fr K`,
    and at the claim's row (`rowOf`, Johnson/Prover/Link/BodyAll.lean) of the state after the
    batching (`J.recB w fr (D 0)`, Test.lean)
  `foldOf_agree`: under `Agree`, `foldOf` is the same list at both families
  `length_foldOf`: `foldOf` has 1 + (h + g) rounds

By what. `test_cut` unfolds `testAll` and one step of `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean). `foldOf_agree` unfolds `aFold`: of the state it takes `μOf`
only, and of the coins the field `W` at stage number 0, which `coinsOf` sets to `hideAt` of `hide`.
`length_foldOf` unfolds `foldShown` (Johnson/Desc/K12/Honest/Fold.lean) and calls `length_showRV`
(Johnson/Prover/Link/FoldSay.lean). `msgAt_first` calls these three and unfolds `msgAt`. That
`freshCol` is the same at both families, where `J.fresh` is `none`, follows from the fields `hide`
and `tails` of `Agree`: `J.first` sets the fresh table to `packedN`
(Johnson/Prover/Link/BodyPack.lean) of `hideAt`, and its tails to the field `tails`.

Hypotheses of `msgAt_first`. hst: the stages are s :: t :: rest: two stages or more. A:
`Agree J w fr s K₁ K₂`, at the first stage s. hi: i < 2 + (h + g): i is a round of "BAT" or of the
first fold. J, w, fr, K₁, K₂ and D are free parameters.

Why `Agree` does not ask that the two families are equal as functions. The frame lends the two parts
stretches of other lengths: the second part carries the fresh table's stretch behind the members',
and, where the table has come earlier, the first part spends the coefficients alone while the second
carries the whole stretch. A stretch is 0 beyond its count. So the two readers differ, as functions
on all numbers, at generic coins. That they differ only where the first part's rounds do not read is
not shown: see the limits.

Limits.
- That a book lends the two parts coins on which the readers agree is not treated: it comes to
  equations on the book's entries (one owner and one start for the spent and the carried stretch of
  the coefficients, and for each member's stretch to both parts) and one on the job's rows.
- The job's rows as a whole need not be the same at the two families: a row's tails may read a
  stretch that one reader alone has.
- `Agree` is a hypothesis here. AgreeBook.lean in this folder (not in the library yet) derives it
  from such equations, with k = h + g at the first stage as one more hypothesis, and only where the
  table has come earlier. A value that meets it at the two parts' readers lies in AgreeToy.lean in
  this folder (not in the library yet), at one small made-up book, where the table has come earlier.
  So at the two parts' readers `Agree` has no value that meets it in the library yet; where the
  first fold sends its own table, neither of the two files gives one. At one family taken twice
  (K₁ = K₂) its three fields hold by reflexivity, which says nothing on the two readers.
- That the two readers differ only where the first part's rounds do not read is not shown. The job's
  field `rows₀` is the caller's function of `mem`: it may put into the first stage's message what it
  reads of `mem` at the number `J.members.length`, where the first part's reader gives
  `Stretch.zero` and the second's gives the fresh table's stretch (see the limits of Parts.lean).
  Where h > k, `hideAt` at h + g reads 2 (h + g) + 1 coins, while the stretch that the first part
  spends where the table has come earlier (`spentRun`, Parts.lean) counts 2k + 1 (see the limits of
  Coins.lean).
- `msgAt_first` is stated for two stages or more only. It counts the rounds as 2 + (h + g), while
  `firstLen` (Parts.lean) counts the first part's as 2 + k: the same number where h is at most k.
- Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- Two families of coins agree on what the first part's rounds read. `hide`: the same coefficients,
by `hideAt` at h + g of `sgOf s`. `table`: the same message of the first stage, by `μOf` applied to
`J.first`. `tails`: where `J.fresh` is `none`, the same field `tails`. -/
structure Agree (J : TestJob W X) (w : W) (fr : Front X) (s : Fmt.M1.Stage) (K₁ K₂ : TestCoins) :
    Prop where
  hide : hideAt ((sgOf s).h + (sgOf s).g) K₁.hide = hideAt ((sgOf s).h + (sgOf s).g) K₂.hide
  table : μOf (sgOf s) (J.first w fr K₁) = μOf (sgOf s) (J.first w fr K₂)
  tails : J.fresh = none → K₁.tails = K₂.tails

/-- The first fold's rounds at the family of coins K: `aFold` at stage number 0 and the stage s,
with 1 as the number of its first round. -/
def foldOf (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) : List Fmt.RoundView :=
  aFold (coinsOf J.p.nums.stages K.hide K.rest) 0 s 1 (J.first w fr K)
    (rowOf (J.recB w fr (D 0))) D

/-- The rounds and the trees of `testAll`, divided after the first fold: those of "BAT", those of
the first fold, and a further list. -/
theorem test_cut (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest) :
    (∃ tl, (testAll J w fr K D).rs = ⟨[], D 0⟩ :: (foldOf J w fr K D s ++ tl)) ∧
    ∃ tl, (testAll J w fr K D).tr = (fun _ => []) ::
      (if J.fresh.isNone then
        ((foldOf J w fr K D s).map (fun _ _ => []) ++ tl).set 0 (freshCol (sgOf s) (J.first w fr K))
      else (foldOf J w fr K D s).map (fun _ _ => []) ++ tl) := by
  unfold testAll foldOf
  split
  · rename_i h0
    rw [hst] at h0
    cases h0
  · rename_i s' rest' h0
    rw [hst] at h0
    obtain ⟨rfl, rfl⟩ := List.cons.inj h0
    simp only [stagesAll]
    exact ⟨⟨_, congrArg _ (List.append_assoc _ _ _)⟩, ⟨_, by rw [List.append_assoc]⟩⟩

theorem foldOf_agree (J : TestJob W X) (w : W) (fr : Front X) (K₁ K₂ : TestCoins)
    (D : ℕ → Fmt.Drawn) (s : Fmt.M1.Stage) (A : Agree J w fr s K₁ K₂) :
    foldOf J w fr K₁ D s = foldOf J w fr K₂ D s := by
  unfold foldOf aFold
  have e1 := A.table
  have e2 : (coinsOf J.p.nums.stages K₁.hide K₁.rest).W (sgOf s) 0 =
      (coinsOf J.p.nums.stages K₂.hide K₂.rest).W (sgOf s) 0 := by
    show hideAt ((sgOf s).h + (sgOf s).g) (if (0 : ℕ) = 0 then K₁.hide else _) =
      hideAt ((sgOf s).h + (sgOf s).g) (if (0 : ℕ) = 0 then K₂.hide else _)
    rw [if_pos rfl, if_pos rfl]
    exact A.hide
  rw [e1, e2]

theorem length_foldOf (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn)
    (s : Fmt.M1.Stage) : (foldOf J w fr K D s).length = 1 + ((sgOf s).h + (sgOf s).g) := by
  unfold foldOf aFold foldShown
  rw [List.length_cons, length_showRV]
  omega

/-- **The first part's messages are the same at both families.** hst: two stages or more. A: `Agree`
at the first stage. hi: i is a round of "BAT" or of the first fold. -/
theorem msgAt_first (J : TestJob W X) (w : W) (fr : Front X) (K₁ K₂ : TestCoins)
    (D : ℕ → Fmt.Drawn) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (A : Agree J w fr s K₁ K₂) (i : ℕ)
    (hi : i < 2 + ((sgOf s).h + (sgOf s).g)) : msgAt J w fr K₁ D i = msgAt J w fr K₂ D i := by
  obtain ⟨⟨a1, r1⟩, ⟨b1, t1⟩⟩ := test_cut J w fr K₁ D s t rest hst
  obtain ⟨⟨a2, r2⟩, ⟨b2, t2⟩⟩ := test_cut J w fr K₂ D s t rest hst
  have ef := foldOf_agree J w fr K₁ K₂ D s A
  have hl := length_foldOf J w fr K₂ D s
  have eP : J.fresh = none →
      freshCol (sgOf s) (J.first w fr K₁) = freshCol (sgOf s) (J.first w fr K₂) := fun hfr => by
    have hs0 : J.s₀ = s := by
      unfold TestJob.s₀
      rw [hst]
      rfl
    have e : (J.first w fr K₁).fM = (J.first w fr K₂).fM := by
      show packedN (sgOf J.s₀) (hideAt ((sgOf J.s₀).h + (sgOf J.s₀).g) K₁.hide) =
        packedN (sgOf J.s₀) (hideAt ((sgOf J.s₀).h + (sgOf J.s₀).g) K₂.hide)
      rw [hs0, A.hide]
    have e' : (J.first w fr K₁).fT = (J.first w fr K₂).fT := A.tails hfr
    funext x
    show wordsOf (wr _ (freshSym _ (J.first w fr K₁).fM (J.first w fr K₁).fT x)) =
      wordsOf (wr _ (freshSym _ (J.first w fr K₂).fM (J.first w fr K₂).fT x))
    rw [e, e']
  rw [ef] at r1 t1
  generalize foldOf J w fr K₂ D s = F at r1 r2 t1 t2 hl
  generalize freshCol (sgOf s) (J.first w fr K₁) = c1 at t1 eP
  generalize freshCol (sgOf s) (J.first w fr K₂) = c2 at t2 eP
  have hrs : (testAll J w fr K₁ D).rs[i]? = (testAll J w fr K₂ D).rs[i]? := by
    rw [r1, r2]
    cases i with
    | zero => simp only [List.getElem?_cons_zero]
    | succ n =>
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  have htr : (testAll J w fr K₁ D).tr.getD i (fun _ => []) =
      (testAll J w fr K₂ D).tr.getD i fun _ => [] := by
    rw [t1, t2]
    cases i with
    | zero => simp only [List.getD_cons_zero]
    | succ n =>
      have hn : n < (F.map fun _ (_ : ℕ) => ([] : List UInt64)).length := by
        rw [List.length_map]
        omega
      rw [List.getD_cons_succ, List.getD_cons_succ]
      cases hfr : J.fresh with
      | none =>
        obtain rfl : c1 = c2 := eP hfr
        simp only [Option.isNone_none, if_true, List.getD_eq_getElem?_getD]
        cases n with
        | zero =>
          rw [List.getElem?_set_self (by rw [List.length_append]; omega),
            List.getElem?_set_self (by rw [List.length_append]; omega)]
        | succ m =>
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_append_left hn, List.getElem?_append_left hn]
      | some _ =>
        simp only [Option.isNone_some, Bool.false_eq_true, if_false, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hn, List.getElem?_append_left hn]
  unfold msgAt
  simp only
  rw [hrs, htr]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.test_cut
#print axioms ProofFile.Honest.K12.foldOf_agree
#print axioms ProofFile.Honest.K12.length_foldOf
#print axioms ProofFile.Honest.K12.msgAt_first
#print axioms ProofFile.Honest.K12.Agree
#print axioms ProofFile.Honest.K12.foldOf
