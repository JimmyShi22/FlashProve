-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/BatStateTest.lean: "every row that the test takes in says its claim of the
words that the plain rows make" as a test with code, `saysB`, so that it can be checked at a value
by an evaluation, and the theorem that the "true" of `saysB` gives that proposition. The proposition
is the hypothesis hs of `bat_claimTrue_state` (Johnson/Desc/K12/Honest/BatState.lean): a hypothesis
on the prover's data, next to `StateAt`. General in the two states, the layout and the plain rows. A
definition with code, a theorem and its proof. It depends on no frame for an honest side: no file
under Johnson/Desc/ProofFile/Honest/ is among its imports, direct or indirect.

In the list: in the phrase above "the test" is a proximity test; below, the test is `saysB`. The
batching is the part `guardedProximityTestParts.bat` (Johnson/Desc/K12/JoinGuarded.lean) of a proximity test. tF and t
have the type `T12` (Johnson/Desc/K12/Join.lean) of the verifier's state inside a proximity test;
read here are its statement `st` and the number `g` of the group under test. L is a layout
(`GroupLayout`; this, `Statement`, `Group` and `Row`: OnBytes/Iop/Ground.lean). The plain rows R are
the prover's rows as plain functions of numbers (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). The rows that a proximity test takes in are `runRows S G`
(OnBytes/Slice/BlkBegin.lean): the rows of the group G of the kind `plain`, each member's sample
rows in the statement S, the rows of G of the kind `generator`. Words (`Words`; this, `value`,
`Says` and `AllSay`: Johnson/Desc/Means/Says.lean) give a value for each oracle message, table and
index. The words that the plain rows make are `wordsAt S L R`
(Johnson/Desc/K12/Honest/LaidState.lean). `value` is a row applied to words: the sum of coefficient
times word over the entries of all tables that the statement has. A row says its claim of the words
(`Says`) if that sum is the row's target; `AllSay` says so of every row of a list. `rdE`
(OnBytes/Slice/BlkRead.lean) reads the program's elements as elements of the extension field.

  `allSay_of`: if `saysB tF t L R` is true, then for every G with `tF.st.groups[tF.g]? = some G`:
    `AllSay rdE t.st (runRows tF.st G).toList (wordsAt t.st L R)`. That is the hypothesis hs of
    `bat_claimTrue_state`, word for word. No other hypothesis
  `saysB tF t L R`: a definition: the test. Where `tF.st` has a group G at the number `tF.g`: for
    every row r of `runRows tF.st G`, `value rdE t.st r (wordsAt t.st L R)` and the target of r,
    read by `rdE`, are written alike (`sameE`, Johnson/Desc/K12/Honest/FirstTest.lean). The rows are
    taken at the statement of tF, the value and the words at the statement of t. Where `tF.st` has
    no such group: false

By what. `allSay_of` unfolds `saysB` and uses `List.all_eq_true` and `same_of` (FirstTest.lean: the
"true" of `sameE` gives that the two elements are equal).

Limits. A "true" at a value is an evaluation by Lean's evaluator, outside the kernel. Nothing is
evaluated here; `#guard` lines in
Johnson/Desc/ProofFile/Honest/K12/ToySays.lean (not in the library yet) evaluate the test at small
made-up values, through `At.says`. The evaluations at which the test by itself returns "false" lie
in that file only. The one caller of `saysB` in the library is `restB`
(Johnson/Desc/ProofFile/Honest/K12/AllB.lean), a larger test of which it is one conjunct. The test
is for small sizes: for each row it sums over every entry of every table that `t.st` has. tF, t, L
and R are free parameters: that a verifier reaches tF or t, that the batching leads from tF to t,
that t passes a claim with the layout L (`t.pass = .claim row L`), that a prover holds R: none of
this is stated here. Only the direction from the test to `AllSay` is stated. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.BatState
import Johnson.Desc.K12.Honest.FirstTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The test: every row that the proximity test takes in says its claim of the words
`wordsAt t.st L R`. tF and t are free parameters of the type of the verifier's state inside a
proximity test. In `bat_claimTrue_state`, tF is the state at which the batching decides and t the
state that it returns; here nothing ties the two, and neither is stated to be a verifier's. -/
def saysB (tF t : T12) (L : GroupLayout) (R : PlainRows) : Bool :=
  match tF.st.groups[tF.g]? with
  | some G =>
    (runRows tF.st G).toList.all fun r =>
      sameE (value rdE t.st r (wordsAt t.st L R)) (rdE.val r.target)
  | none => false

theorem allSay_of {tF t : T12} {L : GroupLayout} {R : PlainRows} (h : saysB tF t L R = true) :
    ∀ G, tF.st.groups[tF.g]? = some G →
      AllSay rdE t.st (runRows tF.st G).toList (wordsAt t.st L R) := by
  intro G hG r hr
  unfold saysB at h
  rw [hG] at h
  exact same_of (List.all_eq_true.1 h r hr)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.allSay_of
#print axioms ProofFile.Honest.K12.saysB
