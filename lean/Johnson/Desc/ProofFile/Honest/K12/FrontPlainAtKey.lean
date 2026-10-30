-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontPlainAtKey.lean: the function `frontPlainB` (FrontPlainB.lean
in this folder; its values are in Bool) is true at three written values: the written place of the
key file's proximity test on the ranges (`piKRFull`), the written thin shape before that test
(`frontKR`), and the sending of the multiplicities as the library's written sizes of a key have it
(`keyFull`). The proof is the kernel's own evaluation (`decide +kernel`). So, by `frontPlain_of_B`
(FrontPlainB.lean), at every state of that thin shape and every sending with these codes and
messages there are plain data Dp of the test's first stage at which `oneFitsB` is true; and at every
group that is the state's group under test, Dp is what the library makes as plain data and passes
the library's clauses (`plain_at_KR`). `frontAsks_KR` (FrontAtKey.lean in this folder) calls
`plain_at_KR`. `frontPlainB_congr` is general in the place, the sendings and the thin shape; all
else is at the written values. One definition with code, and four theorems with their proofs.

In the list: `frontPlainB p P a₀` is a test on a place p, a sending's public data P and a thin
shape a₀. `piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) is the written parameters
(`P12`, Johnson/Desc/K12/Frame.lean), the place among them, of the key file's proximity test on the
ranges at the full size. `stA p` (PlanB.lean in this folder) is the first stage of p
(`Fmt.M1.Stage`); C and Z are a stage's main code and mask code, and `l` is a code's message length.
A state t is a value of the type `T12` (Johnson/Desc/K12/Join.lean) of the verifier's state inside a
proximity test. Among its fields are a statement `st`, the number `g` of the group under test, and
what one part of the test passes to the next (`pass`). `thinSh t` (`ThinSh`,
Johnson/Desc/K12/Honest/Shape/TestCore.lean) is its thin shape: the shape of its statement, book of
trees and count of roots (`coreSh`, Johnson/Desc/Ground/Shape/Core.lean), then `g`, a part of `pass`
(`thinPass`), and the field `mask`. `frontKR`
(Johnson/Desc/K12/Honest/Shape/TestEndedAtKeyRanges.lean) is the thin shape with the written core
`shKRFull` (TestAtKeyRangesShape.lean in that folder), the group number 0, `.nothing` passed on, and
`some 2` in the field `mask`. A sending is a sub-protocol of the kind K1, which sends oracle
messages. P (`K1.Par`, Johnson/Desc/K1/Send.lean) has the codes `P.codes` and the list of messages
`P.sent`. `keyFull` (`Lk6.AtPlan.keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean) is the
library's written sizes of a key at the full size (`KeySized`, OnBytes/Plan/KeyOneTime.lean).
`Wf.messageOf keyFull.ranges.x` (OnBytes/Iop/Wf.lean) is the list of messages of the sending of the
multiplicities at these sizes. `keyFull.once.input` is the message that `oneTimeItems`
(KeyOneTime.lean) lists under the name "index-mask message". The plain data (`Plain`), `gpOf`, which
makes them, `gpL`, which lists the library's clauses on them, each a name with a Bool, and `ok`,
which is true where all these are true, are in Johnson/Desc/K12/Law/FirstOk.lean. `plainSh`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean) gives the shape of plain data. `oneFitsB`
(OneFitsB.lean in this folder) is a function with values in Bool, on a place, a sending's public
data and such a shape. Where it is true, the plain data have one member and one tree's place, and
the member and the first fold's fresh table (the field `fresh` of `Plain`) are the sending's
messages number 0 and 1 (`seatIsB`, OneFitsB.lean). G is a group of `t.st`; its layout is
`layoutOf t.st G` (Johnson/Desc/Means/Layout.lean). `layoutAt t` (JobOne.lean in this folder) is the
layout of group number `t.g`, an empty one where there is no such group. `batT t G {}`
(Johnson/Prover/Link/FormFirst.lean) is t with the group's test begun, passing on the empty row with
the layout of G.

  `plain_at_KR`: under the three hypotheses below, what `frontPlain_of_B` concludes at `piKRFull`, P
    and t. There are plain data Dp such that `oneFitsB piKRFull P (plainSh Dp)` is true and `Dp.L`
    is `layoutAt t`. And at every G that is group number `t.g` of `t.st`: `gpOf` returns Dp at
    `piKRFull`, `batT t G {}`, the first stage and the layout of G;
    `ok (gpL piKRFull (stA piKRFull) {} Dp)` is true; 2 ^ `logEll` of that layout is
    `(stA piKRFull).C.l`; and 2 ^ `logEllZk` of it is `(stA piKRFull).Z.l`
  `frontPlain_KR`: `frontPlainB piKRFull parKR frontKR` is true: by the kernel
  `frontPlain_KR_no`: negative tests: false with the two messages exchanged; with the index masks'
    sending in that sending's stead; at the group 1. In the Lean text these are: the messages of
    `parKR` in reverse order; the one message `keyFull.once.input` for the two;
    `{ frontKR with g := 1 }` for `frontKR`. All else is as in `frontPlain_KR`. By the kernel too
  `frontPlainB_congr`: of the sending's public data `frontPlainB` reads only the codes and the list
    of messages: where `P.codes = P'.codes` and `P.sent = P'.sent`, `frontPlainB p P a₀` is
    `frontPlainB p P' a₀`
  `parKR`: a definition: the sending's public data as far as `frontPlainB` reads them: the codes
    `keyFull.codes`, and one part, under the empty name, with the messages
    `Wf.messageOf keyFull.ranges.x`. The fields `place`, `gp`, `work` and `groups` are filled with
    written values; by `frontPlainB_congr`, `frontPlainB` does not depend on them

By what. `frontPlain_KR` and `frontPlain_KR_no` are proved by `decide +kernel`: Lean's kernel
evaluates `frontPlainB` at closed terms. `frontPlainB_congr` unfolds `frontPlainB`, in which P is an
argument of `oneFitsB` only, and rewrites by `oneFitsB_congr` (OneFitsB.lean). `plain_at_KR` gets
`t.pass = .nothing` from ht by cases on `t.pass` (`thinPass`, TestCore.lean) and
`piKRFull.early = true` by `decide +kernel`, and calls `frontPlain_of_B` (FrontPlainB.lean). It
rewrites by ht, passes from P to `parKR` by `frontPlainB_congr`, where `simp` shows that
`parKR.sent` is `Wf.messageOf keyFull.ranges.x`, and ends with `frontPlain_KR`. The option
`maxRecDepth` is raised to 1000000 for the whole file.

Hypotheses of `plain_at_KR`. hc: `P.codes = keyFull.codes`. hs:
`P.sent = Wf.messageOf keyFull.ranges.x`. ht: `thinSh t = frontKR`.

Limits.
- At written values: `piKRFull` and the written shape (its core `shKRFull`) were written off prints,
  the text that runs of Lean's evaluator printed. The limits of PlaceKeyRangesFull.lean and of
  TestAtKeyRangesShape.lean hold here too.
- In scope (`VerifierAndGoals.InScope Z = true`), under the hypothesis `KeySourced`, `piKRFull` is compared
  with the description's own numbers (`place_sourced`, E2E/KeyRangesK12.lean), and the written shape
  with the run of the description's guards on shapes, at every state under the first chain's thread
  (`Thr`, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) before the test (`shape15_of_thr`,
  `core15`, `thinSh_15`, E2E/KeyRangesShape15.lean). These theorems are not called here. By that
  file's own limits, that a thread is at that point is shown nowhere.
- `keyFull` is a written value too. Nothing here says that these are the sizes at the public files,
  or that a description's sending has these codes and messages: in `plain_at_KR` that is hc and hs.
- That a state has the thin shape `frontKR` is a hypothesis (ht); it is not shown here. t is a free
  parameter of the type `T12`; nothing here shows that it is the verifier's state.
- The four clauses of `plain_at_KR` "at every G" are vacuous where `t.st` has no group number `t.g`.
  The proof of `frontPlain_of_B` shows that there is such a group, but neither theorem states it.
- The negative tests change the list of messages (twice) and the group's number. None changes the
  place, the codes or the core `shKRFull`. Each says that `frontPlainB` as a whole is false; which
  of its clauses fails is not stated.
- On shapes alone: no field element.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontPlainB
import Johnson.Desc.K12.Honest.Shape.TestEndedAtKeyRanges
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Member (piKRFull)
open Lk6.AtPlan (keyFull)
open ProofFile.Honest.Sh (ThinSh thinSh frontKR shKRFull plainSh)

/-- The public data of the sending of the multiplicities, as far as `frontPlainB` reads them: the
codes and the messages, taken from `keyFull`. `frontPlainB` does not depend on the other fields
(`frontPlainB_congr`). -/
def parKR : K1.Par :=
  { place := ⟨1, none, 2, .K1⟩, codes := keyFull.codes, gp := ⟨keyFull.set.samples, 0⟩, work := 0
    parts := [("", Wf.messageOf keyFull.ranges.x)], groups := [] }

/-- Of the sending's public data `frontPlainB` reads only the codes and the list of messages. -/
theorem frontPlainB_congr (p : P12) (P P' : K1.Par) (a₀ : ThinSh) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : frontPlainB p P a₀ = frontPlainB p P' a₀ := by
  unfold frontPlainB
  simp only [oneFitsB_congr p P P' _ hc hs]

/-- **`frontPlainB` is true at the written place, sending and thin shape.** By the kernel's own
evaluation. -/
theorem frontPlain_KR : frontPlainB piKRFull parKR frontKR = true := by decide +kernel

/-- Negative tests: `frontPlainB` is false with the messages in reverse order, with the one message
`keyFull.once.input` for the two, and at the group number 1. -/
theorem frontPlain_KR_no :
    frontPlainB piKRFull
        { parKR with parts := [("", (Wf.messageOf keyFull.ranges.x).reverse)] } frontKR = false ∧
      frontPlainB piKRFull { parKR with parts := [("", #[keyFull.once.input])] } frontKR = false ∧
      frontPlainB piKRFull parKR { frontKR with g := 1 } = false := by decide +kernel

/-- **At every state of that thin shape**, and every sending with the written codes and messages:
what `frontPlain_of_B` (FrontPlainB.lean) concludes. hc, hs: the codes and the messages of P are
those of `keyFull`. ht: the thin shape of t is `frontKR`; t is a free parameter. -/
theorem plain_at_KR (P : K1.Par) (hc : P.codes = keyFull.codes)
    (hs : P.sent = Wf.messageOf keyFull.ranges.x) (t : T12) (ht : thinSh t = frontKR) :
    ∃ Dp : Plain, oneFitsB piKRFull P (plainSh Dp) = true ∧ Dp.L = layoutAt t ∧
      ∀ G, t.st.groups[t.g]? = some G →
        gpOf piKRFull (batT t G {}) (stA piKRFull) (layoutOf t.st G) = some Dp ∧
          ok (gpL piKRFull (stA piKRFull) {} Dp) = true ∧
          2 ^ (layoutOf t.st G).logEll = (stA piKRFull).C.l ∧
          2 ^ (layoutOf t.st G).logEllZk = (stA piKRFull).Z.l := by
  have hp : t.pass = .nothing := by
    have k : ProofFile.Honest.Sh.thinPass t.pass = .nothing := congrArg (·.pass) ht
    cases h : t.pass with
    | nothing => rfl
    | claim _ _ => rw [h] at k; cases k
    | single _ _ => rw [h] at k; cases k
    | switched _ _ _ => rw [h] at k; cases k
  refine frontPlain_of_B piKRFull P t hp (by decide +kernel) ?_
  rw [ht, frontPlainB_congr piKRFull P parKR frontKR hc (hs.trans (by
    show _ = ([("", Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray
    simp))]
  exact frontPlain_KR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.frontPlainB_congr
#print axioms ProofFile.Honest.K12.frontPlain_KR
#print axioms ProofFile.Honest.K12.frontPlain_KR_no
#print axioms ProofFile.Honest.K12.plain_at_KR
#print axioms ProofFile.Honest.K12.parKR
