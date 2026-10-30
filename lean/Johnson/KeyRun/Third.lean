-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/KeyRun/Third.lean: a check of a key file's third chain as a plain function, with code, of
the plan's key chains and the file's three views, and of nothing else: `third`.

`third` is two tests. `thirdPublicOk` is on the plan alone. `dec₃` is on the views: it is `decWith`
(Johnson/KeyRun/ThirdAtClaim.lean) at the claim that `claim₁` (Johnson/KeyRun/FirstClaim.lean) makes
of the first view. No block of the verifier program is run beneath either. They call functions of
the program's text that are no blocks, and parts are written after the program's text: the heads of
the two files list both for `dec₃`, and explain the words.
Main names:
  `dec₃`: the test on the views.
  `thirdPublic`: ten tests on the plan, each with a name; `thirdPublicOk`: all say yes. All but the
    seventh and the tenth are written after tests of the program (its readers, `Key.check`, its
    blocks); the eighth is stricter at one place (Johnson/KeyRun/TestPlan.lean, Limits). `dec₃`
    makes a few of them too: the head of Johnson/KeyRun/ThirdAtClaim.lean, (2).
    (1) The first two chains hold the same codes and shape. (2) The three plans have the same
    settings, but for the digest; the field is the program's; the word `saved` is 1; the second and
    third have no entry "RECORD" ((1) and (2): `KeyChains.read`, on the bytes; the field:
    `Key.check`; `saved`: `Fmt.Plan.ok`). (3) `Key.admitted`, which holds `linOk`, and more than one
    column (`memberRowsFit`). (4) `Codes.lengthsOk`, which every run of a block asks
    (`Blk.runNamed`). (5) Each member fits the group (`Blk.join`), and the first stage's codes are
    the group's (`ioppVerify`). (6) `ioppOk`. (7) WHAT `dec₃` HAS BUILT IN, a narrowing of this
    file's own: one answer to a sample, masks ride, and the first fold's mask comes ahead with W.
    The program also takes other plans; `third` says no to them. (8) The third chain's plan has just
    the test's rounds, each with the name, message, draws, range of positions and count of rows that
    `wants₃` lists (Johnson/KeyRun/TestPlan.lean). (9) "SEND answer" stands behind each "SEND seed"
    that `dec₃` reads. (10) A SECOND NARROWING: no stage's code is longer than 2^32. The point of a
    position in `iopp` (`Fmt.M1.point`, Fmt/M1Codes.lean) and the program's (`codePoint`,
    OnBytes/Iop/Ground.lean) are one value up to that length (`toF_codePoint`,
    OnBytes/Slice/ProgCodes.lean) and part at a position with bit 32 set; the program takes codes up
    to 2^60. Where they say yes, every code that `dec₃` looks up (`depthOf`, `stOf`, `wanted`,
    `FirstClaim.lay`) is there.
  `third`; `third_dec₃`: its yes gives a yes of `dec₃`.

What it is not.
  - No equation ties `third` to a protocol of which this library states soundness, or to the
    program's decision: it is a function that can be run, not one that is proved. It is none of the
    library's verifiers, and no verifier and no theorem on soundness calls it.
  - It checks the third chain alone. The first two chains' own tests are not asked. Of the first
    view it reads the rounds that `FirstClaim.roundsRead` lists and four rounds of seeds and
    answers; of the second view three rounds; of neither an opened column.
  - KNOWN LIMITS follow (rows 8 and 6 of the two files lean/Ask/KeyThirdChain*.lean ask the first
    two). `third` gives the same answer after a change (1) of a value in another round of the first
    chain, (2) of an element that the prover sent in a round inside the last level of a part's key
    tree, whose challenge alone is taken, (3) of a value in another round of the second chain, (4)
    of a column that was opened in these two chains.
  - `thirdPublic` is written by reading the program's text; it does not ask all that the program
    asks of the plan. Not asked: the bits of work and the numbers of positions; what shares a tree
    (the classes of leaves: `layTrees`, `linAloneInItsTree`, `countOpening`); the strict reader's
    conditions on a description beyond an entry's bytes, roots and answers; that the three digests
    are equal; that every group has been tested at the chain's end (`Blk.requireAllTested`); the
    first two chains' plans beyond the names above; the limits of Johnson/KeyRun/TestPlan.lean. The
    list may not be whole. It holds the plan's parts against each other, not against written
    constants of one setting: a plan of another setting that fits together passes. A test of that
    kind belongs to a check of the whole key file, which is not here.
  - All that the heads of the two files say that they are not, among it the known differences from
    the program's run on the side of the views. Two of these by name: other items, positions or
    matrix entries in the third view's first round pass, and `sentOf` passes over an item that is no
    element and takes an answer for an element. A view that the strict reader has made under an
    entry that the eighth test has passed holds nothing of the kind: that is the reader's doing,
    not `third`'s.


-/
import Johnson.KeyRun.ThirdAtClaim
import Johnson.KeyRun.FirstClaim
import Johnson.KeyRun.TestPlan

set_option autoImplicit false

namespace Johnson.KeyRun.Third

open OnBytes OnBytes.Params

/-- **The test on the views.** It says no if `claim₁` makes no claim of the first view. -/
def dec₃ (k : KeyChains) (v₁ v₂ v₃ : Fmt.View) : Bool :=
  match FirstClaim.claim₁ k.oneTime v₁ 0 with
  | some c => decWith (pubOf k) c v₁ v₂ v₃
  | none => false

/-- What the entries of the third chain's plan must say. The round "BAT" batches the rows (Eval) and
(Dot) and each of the three members' sample rows. -/
def wants₃ (k : KeyChains) : List TestPlan.Want :=
  let S := k.shared.lin
  let a := k.second.given.plan.samples
  TestPlan.wantsTest k.shared.codes a S.testOwn (2 + 3 * a) (if S.masksAhead then 0 else 1)
    S.choice.masksRide

/-- The plan calls the round behind round i "SEND answer". -/
def answersBehind (es : List Fmt.Entry) (i : Option Nat) : Bool :=
  (i.bind fun i => es[i + 1]?).map (·.name) == some "SEND answer"

/-- Two plans have the same settings, as `Params.sameSetting` asks, but for the digest, and for the
number of answers, which the seventh test asks. -/
def sameSettings (a b : Fmt.Plan) : Bool :=
  a.field == b.field && a.salt == b.salt && a.nonce == b.nonce && a.posB == b.posB &&
    a.saved == b.saved

/-- The name of the test that holds the third chain's plan against `wants₃`. -/
def roundsTest : String := "the third chain's plan has just the test's rounds"

/-- **The tests on the plan alone**, each with its name. -/
def thirdPublic (k : KeyChains) : List (String × Bool) :=
  let P := pubOf k
  let S := P.S
  let s₁ := named P.e₁ "SEND seed"
  let p₁ := k.oneTime.given.plan
  [("the first two chains hold the same codes and the same shape",
      k.oneTime.codes == P.codes && k.oneTime.lin == S),
   ("the three plans have the same settings and the program's field; no RECORD in the last two",
      p₁.field == .two && p₁.saved == 1 && sameSettings p₁ k.shared.given.plan &&
        sameSettings p₁ k.second.given.plan && k.shared.given.record.isNone &&
        k.second.given.record.isNone),
   ("the first chain's public values fit together (Key.admitted), with more than one column",
      Key.admitted k.oneTime && decide (0 < S.kCol)),
   ("every code's message length is a power of two (Codes.lengthsOk)", P.codes.lengthsOk),
   ("each member fits the group, and the first stage's codes are the group's",
      ([P.idx.shape, S.w, S.omega].all fun o =>
        (o.mainRows == 0 || o.code == S.w.code) &&
          (o.maskRows == 0 || o.maskCode == S.ownMaskCode)) &&
        (S.testOwn.head?.map fun s => (s.code, s.maskCode)) == some (S.w.code, S.ownMaskCode)),
   ("the stages fit their codes and each other (ioppOk)",
      ioppOk P.codes S.testOwn k.second.given.plan.samples),
   ("one answer to a sample in all three plans, masks ride, the first mask comes ahead",
      p₁.samples == 1 && k.shared.given.plan.samples == 1 &&
        k.second.given.plan.samples == 1 && S.choice.masksRide && S.masksAhead),
   (roundsTest, P.e₃.length == (wants₃ k).length && TestPlan.okFrom (wants₃ k) P.e₃ 0),
   ("SEND answer stands behind each SEND seed that is read",
      answersBehind P.e₁ s₁.head? && answersBehind P.e₁ s₁.getLast? &&
        answersBehind P.e₂ (named P.e₂ "SEND seed")[1]?),
   ("no stage's code is longer than 2^32",
      S.testOwn.all fun s => decide ((P.codes.base.getD s.code default).logN ≤ 32) &&
        decide ((P.codes.mask.getD s.maskCode default).logN ≤ 32))]

def thirdPublicOk (k : KeyChains) : Bool := (thirdPublic k).all (·.2)

/-- **A check of the third chain**: the tests on the plan, then the test on the views. -/
def third (k : KeyChains) (v₁ v₂ v₃ : Fmt.View) : Bool := thirdPublicOk k && dec₃ k v₁ v₂ v₃

theorem third_dec₃ {k : KeyChains} {v₁ v₂ v₃ : Fmt.View} (h : third k v₁ v₂ v₃ = true) :
    dec₃ k v₁ v₂ v₃ = true := by
  unfold third at h
  exact (Bool.and_eq_true _ _ ▸ h).2

end Johnson.KeyRun.Third
