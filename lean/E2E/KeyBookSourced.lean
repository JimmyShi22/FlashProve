-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookSourced.lean: which fields of the sizes `KeyPub.of` (E2E/KeyBook.lean) reads, and that,
at public files in scope, it returns at the sizes in the source of the key file's description the
value that it returns at the library's written sizes (`fullPub`, E2E/KeyBookAtWritten.lean).
`KeyPub.of z a` computes, from the sizes z (`Plan.KeySized`, OnBytes/Plan/KeyOneTime.lean) and the
number a of answers to an OOD sample, the structure `KeyPub` of public data from which `keyBook`
computes the key file's book of coins; at some sizes it returns nothing. A book (`ProverCoinCounts`) is a
structure of the frame (Johnson/Desc/ProofFile/Honest/Frame.lean): the public table that says how
many coins each part of an honest prover has of its own, and which of these coins other parts are
given too. Four theorems; no definition. Public data only. `of_flags` and `of_reads` are general in
the sizes; the other two hold at one size.

For what. The book's counts are computed from the codes and shapes in the sizes. Theorems of other
files on the book at the full size (`book_passes`, E2E/KeyBookThirdNamed.lean, among them) have the
hypothesis `fullPub = some K`, and `fullPub` is `KeyPub.of` at the library's written value `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean). The key file's description is `descriptionFromSource X N P`
(Johnson/Desc/Key/Desc.lean; a description is the IOP of a file as written in Lean), and its source
X (`Source`, Johnson/Desc/Key/FileOk.lean) is what it is made of. By `pub_of_made` and
`pub_of_source` that hypothesis can be stated at the source's values instead:
E2E/KeyBookSourcedPasses.lean does so for `book_passes`.

  `pub_of_made`: in scope: `KeyPub.of` at the sized key in the answer m of `madeAt`
    (`m.p.chains.made.sized.key`) and at the number of answers in the source's setting
    (`X.set.samples`) is `fullPub`
  `pub_of_source`: in scope: `KeyPub.of z X.set.samples` is `fullPub` at every z whose four fields
    of `of_reads` are, in that order, the fields `lin`, `ranges`, `codes` and `indexMasks` of
    `X.Y.k.oneTime`. That is the source's value of `OneTime` (OnBytes/Params/Chains.lean): what the
    parameter bytes of a key's one-time chain hold. The one-time chain is the key file's first chain
  `of_reads`: sizes z and z' that agree in four fields give the same value of `KeyPub.of`, at every
    a. The four: `once.shape`, the shape of the test on the table; `ranges.x`, the parameters of the
    proof of the ranges; `codes`, the codes; `once.input`, the notice of the index-mask message
    (`OracleNotice`: an oracle message as it is announced). So `KeyPub.of` reads nothing else of the
    sizes
  `of_flags`: where `KeyPub.of z a` returns a value, the five flags of its guard are as follows.
    `ranges.x.choice.masksRide` and `once.shape.choice.masksRide` are true: the proximity tests'
    masks are sent along with earlier oracle messages (`IoppChoice`, OnBytes/Params/Items.lean).
    `once.shape.sharedSplitNeeded` is true: the folded row and Omega differ in code, so there is a
    split between their groups. `once.shape.masksAhead` is true: the fresh tables of two tests'
    first folds are sent ahead, with the folded row and with W. `once.shape.ownSplitNeeded` is
    false: W and Omega have one code, so W's own group has no split (OnBytes/Iop/Lin.lean)

By what. `of_flags` and `of_reads` unfold `KeyPub.of`. `pub_of_made` rewrites by `key_in_scope` (the
sized key in m is `keyFull`) and by the first equation of `five_in_scope` (`X.set` is
`keyFull.set`); what is left is the definition of `fullPub`. `pub_of_source` rewrites by that first
equation and is then `of_reads` at z' := `keyFull`, by the other four equations of `five_in_scope`:
the four fields of `X.Y.k.oneTime` are those of `keyFull`. Both lemmas are the library's:
Johnson/RunOne/Law/KeyInScope.lean.

Hypotheses of `pub_of_made` and `pub_of_source`. The first five are those of `five_in_scope`. None
is proved here.
  hZ: the three public files Zp (`VerifierAndGoals.PublicFiles`) are in scope (`VerifierAndGoals.InScope`, Ladder.lean)
  hP: `ReadOf Zp.pol Z` (Johnson/RunOne/Law/KeyInScope.lean): `polLayout` at the parameter file
    returns the scan `Z.P` with some layout, and the layout of the weights in Z (`Z.layers.wsLay`)
    is computed from these two. `readOf_publicOf` and `readOf_publicOfO` (same file) prove it of
    what the library's two routines that read the public files return
  hm: `madeAt Z Zp.lay cfg` (Johnson/Desc/Key/Road.lean) returns m (`Made`,
    Johnson/G/RoundsOfPlan.lean: the planner's answer and what six chains send). cfg, the argument
    for the digest of the public files, is any byte string
  hX: `sourceOf m` (Johnson/Desc/Key/Desc.lean) returns the source X
  hp: the description `descriptionFromSource X N P` passes its tests on the plan (`FileDescription.planOk`,
    Johnson/Desc/Block.lean). N and P, which hold the numbers of the proximity tests' places, are
    free parameters
  h₁ to h₄, in `pub_of_source` only: the four equations on z

Limits. `pub_of_made` and `pub_of_source` say that two calls of one function return one value. They
do not say that the function's rule for coins is right: by the limits of E2E/KeyBook.lean the book
is a reading, not a theorem. They are at one size: in scope the sized key is `keyFull`
(`key_in_scope`), so they say nothing at another size, and every z of `pub_of_source` has the four
fields of `keyFull`. They are equations between values of `Option KeyPub`: that `fullPub` is not
`none` is not shown here; it is `full_made` (E2E/KeyBookPassesNamed.lean). `of_flags` has one
direction: with the five flags so, `KeyPub.of` still returns nothing where a message is not made,
where Omega's test has no stage, or where a code is missing. No property of a protocol is stated:
nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookAtWritten
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes
open OnBytes.Model.Verify (Public)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source LaterPlaces madeAt sourceOf descriptionFromSource)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope five_in_scope)
open Lk6.AtPlan (keyFull)

/-- Where `KeyPub.of` returns a value, the five flags of its guard have the values that the guard
asks for. -/
theorem of_flags {z : Plan.KeySized} {a : Nat} {K : KeyPub} (h : KeyPub.of z a = some K) :
    z.ranges.x.choice.masksRide = true ∧ z.once.shape.choice.masksRide = true ∧
      z.once.shape.sharedSplitNeeded = true ∧ z.once.shape.masksAhead = true ∧
      z.once.shape.ownSplitNeeded = false := by
  cases hc : (z.ranges.x.choice.masksRide && z.once.shape.choice.masksRide &&
      z.once.shape.sharedSplitNeeded && z.once.shape.masksAhead &&
      !z.once.shape.ownSplitNeeded) with
  | true =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
  | false =>
    exfalso
    unfold KeyPub.of at h
    simp [hc, guard] at h

/-- `KeyPub.of` reads four fields of the sizes only: sizes that agree in them give one value. -/
theorem of_reads {z z' : Plan.KeySized} {a : Nat} (h₁ : z.once.shape = z'.once.shape)
    (h₂ : z.ranges.x = z'.ranges.x) (h₃ : z.codes = z'.codes) (h₄ : z.once.input = z'.once.input) :
    KeyPub.of z a = KeyPub.of z' a := by
  unfold KeyPub.of
  rw [h₁, h₂, h₃, h₄]

variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hP : ReadOf Zp.pol Z)
  {cfg : ByteArray} {m : Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
  (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (descriptionFromSource X N P).planOk = true)

include hZ hP hm hX hp in
/-- **In scope, at the sized key in the answer of `madeAt` and at the number of answers in the
source's setting, `KeyPub.of` returns `fullPub`**, its value at the written sizes. -/
theorem pub_of_made : KeyPub.of m.p.chains.made.sized.key X.set.samples = fullPub := by
  rw [key_in_scope hZ hP hm, (five_in_scope hZ hP hm hX hp).1]
  rfl

include hZ hP hm hX hp in
/-- **In scope, `KeyPub.of` returns `fullPub` at every z whose four fields are those of the source's
one-time chain**, at the same number of answers. -/
theorem pub_of_source (z : Plan.KeySized) (h₁ : z.once.shape = X.Y.k.oneTime.lin)
    (h₂ : z.ranges.x = X.Y.k.oneTime.ranges) (h₃ : z.codes = X.Y.k.oneTime.codes)
    (h₄ : z.once.input = X.Y.k.oneTime.indexMasks) : KeyPub.of z X.set.samples = fullPub := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := five_in_scope hZ hP hm hX hp
  rw [e0]
  exact of_reads (h₁.trans e2) (h₂.trans e1) (h₃.trans e4) (h₄.trans e3)

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.of_flags
#print axioms AtPublicFiles.KeyBook.of_reads
#print axioms AtPublicFiles.KeyBook.pub_of_made
#print axioms AtPublicFiles.KeyBook.pub_of_source
