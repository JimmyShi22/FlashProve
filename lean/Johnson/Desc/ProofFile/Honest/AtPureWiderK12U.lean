-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK12U.lean: `widerFillOwnCP` (Honest/AtPureWiderK12.lean)
with one side more in the shared chain: the prover's side of the proximity test on G_u (the chain's
piece 9, of the kind K12). The side is its authors' `K12.AtProof.halfU`
(Honest/K12/AtProof/HalfU.lean), laid behind the chain's six other sides, and only where these are
made. Three definitions; ten short lemmas.

  `sharedWithU`        the six of `nowSharedBy`, then the authors' pair; no side at all where the
                       six are not made
  `widerFillOwnCPU`    `widerFillOwnCP` with that field `shared`
  `widerFillAtCPU`     `widerFillAtCP`'s sister
  `sharedWithU_ok`, `sharedWithU_error`   the two arms
  `sharedWithU_withHalfU`   where the six are made the field is that of the authors' own term,
                       `K12.AtProof.withHalfU` at this filling's reader
  `sixAt_is`           the authors' `K12.AtProof.sixAt` is `nowSharedBy`
  `widerFillOwnCPU_shared`, `_lots`, `_second`, `_enc`   the fields
  `atPure_storedWords`   at the prover that `onlineProverFromPublicFiles` returns, at any choice of fields, the stored
                       words are the filling's columns as words
  `atPure_key_pub`     and its key is the public part's

Why the arm. THE ARM IS LOAD-BEARING: NEVER LAY `halfU` WITHOUT IT. The job's authors (they are the
list's authors of Honest/AtPureWiderK12.lean) name two public tests that the job itself does not ask
(Honest/K12/JobShared.lean, head): `sendingsFit A.P`, «a named public hypothesis» of «every theorem
on a random value over these two jobs»; and `LinShape.ok`: at a shape that it refuses «`rowsOf` lays
an entry of the matrix where a pad of the index committer is due». The maker of the six rejects
where `OnBytes.linOk` or `K14.sendingsFit` says no (Honest/K14/Six.lean), at the same parameters
`p14At Z`; `S.ok` is the first conjunct of `linOk` (OnBytes/Iop/Lin.lean). So where the pair is laid
here both tests have passed (by reading these three texts; no lemma). At the authors' own term the
pair would stand alone where the six are not made.

Limits.
  * A SILENT DEFAULT: no side of the shared chain where `nowSharedBy` returns an error: the value
    that the field has in `widerFillOwn`. A second, the authors': no pair where `K12.AtProof.four`,
    `K12.AtProof.sendPub` or `Desc.K14.blocks` gives nothing (by reading, none of the three is met
    where the six are made: so there the pair is laid). Both read the public part alone.
  * THE TWO PARTS CANNOT REFUSE (Honest/K12/Parts.lean): having a side is no ground. No word
    «plays», «accepted» or «tested», and no count, without, at the same stand, by name:
    `K12.AtProof.atHandAtU … = true` (the job's authors'; in no file that was read for this one) ·
    `nowSharedBy … = .ok six` · the five steps of the verifier's above the state on entry return
    (`TestJob.recB`, Honest/K12/Test.lean; Johnson/Desc/K12/Honest/Stages.lean) · `masksAhead` and
    `sharedSplitNeeded` · the stages in the shape are those of the test's parameters. Owed beside
    these: two stages or more, which the text of `halfU` does not ask. Under the head, by the job's
    authors' word: `masksAhead` and `sharedSplitNeeded` are true (`facts_at_head`,
    Honest/K12/NearAtHead.lean), and the test's stages are five written ones (`stages_at_head`,
    Honest/K12/StagesAtHead.lean). Neither is imported here by name (NearAtHead.lean lies beneath
    Honest/K12/AtProof/HalfU.lean), and neither was read for this file.
  * FOUR MORE KINDS OF SILENT DEFAULTS STAND IN THE PROVER's SEALED TEXT ABOVE THE STATE ON ENTRY,
    general in the job (found by the job's authors): `lastOut` takes the claim
    `⟨#[], #[], (0, 0, 0)⟩` where the stage or its claim is not found
    (Johnson/Prover/Link/BodyAll.lean; Johnson/Desc/K12/Honest/Stages.lean) · `rowOf t` is `{}`
    where the record passes no claim (BodyAll.lean) · `aAns` reads a stage and an element by
    defaults (Stages.lean) · challenges are read by `.elems.headD (0, 0, 0)` (`aPoint`, Stages.lean;
    `lastOut`). The first two hang on the record. The test on the state on entry covers none.
  * Where the fold over the eight sub-protocols in front, or the way in, refuses, the state on entry
    falls back, without a warning, on a state that is not shown to be the verifier's, and the parts
    send all the same. A front that shows more rounds than the eight take gives the same state.
  * What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
    no theorem): «atHandAtU reads the key and,
    through enc, the index and the committer's values: its verdict is a function of the private
    input: a test for us, never a thing that a simulator or a page may be said to know.»
  * The job reads the stored table's columns at "LOC"'s positions; these are computed from the
    index. Never a word on a simulator at this place without «given the stored table's columns
    opened at "LOC"'s positions».
  * The filling's columns are nothing just at another item than 0, where `rowsFit` fails, and from
    2^a on: the public part, the item and the position alone: `encW_item`, `encW_unfit`,
    `encAt_beyond`, `encW_fit` (Johnson/Bind/ForProver/Laws.lean) and `encW_some`
    (Johnson/Bind/ForProver/Declared.lean), their authors'. Not imported here.
  * The job's rows never refuse; they read by defaults (Honest/K12/JobShared.lean): where message 1
    of a sending does not exist the member has no rows, without a warning.
  * The job's authors' head (Honest/K12/JobShared.lean): «o_sp's values stand in three places of the
    shared chain: they go into both jobs, and the round "SPLIT" spends entry 0 of its mask row»: the
    job at the test on G_u (`jobAtU`), the job at the test on G_omega (`jobAtOmega`), and that
    round. Of a member's values in the job and in the sending: «That the two are the same values is
    up to whoever gives the test's parts their random values; it is not checked here.» Owed before
    any count at the pair: the lending at this filling's book, by a law: one owner and one start
    for each carried stretch; and that it is one coin that stands at these three places, each by
    name.
  * A DUTY OF THE CALLER THAT THE JOB's AUTHORS NAME (Honest/K12/JobShared.lean, Limits): «That A is
    the one of `proverSidesOfSharedSendings` in the same prover's side is up to the caller too: its field `atPoint`,
    the number of the round "LIN point", is compared with nothing.» `sharedWithU` is that caller.
    The job's A (`K12.AtProof.sendPub Z`) and the A of the six's sendings (`K14.sixOf`, by `dataOf`)
    are made by two texts; that they are one (P of `p14At Z`; `atPoint` the rounds in front of
    `K14.place 1` in the shared chain's list) is read, not proved. The like of the reader of the
    committer's values.
  * That `onlineProverFromPublicFiles` returns at these choices of fields (no side may be a stray), that `ready` does,
    that a part plays or is accepted: none is stated here.
  * All limits of Honest/AtPureWiderK12.lean and of Honest/K12/AtProof/HalfU.lean hold here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ X : Type}

/-! ## 1 The definitions -/

/-- **The shared chain's sides: the six, then the pair at the test on G_u.** A SILENT DEFAULT: no
side at all where the six are not made. THE ARM IS LOAD-BEARING: NEVER LAY `halfU` WITHOUT IT: where
the six are made `OnBytes.linOk` and `K14.sendingsFit` have passed (by reading; no lemma), which the
job's authors name and the job itself does not ask; at a shape that `LinShape.ok` refuses «`rowsOf`
lays an entry of the matrix where a pad of the index committer is due»
(Honest/K12/JobShared.lean). One reader of the index at all three places. THE TWO PARTS CANNOT
REFUSE: having a side is no ground that they play. -/
def sharedWithU (I : WiderIn W₀) (Z : Pub) :
    List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit) :=
  match nowSharedBy (I.weights Z) Z with
  | .ok six =>
    six ++ K12.AtProof.halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z
  | .error _ => []

/-- **`widerFillOwnCP` with the pair at the test on G_u behind the shared chain's six.** The
arguments are `widerFillOwn`'s. -/
def widerFillOwnCPU (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwnCP own₀ L I o S O with shared := fun Z _ => sharedWithU I Z }

/-- **`widerFillAtCP`'s sister with that pair.** -/
def widerFillAtCPU (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnCPU () (LongLots.plain o S O) I o S O

/-! ## 2 The two arms -/

/-- **Where the six are made**: the six, then the authors' pair. -/
theorem sharedWithU_ok (I : WiderIn W₀) {Z : Pub}
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    (h : nowSharedBy (I.weights Z) Z = .ok six) :
    sharedWithU I Z =
      six ++
        K12.AtProof.halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z := by
  show (match nowSharedBy (I.weights Z) Z with
    | .ok six =>
      six ++ K12.AtProof.halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z
    | .error _ => []) = _
  rw [h]

/-- **Where they are not made**: no side. -/
theorem sharedWithU_error (I : WiderIn W₀) {Z : Pub} {e : String}
    (h : nowSharedBy (I.weights Z) Z = .error e) : sharedWithU I Z = [] := by
  show (match nowSharedBy (I.weights Z) Z with
    | .ok six =>
      six ++ K12.AtProof.halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z
    | .error _ => []) = _
  rw [h]

/-- **Where the six are made the field is that of the authors' own term at this filling's reader.**
-/
theorem sharedWithU_withHalfU (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Z : Pub} (G : Ground)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    (h : nowSharedBy (I.weights Z) Z = .ok six) :
    sharedWithU I Z =
      (K12.AtProof.withHalfU (widerFillOwnCP own₀ L I o S O) I.weights).shared Z G := by
  rw [sharedWithU_ok I h]
  show _ = (nowSharedBy (I.weights Z) Z).toOption.getD [] ++
    K12.AtProof.halfU (I.weights Z) (fun w => Bind.ForProver.encW Z (I.weights Z w)) Z
  rw [h]
  rfl

/-- The authors' second text of the six's maker is `nowSharedBy`. -/
theorem sixAt_is (wt : W₀ → Weights) (Z : Pub) : K12.AtProof.sixAt wt Z = nowSharedBy wt Z := rfl

/-! ## 3 The choice of fields -/

/-- The field `shared`. -/
theorem widerFillOwnCPU_shared (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (widerFillOwnCPU own₀ L I o S O).shared Z G = sharedWithU I Z := rfl

/-- The field `lots` is `widerFillOwnCP`'s. -/
theorem widerFillOwnCPU_lots (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPU own₀ L I o S O).lots = (widerFillOwnCP own₀ L I o S O).lots := rfl

/-- The field `second` is `widerFillOwnCP`'s. -/
theorem widerFillOwnCPU_second (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCPU own₀ L I o S O).second = (widerFillOwnCP own₀ L I o S O).second := rfl

/-- The field `enc`: the columns that the pair is laid at. -/
theorem widerFillOwnCPU_enc (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) :
    (widerFillOwnCPU own₀ L I o S O).enc Z = fun w => Bind.ForProver.encW Z (I.weights Z w) := rfl

/-! ## 4 At the prover that `onlineProverFromPublicFiles` returns -/

/-- **The stored words are the filling's columns as words**, at any choice of fields. -/
theorem atPure_storedWords {Rc Tr X₀ Y : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ Y} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (w₀ : W₀) (rc : Rc) (item x : Nat) :
    A.H.storedWords w₀ rc item x = (P.enc A.Z w₀ rc item x).map (·.map OnBytes.Slice.ofF) := by
  show (A.H.stored w₀ rc item x).map (·.map OnBytes.Slice.ofF) = _
  rw [(atPure_ok h).2.2.2.2.1]

/-- **The key is the public part's**, at any choice of fields. -/
theorem atPure_key_pub {Rc Tr X₀ Y : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ Y} {A : OnlineProverWithDescription W₀ Rc Tr X₀ Y} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (x : Inst) : A.H.key x = x.pub.key := by
  rw [(atPure_ok h).2.2.2.2.2.2.1]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.sharedWithU
#print axioms ProofFile.Honest.widerFillOwnCPU
#print axioms ProofFile.Honest.widerFillAtCPU
#print axioms ProofFile.Honest.sharedWithU_ok
#print axioms ProofFile.Honest.sharedWithU_error
#print axioms ProofFile.Honest.sharedWithU_withHalfU
#print axioms ProofFile.Honest.sixAt_is
#print axioms ProofFile.Honest.widerFillOwnCPU_shared
#print axioms ProofFile.Honest.widerFillOwnCPU_lots
#print axioms ProofFile.Honest.widerFillOwnCPU_second
#print axioms ProofFile.Honest.widerFillOwnCPU_enc
#print axioms ProofFile.Honest.atPure_storedWords
#print axioms ProofFile.Honest.atPure_key_pub
