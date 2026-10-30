-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeJoinAtFiles.lean: at three public files Z, under the hypotheses that are listed below, one
value of three honest provers, `proversOf hT hL (famG …)`, meets these structures. On the acceptance
side: `OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean), which is what the prover of a
whole request asks of three honest provers and three families of falls (`Falls`: sets of verifier
randomness that are set aside on the acceptance side). On the privacy side: the structures on
provers of the statement of index privacy (`OnBytes.WholeKey`, Johnson/WholeKey/Premises.lean):
`ExtEnc`, `Sims.Good`, `StopsSmall`, and the clause on the session's prover of `RunVals`. The
session's prover, the third of the three, is the family `famG` of one request's honest provers, one
for each number of a stored copy (below: the number). It is built by `ProofFile.Honest.honestBatchProverOfFile` from a
description (the IOP of the proof file as written in Lean: `descZ Zp Np cF`), a book of coins B
(`ProverCoinCounts`), rows G (`Sides`: for each sub-protocol the prover's part and its simulator) and a prover
structure H (`ProofFile.Honest.Prover`). hT and hL, the key file's prover and the link's, are free
parameters. The object and the wiring are those from which the verifier is compiled (`protocolAtFiles Z`,
`(lettersZ Z c₀ m₀).W`).

How general. `honFit_atFiles` and `both_atFiles` are stated in scope (`InScope Z = true`), where the
IOP's own test on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`), at a description that
`LaidAt` (Johnson/P5J/LaidOpens.lean) ties to Z. `extEnc_join`, `stops_join`, `good_join` and
`runVals_join` take none of these three hypotheses: they hold at every Z (where that test rejects,
only nominally: Limits of E2E/BridgeAlong.lean) and at every (Zp, Np, cF), `stops_join` and
`good_join` at those that meet `ItemsZero` (see hit, below). All hold at the wiring of every pair of
a digest c₀ and a further reading m₀; the wiring does not depend on the pair (`wiring_any`,
E2E/BridgePremWLink.lean). Yes is any relation that implies the object's own relation `RyesZ Z`. In
`HonFit`, S is any structure of the OOD-seed wire (`SdOf`) whose test on the number reads the front
round's number (`NumReads`); the compiled verifier's own structure is one (`num_letters`).

  `both_atFiles`: one conjunction of `HonFit`, `ExtEnc`, `StopsSmall`, `Sims.Good` and `RunValsB`,
    all five at the one value `proversOf hT hL (famG …)`, with one wiring and one relation Yes
  `honFit_atFiles`: `HonFit` at that value and at the falls `fallsOf … (guardFall Zs (fallG …))`;
    the bound for the session's prover is zB + z + pF. Zs: the OOD seeds that are set aside, given
    the index and the committer's randomness: no acceptance is asked there
  `good_join`: `Sims.Good` at that value, the session's clause at error 0, from `ExactAt`
  `stops_join`: `StopsSmall` at that value, the session's clause at z, from `HidSmall`
  `extEnc_join`: `ExtEnc` at that value, from the two equations on the external strings of hT and hL
  `RunValsB`, `runVals_join`: a definition: the clause on the session's prover of `RunVals` at that
    value, as the statement of index privacy has it (in the range ok, outside the abort set): the
    run values are in the plain parts of the honest run; it holds, with no hypothesis
  `famG_eq`: `famG` is `onlineProversOfCommitter` (E2E/BridgeTied.lean) at the prover structure `G.prover H`: by
    unfolding
  `TiedYes`, `TiedOut`, `TiedIn`: definitions: relations between a number, a private input and an
    instance. `TiedYes`: the instance is what `instanceAsPlainRecord` writes for a request of Yes at the index,
    with this private input's own OOD sample, and the pair is tied (`TiedG`,
    E2E/BridgeLinkAtFiles.lean). `TiedOut` adds that the OOD seed is outside Zs; `TiedIn` adds to
    `TiedYes` that the index is in ok and the OOD seed in Gs
  `validYes`, `validOut`, `validIn`: under hY and hit: for an index and a request of Yes, at every
    number and committer's randomness, the private input and what `instanceAsPlainRecord` writes meet `TiedYes` at
    every OOD seed (`ValidTied`), `TiedOut` at the seeds outside Zs (`ValidTiedZ`), and `TiedIn` at
    the indices of ok and the seeds of Gs (`ValidTied`)
  `FirstAt`, `firstAt_of_one`: a definition: the description's first test `okStart` accepts every
    instance of a relation; in scope, under `LaidAt`, it holds at `TiedOut` if that test accepts one
    written instance
  `ThreadsAt`, `PlainAt`, `ServesAt`: definitions: three hypotheses of `honFit_atFiles`, see below
  `RowsAt`, `rowsAt_of`: a definition: at every input of a relation and at all purses (`Purse`: the
    coins of one chain's parts) `ready` returns, `PlanServes` holds, and there is a value of
    `ThreadsC` with the rows' own lists of falls; at `TiedOut` it follows from `ThreadsAt`,
    `PlainAt`, `ServesAt`, the plan's test `planOk` and `DataFits`
  `servesAt_of`: `ServesAt Z H Yes` follows from `Serves Z H` (E2E/ReadyAtFiles.lean)
  `hidSmall_in`: `HidSmall` at `TiedYes` gives `HidSmall` at `TiedIn`, with the same bound
  `extIsEnc_famG`: the family's external strings are the object's encoded index (`ExtIsEnc`)
  `width_extZ`, `stored_of_tied`: every column of the committer's string has the encoder's width; at
    a tied input the stored columns are at hand at the declared widths
  `NumReads`, `num_letters`: see How general
  `protocolAtFiles`, `lettersZ`, `dataZ`, `chainsZ`, `descZ`, `WZ`, `CoinG`, `pursesOf`, `provG`, `famG`,
    `fallG`: abbreviations for long terms. `provG` is H with the committer's columns as its stored
    table at the item 0 only, with the committer's key (`Committer.proverAt` at 0,
    Johnson/Desc/ProofFile/Honest/CommitterAt.lean), and with the rows G as its parts

Files that import this one: E2E/BridgePremW.lean, E2E/BridgePremWCoins.lean and
E2E/BridgePremWKey.lean have terms of all hypotheses of the statement of index privacy (`PremW`) at
this family. E2E/CompleteAsIOPByYes.lean takes a value of `HonFit` at this family to completeness in
parts (`parts_of_yesDebts`: under hf, which `workFaithful_atFiles` (E2E/CompleteAsIOPWorkBits.lean)
has, and `YesDebts`, whose fields are hypotheses). Next to this file, general in the object and the
family: E2E/BridgeSeeds.lean has a tie of the two sets of OOD seeds.

By what. `honFit_atFiles` is one call of `honFit_link` (E2E/BridgeJoin.lean), which calls
`honFit_of` (E2E/BridgeAccept.lean). The five clauses of `HonFit` on the session's prover:
  `accB`, its hypotheses: `validOut` turns "Yes holds of index and request, and the OOD seed is not
    set aside" into `TiedOut`, at every number
  `accB`, its conclusion: `accAtTied_of_yes` (E2E/BridgeLink.lean), through the theorem on the
    compiled verifier's slot (`LPFFrame.frame_at_slot`, Johnson/LPFFrame/Proofs.lean), which deals
    with the nonces and the test bits. Its hypotheses other than `YesAt` are proved at Z in
    E2E/BridgeLinkAtFiles.lean. `full_atFiles`: every stored table's part of a round's draws has as
    many draws as it says. `carries_atFiles`: the external string carries its positions.
    `run_atFiles`: where the description's decision accepts what is written, so does the object's;
    here `LaidAt` ties the description to Z. `sil_atFiles`: the test on the three rounds without a
    challenge accepts, at all run values. `YesAt` comes from `yesAt_of_debts` (E2E/BridgeLink.lean),
    which calls `ProofFile.Honest.yes_at_stratC` (Johnson/Desc/ProofFile/Honest/Law/ThreadStratC.lean)
  for `yesAt_of_debts`, of the description: `planOk` (a field of `LaidAt`); `dataFits_atFiles` and
    `due_atFiles` (E2E/BridgePaidAtFiles.lean); `firstAt_of_one`, by `AtPublicFiles.Start.okStart_of_one`
    (E2E/StartInScope.lean)
  for `yesAt_of_debts`, of the rows: `rowsAt_of`. That `ready` returns at all purses:
    `ProofFile.Honest.ready_any` (Honest/Law/ReadyAny.lean). `PlanServes`: `ProofFile.Honest.planServes`
    (Honest/Law/PlanGives.lean); its hypothesis that the stored columns are at hand at their widths
    comes from "tied" by `stored_of_tied`, with the plan's test, `DataFits` and `width_extZ` (by
    `ext_obj` and `enc_col`, E2E/TiedAtFiles.lean)
  `extB`, and the clause on the session's prover of `ExtEnc`: `extIsEnc_famG`, by `ext_obj`: the
    committer's string is the object's encoded index
  `whB`: `withheldZero_along` and `fallZero_along` (E2E/BridgeFalls.lean): neither the abort set
    (`withheld`: `Bad` together with `Hid`) nor the fall depends on the test bits
  `prB`: `prB_of` (E2E/BridgeAccept.lean): a bound for a union, from hb, hz and hf
  `num`: `num_link` (E2E/BridgeJoin.lean): the front round holds the number, and nonces do not
    change it
The privacy side: `extEnc_of`, `stops_of_small` and `good_of_exact` (E2E/BridgePrivacy.lean), with
`hidZero_link` (E2E/BridgeJoin.lean) and `ExactAt.re` (E2E/BridgeAlong.lean). `runVals_join`:
`runVals_tied` (E2E/BridgeTied.lean), which has the equation at every verifier randomness. "Tied" in
the three relations: `validTiedG_atFiles` (E2E/BridgeLinkAtFiles.lean). `servesAt_of`: `Serves.both`
(E2E/ReadyAtFiles.lean). In `proversOf` the session's prover is `Family.glue`
(E2E/HonestFamily.lean): one honest prover with the number inside its private input; the type of its
coins does not depend on the number.

Hypotheses of `honFit_atFiles`. scope, live, L: see How general. hS: `NumReads`. hY: Yes implies
`RyesZ Z`. g: `NineFit` (E2E/BridgeAccept.lean): the nine clauses of `HonFit` on the key file's
prover, on the link's, and on the measure ζ of the seeds set aside; there the measures of these two
provers' abort sets and falls are asked at all OOD seeds, those set aside included. h₀, public: the
description's first test accepts one written instance. Then, in scope, it accepts all: at written
instances its verdict depends on no relation, prover, row, coin, request or OOD seed (it does read
the OOD seeds and answers: they pass by their type). Q: `PlainAt`: three Bool-valued tests (one on
the description's sealing round, two on the description and the rows); two public statements on the
declared rounds (no round asks for more non-zero elements than elements, which is a hypothesis here
and a theorem in scope under `LaidAt`: `nonZero_atFiles`, E2E/BridgeNonZero.lean; every stored table
has the encoder's width); and `ready` returns once, at some input and purses. Sv:
`ServesAt Z H Yes`: at the requests of Yes the prover structure H accepts the index and has a trace
at what is written, at every OOD sample (`Serves`, from which it follows, asks the trace at the
object's whole relation and the test on the index at every matrix in range). hthr: `ThreadsAt` at
`TiedOut`: the invariants of all sub-protocols (`ThreadsC`), with the rows' own lists of falls, at
every input of `TiedOut` and all purses at which `ready` returns. They contain, sub-protocol by
sub-protocol, "this sub-protocol's step accepts outside its fall" and, with no fall, the second
chain's start and the last test. So the theorem is one of composition: these compose at the
strategy's own transcript, and go through nonces, test bits, reads and the object's decision up to
`AccLaw`. hb: the measure of the public abort set `Bad` is at most zB. hz: the measure of the abort
set `Hid`, which may depend on the private input, is at most z, at the requests of Yes at all OOD
seeds (`TiedYes`). hf: the measure of the fall at each fixed coin is at most pF, at `TiedOut`. Every
hypothesis on the session's prover's acceptance is asked at `TiedOut` only, but for `ServesAt`,
which is asked at every OOD sample: at a seed that is set aside, nothing else is asked of that
prover but the measure of its own abort set.

Further hypotheses of `both_atFiles`. s, gd: values of `StopsSmall` and `Sims.Good` at any families
Fm₂, Fm₃ in the place of `famG`: their two clauses each on the key file's prover and the link's are
handed through. hz': the measure of `Hid` is at most z', at `TiedIn`; z' := z can always be taken
(`hidSmall_in`), and a z' of its own only allows a finer bound. hx: `ExactAt` at the description's
own instances, at the inputs of `TiedIn`: outside `Hid` the honest output is the named simulator's.
E2E/BridgeExact.lean, which imports this file, has it from a conditional lemma on one slot.

The hypothesis hit of `validYes`, `validOut`, `validIn`, `stops_join` and `good_join`:
`AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)` (E2E/ItemsZero.lean): every stored table that a round of the
description declares is under the item 0, which is where `provG` has the committer's columns.
`honFit_atFiles` and `both_atFiles` prove it from the field `data` of `LaidAt`, by
`itemsZero_of_data`.

Limits.
- Conditional. No rows G are shown to meet `ThreadsAt`; none of the public hypotheses is shown of
  any Z; no measure is shown. No value is shown to meet all hypotheses of `both_atFiles` together,
  not even a small made-up one. Where zB + z + pF ≥ 1, ζ ≥ 1, pT ≥ 1, pL ≥ 1 or z' ≥ 1, the clause
  with that bound is vacuous. With Zs set to all seeds the hypotheses on acceptance hold vacuously,
  and the price is ζ ≥ 1.
- There are two sets of OOD seeds, which nothing ties to each other in `both_atFiles`: Zs (set
  aside, for acceptance; it may read the index and the committer's randomness) and Gs (good, for
  privacy). Where every seed of Gs is set aside the two sides share no seed. Only a small ζ and a
  small chance of a seed outside Gs together, at one S, guard against that; the second of these does
  not occur in this file. A tie is in E2E/BridgeSeeds.lean: with Zs set to "outside Gs" the two
  sides speak of the same seeds and ζ is that chance. With Gs or ok set to a predicate that never
  holds the privacy side is vacuous.
- The price of one relation: Yes is a free parameter on both sides, and it may read the index. The
  simulator is bound with Yes and ok, not before them: at a Yes (or ok) that holds at one index only
  the simulator may lean on that index, and `Sims.Good` then says nothing on hiding the index.
  (Where `ExactAt` is had from `exactAt_of_owed`, E2E/BridgeExact.lean, the simulator reads none of
  Yes, ok and Gs.) With Yes set to a relation that never holds the session's clauses are vacuous on
  both sides. Of requests in `RyesZ Z` outside Yes nothing is said. The tie that the library's
  `bundle_argW` (Johnson/WholeKey/Bundle.lean) asks next to `PremW`, "every index with a true
  instance is in the range ok", is not asked here.
- S is any structure, and it is not tied to the verifier's own OOD-seed wire: its map from digests
  to seeds is a free field: at a constant map, ζ = 0 is met with all seeds but one set aside.
  `HonFit` speaks of the compiled verifier only at that verifier's own structure.
- No valid pair is shown at any Z: where no request holds at any index the clauses on acceptance are
  vacuous. The index type is every matrix of the full size's shape; `RyesZ Z` contains "the matrix
  is in range", and it is the relaxed relation: some trace is within the bounds.
- In `honFit_atFiles` and `both_atFiles` the description is tied to Z; the rows G, the prover
  structure H and the book of coins B are free parameters. R₂ and R₃ are any finite types with codes
  run₂, run₃ into bytes: that the codes hit the values that a byte format accepts, and all of them,
  is not treated.
- The lists of falls (`G.falls₁`, `G.falls₂`, `G.falls₃`; a `ProofFile.Honest.Fall` is a computable test
  at a sub-protocol's place, and it fires where that test returns something) are free fields of the
  rows G. A fall that always fires makes the statement on acceptance (`accB`) vacuous. At a
  sub-protocol without a round, a fall whose test is "this sub-protocol's own step rejects" makes
  "no fall fires along the run" contain a part of the conclusion. So that statement says something
  at a sub-protocol only next to each fall's text and its measured share (`FallSmall`, at each fixed
  coin): without that measure it says nothing there.
- The form: a fall depends on the prover's coins: it is a second set, which reads the coin, for
  completeness only, and it is not folded into the abort set. `HonFit` asks acceptance at every coin
  outside the abort set and the fall at that coin, and the measure at each fixed coin; a mean over
  the coins of these bounds then bounds the error over verifier randomness and coins jointly, which
  is how the goals measure. It does not bound the set of verifier randomness at which some coin
  falls.
- `HonFit` has a parameter for OOD seeds that are set aside, given the index and the committer's
  randomness; it has none for committer's randomness and none for purses: one purse at which a fall
  fires at nearly every verifier randomness forces pF to 1, and one seed at which the measure of the
  abort set `Hid` is large forces z up, whatever Zs is.
- Who picks the number is not said (Limits of E2E/BridgePrivacy.lean). "Error 0" in `Sims.Good` is
  no result by itself (same Limits).
- The instance holds the OOD sample, and the front round and the joining round show its answers:
  what a sample tells of the index is not treated in this file. The statement on samples and opened
  positions (the field `hidE` of `ReadsG`, Hiop/Seeded/Game.lean, which the term of `PremW` in
  E2E/BridgePremW.lean holds next to `Sims.Good`; E2E/TablesAtOwnObject.lean) is not joined to
  `ExactAt` here. The statement of index privacy takes both among its premises (the fields `reads`
  and `good` of `PremW`, Johnson/WholeKey/Premises.lean); that they hold together at this family is
  not shown in this file.
- The description's test on the three rounds without a challenge (the parameter `silent`) is set to
  `silInst` (E2E/TiedAtFiles.lean); no proof here uses which test it is.
- No theorem of this folder says that the IOP's own tests on the public files pass at any files.
- The limits of E2E/BridgePrivacy.lean, E2E/BridgeAccept.lean, E2E/BridgeFalls.lean,
  E2E/BridgeLink.lean, E2E/TiedAtFiles.lean, E2E/StartAtFiles.lean, E2E/StartInScope.lean and
  E2E/ReadyAtFiles.lean hold here too.
- Neither the theorem on completeness nor the statement of index privacy is called here: what is
  concluded are hypotheses of these two.
-/
import E2E.BridgePaidAtFiles
import E2E.BridgeTied
import E2E.StartInScope
import E2E.ReadyAtFiles
import Johnson.Desc.ProofFile.Honest.Law.ReadyAny
import Johnson.Desc.ProofFile.Honest.Law.PlanGives

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (SgX)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages Tied)

/-- At a tied input the stored columns are at hand at their widths, where no declared stored table
is deeper than the data's depth (ha) and the external string's columns have the declared width (hw).
-/
theorem stored_of_tied {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} [Inhabited R₃] {D : WholeD}
    {F : VerifiableInference.Desc.FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {J : R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3}
    {ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str} {pubJ : R₂ → R₃ → Xi → TF × TJ × T3}
    {sh : Ky → F.S₂} {Rel : W₀ → Rc → Xi → Prop} {w : W₀ × Rc × Sd} {x : Xi}
    (ht : Tied D F H J ext pubJ sh Rel w x)
    (ha : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, t.sh.a ≤ D.a)
    (hw : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, ∀ p,
      ((ext w p).2).length = t.sh.W) :
    ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
      ∃ u, H.storedWords w.1 w.2.1 t.item y = some u ∧ u.length = t.sh.W :=
  fun d hd t htm y hy =>
    have h : y < 2 ^ D.a := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (ha d hd t htm))
    ⟨_, ht.table d hd t htm y h, hw d hd t htm ⟨y, h⟩⟩

end AtPublicFiles.Bridge

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse Coins Tied halvedAll sealPlain rootedAll ready PlanServes
  ThreadsC)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.Prover (HonFit)
open OnBytes.WholeKey (ExtEnc StopsSmall Sims)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/-! ## Abbreviations for long terms; Lean unfolds them by itself -/

/-- The library's object at Z. -/
abbrev protocolAtFiles (Z : PublicFiles) := (filesAt Z).withProvers (dataAtFiles flashProveData Z).P

/-- The parameters of the compiled verifier at Z, a digest c₀ and a further reading m₀. -/
abbrev lettersZ (Z : PublicFiles) (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) :=
  (dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀

/-- The data of the proof file's rounds in the object at Z. -/
abbrev dataZ (Z : PublicFiles) : WholeD := (dataAtFiles flashProveData Z).DP.at frS.P.T.a

/-- The three chains of the proof file's protocol at Z. -/
abbrev chainsZ (Z : PublicFiles) :=
  OnBytes.Maker.chainsOf (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
    (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty

/-- The description built from (Zp, Np, cF). -/
abbrev descZ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :=
  F0T OnBytes.secondHashFunction Zp Np cF

/-- The private inputs of the session's prover at Z, without the number: an index, the committer's
randomness and an OOD seed. -/
abbrev WZ (Z : PublicFiles) : Type := FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed

/-- The prover's coin: a purse and a run value for the shared part; two purses and a run value. -/
abbrev CoinG (B : ProverCoinCounts) (R₂ R₃ : Type) : Type :=
  (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)

/-- The run's coins in it: the three purses. -/
abbrev pursesOf {B : ProverCoinCounts} {R₂ R₃ : Type} (c : CoinG B R₂ R₃) : Coins B :=
  ⟨c.2.1.1, c.1.1, c.2.1.2⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- The prover structure H with the committer's columns as its stored table at the item 0, no column
at any other item, and the committer's key (`Committer.proverAt` at 0), and with the rows G as its
parts (`Sides.prover`). -/
abbrev provG := G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)

/-- The family of the session's honest provers at Z, by the copy's number. -/
abbrev famG :=
  famL (P := (dataAtFiles flashProveData Z).P) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)

/-- Its falls: at a number, a private input, an instance and a coin, the set of verifier randomness
at which the honest run meets one of G's falls: `fallAt` returns something (`fallBC`,
E2E/BridgeFalls.lean). -/
abbrev fallG :=
  fallL (P := (dataAtFiles flashProveData Z).P) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)

/-- `famG` is `onlineProversOfCommitter` (E2E/BridgeTied.lean) at the prover structure `G.prover H`: by unfolding. -/
theorem famG_eq :
    famG Z Zp Np cF run₂ run₃ B G H = onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P
      (G.prover H) := rfl

/-! ## The relations -/

/-- The instance is what `instanceAsPlainRecord` writes for a request of Yes at the index, with the OOD sample of
this private input; and the pair is tied (`TiedG`). -/
def TiedYes (Yes : FullSizeMatrix → XF → Prop) (n : ℕ) (w : WZ Z) (x : ProofFile.Inst) : Prop :=
  (∃ x', Yes w.1 x' ∧ x = instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) ∧ TiedG Z Zp Np cF run₂ run₃ B
    G H n w x

/-- `TiedYes`, and the OOD seed is not set aside. -/
def TiedOut (Yes : FullSizeMatrix → XF → Prop) (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed) (n : ℕ) (w : WZ Z)
    (x : ProofFile.Inst) : Prop :=
  w.2.2 ∉ Zs w.1 w.2.1 ∧ TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w x

/-- `TiedYes`, with the index in the range ok and the OOD seed in the set Gs. -/
def TiedIn (Yes : FullSizeMatrix → XF → Prop) (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) (n : ℕ) (w : WZ Z)
    (x : ProofFile.Inst) : Prop :=
  ok w.1 ∧ Gs w.2.2 ∧ TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w x

variable {Yes : FullSizeMatrix → XF → Prop}

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
theorem validYes (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) :
    ValidTied (L := protocolAtFiles Z) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (instanceAsPlainRecord a)) (fun
                                  _ => True)
      (fun _ => True) Yes :=
  fun n i r e x _ _ hx =>
    ⟨⟨x, hx, rfl⟩,
      validTiedG_atFiles Z Zp Np cF run₂ run₃ B G H hit n i r e x trivial trivial (hY i x
      hx)⟩

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
theorem validOut (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (Zs) :
    ValidTiedZ (L := protocolAtFiles Z) (fun n w a => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a))
      Yes Zs :=
  fun n i r e x hx he => ⟨he,
    validYes Z Zp Np cF run₂ run₃ B G H hY hit n i r e x trivial trivial hx⟩

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
theorem validIn (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (ok) (Gs) :
    ValidTied (L := protocolAtFiles Z) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (instanceAsPlainRecord a))
      ok Gs Yes :=
  fun n i r e x hi hg hx => ⟨hi, hg, validYes Z Zp Np cF run₂ run₃ B G H hY hit n i r e x trivial
    trivial hx⟩

/-! ## The first test: a public hypothesis -/

/-- The description's first test accepts every instance of the relation. -/
def FirstAt (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  ∀ n w x, TiedX n w x → (descZ Zp Np cF).okStart x = true

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
/-- In scope it follows from one accept: where the first test accepts one written instance it
accepts all (`AtPublicFiles.Start.okStart_of_one`, E2E/StartInScope.lean). -/
theorem firstAt_of_one (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true) (Zs) :
    FirstAt Z Zp Np cF (TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs) := by
  intro n w x h
  obtain ⟨x', -, rfl⟩ := h.2.1
  obtain ⟨z₀, hz₀⟩ := h₀
  exact AtPublicFiles.Start.okStart_of_one scope L hz₀ _

/-! ## What is asked of the rows -/

/-- What is asked of the rows, at all purses: `ready` returns; `PlanServes` holds; there is a
value of `ThreadsC` (the invariants of all sub-protocols) with the rows' own lists of falls. -/
def RowsAt (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  ∀ n w x (c : CoinG B R₂ R₃), TiedX n w x →
    ∃ R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w.1 w.2.1 x (pursesOf c) = .ok R ∧
      PlanServes (provG Z Zp Np cF B G H) w.1 w.2.1 R ∧
      ∃ Thr : ThreadsC (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w.1 w.2.1 x (pursesOf c) R,
        Thr.f₁ = G.falls₁ ∧ Thr.f₂ = G.falls₂ ∧ Thr.f₃ = G.falls₃

/-- A value of `ThreadsC` (the invariants of all sub-protocols) with the rows' own lists of falls,
wherever `ready` returns. -/
def ThreadsAt (TiedX : ℕ → WZ Z → ProofFile.Inst → Prop) : Prop :=
  ∀ n w x (c : CoinG B R₂ R₃) R, TiedX n w x →
    ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w.1 w.2.1 x (pursesOf c) = .ok R →
      ∃ Thr : ThreadsC (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w.1 w.2.1 x (pursesOf c) R,
        Thr.f₁ = G.falls₁ ∧ Thr.f₂ = G.falls₂ ∧ Thr.f₃ = G.falls₃

/-- What is asked of the description and the rows next to the invariants: three Bool-valued tests,
two statements on the declared rounds, and that `ready` returns once. -/
structure PlainAt : Prop where
  /-- the sealing round (the first chain's last declared round) states no item but roots, and no
  root -/
  plainSeal : sealPlain (descZ Zp Np cF) = true
  /-- the prover has a part (`Placed`) for each sub-protocol that states an item that is no root -/
  halved : halvedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true
  /-- the prover has a part (`Placed`) for each sub-protocol that sends a root -/
  rooted : rootedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true
  /-- no declared round asks for more non-zero elements than elements -/
  nonZero : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
    (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE
  /-- every declared stored table has the encoder's width -/
  width : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
    (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, t.sh.W = 2 ^ frS.P.v
  /-- `ready` returns once, at some input and purses -/
  ready₁ : ∃ w₀ rc x k R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R

/-- Every column of the committer's string has the encoder's width, at every private input. -/
theorem width_extZ (w : WZ Z) (p : Fin (2 ^ (dataZ Z).a)) :
    ((extZ Z w p).2).length = 2 ^ frS.P.v := by
  have e : extZ Z w = encAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 := ext_obj Z (dataAtFiles flashProveData Z).P w
  rw [e, enc_col]
  simp [colF]

/-- Two of the tests of `ProofFile.Honest.ready`, those that read the index or the instance, at the
requests of Yes: the prover's test on the index accepts, and it has a trace at what is written, at
every OOD sample. By themselves these two do not make `ready` return: `rowsAt_of` also takes the one
return of `ready` in `PlainAt`. -/
def ServesAt (Yes : FullSizeMatrix → XF → Prop) : Prop :=
  ∀ (M : FullSizeMatrix) (x' : XF) (rec : OnBytes.Flat.RecFull), Yes M x' →
    H.inRange M = true ∧ (H.trace M (instanceAsPlainRecord (x', rec))).isSome = true

/-- It follows from `Serves Z H` (E2E/ReadyAtFiles.lean), which asks the trace at the object's whole
relation and the test on the index at every matrix in range. -/
theorem servesAt_of (hY : ∀ i x, Yes i x → RyesZ Z i x) (S : Serves Z H) : ServesAt Z H Yes :=
  fun _ _ rec h => S.both rec (hY _ _ h)

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
/-- `RowsAt` from the invariants (`ThreadsAt`), `PlainAt` and `ServesAt`, at `TiedOut`. That `ready`
returns depends on no purse (`ready_any`), and `PlanServes` follows (`planServes`): two theorems
under Johnson/Desc/ProofFile/Honest/Law. That no declared stored table is deeper than the data
follows from the plan's test and `DataFits`. -/
theorem rowsAt_of (Zs) (hp : (descZ Zp Np cF).planOk = true)
    (hD : ProofFile.Honest.DataFits (descZ Zp Np cF) (dataZ Z)) (Q : PlainAt Z Zp Np cF B G H)
    (S : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      Zs)) :
    RowsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs) := by
  intro n w x c hx
  obtain ⟨w₀, rc, x₀, k, R₀, h⟩ := Q.ready₁
  have hin : (provG Z Zp Np cF B G H).inRange w.1 = true ∧
      ((provG Z Zp Np cF B G H).trace w.1 x).isSome = true := by
    obtain ⟨x', hx', rfl⟩ := hx.2.1
    exact S _ _ _ hx'
  obtain ⟨R, hR⟩ := ProofFile.Honest.ready_any (rc' := w.2.1) h hin.1 hin.2 (pursesOf c)
  exact ⟨R, hR, ProofFile.Honest.planServes hR hp Q.rooted
    (stored_of_tied (show Tied _ _ _ _ _ _ _ _ w x from hx.2.2)
      (fun d hd t ht => le_of_eq ((((descZ Zp Np cF).planOk_ok).1 hp).depth d hd t ht |>.trans
        hD.depth.symm))
      (fun d hd t ht p => (width_extZ Z w p).trans (Q.width d hd t ht).symm)),
    hthr n w x c R hx hR⟩

/-- The measure of the abort set `Hid`, which may depend on the private input, at the smaller
relation: from the same at the larger. -/
theorem hidSmall_in {ok : FullSizeMatrix → Prop} {Gs} {z : ℝ≥0∞}
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes
      ok Gs n w (instanceAsPlainRecord a)) z :=
  fun n w a h => hz n w a h.2.2

/-! ## The structures of the two sides -/

/-- The family's external strings are the object's encoded index. -/
theorem extIsEnc_famG : ExtIsEnc (famG Z Zp Np cF run₂ run₃ B G H) :=
  fun _ i r e => ext_obj Z (dataAtFiles flashProveData Z).P (i, r, e)

/-- The test on the number reads the front round's number. -/
def NumReads (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (S : SdOf (lettersZ Z c₀ m₀)) : Prop :=
  ∀ k π, S.num k π = decide (((chainsZ Z).plF π).copy = k)

/-- The compiled verifier's own structure of the OOD-seed wire has such a test: by unfolding. -/
theorem num_letters (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) :
    NumReads Z c₀ m₀ (lettersZ Z c₀ m₀).letters.Sd := fun _ _ => rfl

/-- **`HonFit` at Z.** The head of this file says what is proved and what stays a hypothesis. -/
theorem honFit_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (S : SdOf (lettersZ Z c₀ m₀))
    (hS : NumReads Z c₀ m₀ S) (hY : ∀ i x, Yes i x → RyesZ Z i x) (hT) (hL) (FT) (FL) (Zs)
    {ζ pT pL zB z pF : ℝ≥0∞} (g : NineFit hT hL (lettersZ Z c₀ m₀).W FT FL Zs S Yes ζ pT pL)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G H) (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      Zs))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (fallsOf hT hL _ FT FL (guardFall Zs
      (fallG Z Zp Np cF run₂ run₃ B G H)))
      (lettersZ Z c₀ m₀).W S Yes Zs ζ pT pL (zB + z + pF) :=
  honFit_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF)
      (extZ Z) S hT hL
    FT FL Zs g (full_atFiles Z scope live) (carries_atFiles Z) (run_atFiles Z Zp Np cF live L)
    (fun n r2 r3 w a h => sil_atFiles Z Zp Np cF run₂ run₃ B G H n r2 r3 w a h.2.2)
    (yesAt_of_debts (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)
      L.planOk Q.plainSeal (dataFits_atFiles Z Zp Np cF scope live L) Q.halved
      (due_atFiles Z Zp Np cF scope live L Q.nonZero) _ _ (fun _ _ _ h => h.2.2)
      (fun n w x c h => ⟨firstAt_of_one Z Zp Np cF run₂ run₃ B G H scope L h₀ Zs n w x h,
        rowsAt_of Z Zp Np cF run₂ run₃ B G H Zs L.planOk
          (dataFits_atFiles Z Zp Np cF scope live L) Q Sv hthr n w x c h⟩))
    (extIsEnc_famG Z Zp Np cF run₂ run₃ B G H)
      (validOut Z Zp Np cF run₂ run₃ B G H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data) Zs) hb hz
      (validYes Z Zp Np cF run₂ run₃ B G H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data)) hf
    (num_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF)
        (extZ Z) S hS
      (fun _ _ _ _ _ _ _ => rfl))

/-- `ExtEnc`, of the statement of index privacy, at the same value. -/
theorem extEnc_join (hT) (hL) (eT : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (eL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = ((protocolAtFiles Z).encodeIndex i r, (protocolAtFiles Z).encodeIndex i r')) :
    ExtEnc (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) :=
  extEnc_of hT hL _ (extIsEnc_famG Z Zp Np cF run₂ run₃ B G H) eT eL

/-- **`StopsSmall`, of that statement, at the same value and the same relation Yes**, the session's
clause at z. One hypothesis on the session's prover: the measure of `Hid`, at the inputs of `TiedIn`
only. One on the description: hit. -/
theorem stops_join (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (c₀ : VerifiableInference.Digest)
    (m₀ : List (Iop.Dig 256)) (hT) (hL) {ok : FullSizeMatrix → Prop} {Gs} {pT pL pO z : ℝ≥0∞} {Fm'}
    (s : StopsSmall (proversOf hT hL Fm') (lettersZ Z c₀ m₀).W ok Gs Yes pT pL pO)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H
      Yes ok Gs n w (instanceAsPlainRecord a)) z) :
    StopsSmall (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (lettersZ Z c₀ m₀).W ok Gs Yes pT
      pL z :=
  stops_of_small hT hL _ _ s hz (validIn Z Zp Np cF run₂ run₃ B G H hY hit ok Gs)
    (hidZero_link (lettersZ Z c₀ m₀) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))

/-- **`Sims.Good`, of that statement, at the same value and the same relation Yes**, the session's
clause at error 0 (no result by itself). One hypothesis on the session's prover: outside `Hid` its
output is the named simulator's, at the description's own instances, at the inputs of `TiedIn` only.
One on the description: hit. -/
theorem good_join (hY : ∀ i x, Yes i x → RyesZ Z i x)
    (hit : AtPublicFiles.AtZero.ItemsZero (descZ Zp Np cF)) (c₀ : VerifiableInference.Digest)
    (m₀ : List (Iop.Dig 256)) (hT) (hL) {simOne} {sT sL} {ok : FullSizeMatrix → Prop} {Gs}
    {zT zL zO : ℝ≥0∞} {Fm'}
    (g : Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf hT hL Fm') (lettersZ Z c₀ m₀).W ok Gs Yes zT zL zO)
    (h : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs)) :
    Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (lettersZ Z c₀ m₀).W ok Gs Yes zT zL 0 :=
  good_of_exact hT hL _ _ g (h.re instanceAsPlainRecord _ id) (validIn Z Zp Np cF run₂ run₃ B G H hY hit ok Gs)
    (extIsEnc_famG Z Zp Np cF run₂ run₃ B G H)

/-- The clause on the session's prover of `RunVals`, at a value of three provers. -/
def RunValsB (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (ok : FullSizeMatrix → Prop) : Prop :=
  ∀ i r e n x (κ : CoinG B R₂ R₃) ρ, ok i →
    ρ ∉ (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)).B.withheld (i, r, e, n) (x, (protocolAtFiles Z).recOf
      i r e) →
    pvZ Z (dataAtFiles flashProveData Z).P (((proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)).B.strat (i, r,
                   e, n)
                   (x, (protocolAtFiles Z).recOf i r e) κ).run ρ).1.plains = (run₂ κ.1.2, run₃ κ.2.2)

/-- It holds at the same value: proved. Its two hypotheses, that the index is in the range ok and
that ρ is outside the abort set, are not used. -/
theorem runVals_join (hT) (hL) (ok : FullSizeMatrix → Prop) : RunValsB Z Zp Np cF run₂ run₃ B G H hT hL ok :=
  fun i r e n x κ ρ _ _ =>
    runVals_tied Z Zp Np cF silInst run₂ run₃ B (dataAtFiles flashProveData Z).P (G.prover H) hT hL i r e n x κ ρ

/-- **Both sides at one value**: one conjunction, with the same hT, hL and family in all five, and
the same wiring and relation Yes wherever they are read (`ExtEnc` and `RunValsB` read neither). -/
theorem both_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (S : SdOf (lettersZ Z c₀ m₀))
    (hS : NumReads Z c₀ m₀ S) (hY : ∀ i x, Yes i x → RyesZ Z i x) (hT) (hL) (FT) (FL) (Zs)
    {ζ pT pL zB z z' pF hpT hpL hpO zT zL zO : ℝ≥0∞} {Fm₂ Fm₃} {simOne} {sT sL}
    {ok : FullSizeMatrix → Prop} {Gs} (g : NineFit hT hL (lettersZ Z c₀ m₀).W FT FL Zs S Yes ζ pT pL)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G H) (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      Zs))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF)
    (s : StopsSmall (proversOf hT hL Fm₂) (lettersZ Z c₀ m₀).W ok Gs Yes hpT hpL hpO)
    (hz' : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G
      H Yes ok Gs n w (instanceAsPlainRecord a)) z')
    (gd : Sims.Good
      ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      (proversOf hT hL Fm₃) (lettersZ Z c₀ m₀).W ok Gs Yes zT zL zO)
    (hx : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)) simOne
      (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs)) :
    HonFit (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (fallsOf hT hL _ FT FL (guardFall Zs
      (fallG Z Zp Np cF run₂ run₃ B G H)))
        (lettersZ Z c₀ m₀).W S Yes Zs ζ pT pL (zB + z + pF) ∧
      ExtEnc (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) ∧
      StopsSmall (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (lettersZ Z c₀ m₀).W ok Gs Yes
        hpT hpL z' ∧
      Sims.Good
        ⟨sT, sL, fun n a ρ ans =>
        (simOne n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
        (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H)) (lettersZ Z c₀ m₀).W ok Gs Yes zT zL 0 ∧
      RunValsB Z Zp Np cF run₂ run₃ B G H hT hL ok :=
  ⟨honFit_atFiles Z Zp Np cF run₂ run₃ B G H scope live L c₀ m₀ S hS hY hT hL FT FL Zs g h₀ Q Sv
      hthr hb hz hf,
    extEnc_join Z Zp Np cF run₂ run₃ B G H hT hL g.extT g.extL, stops_join Z Zp Np cF run₂ run₃ B G
      H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data) c₀ m₀ hT hL s hz',
    good_join Z Zp Np cF run₂ run₃ B G H hY (AtPublicFiles.AtZero.itemsZero_of_data L.data) c₀ m₀ hT hL gd hx,
      runVals_join Z Zp Np cF run₂ run₃ B G
      H hT hL ok⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Bridge.stored_of_tied
#print axioms AtPublicFiles.AtFiles.famG_eq
#print axioms AtPublicFiles.AtFiles.validYes
#print axioms AtPublicFiles.AtFiles.validOut
#print axioms AtPublicFiles.AtFiles.validIn
#print axioms AtPublicFiles.AtFiles.firstAt_of_one
#print axioms AtPublicFiles.AtFiles.width_extZ
#print axioms AtPublicFiles.AtFiles.servesAt_of
#print axioms AtPublicFiles.AtFiles.rowsAt_of
#print axioms AtPublicFiles.AtFiles.hidSmall_in
#print axioms AtPublicFiles.AtFiles.extIsEnc_famG
#print axioms AtPublicFiles.AtFiles.num_letters
#print axioms AtPublicFiles.AtFiles.honFit_atFiles
#print axioms AtPublicFiles.AtFiles.extEnc_join
#print axioms AtPublicFiles.AtFiles.stops_join
#print axioms AtPublicFiles.AtFiles.good_join
#print axioms AtPublicFiles.AtFiles.runVals_join
#print axioms AtPublicFiles.AtFiles.both_atFiles
#print axioms AtPublicFiles.AtFiles.protocolAtFiles
#print axioms AtPublicFiles.AtFiles.lettersZ
#print axioms AtPublicFiles.AtFiles.dataZ
#print axioms AtPublicFiles.AtFiles.chainsZ
#print axioms AtPublicFiles.AtFiles.descZ
#print axioms AtPublicFiles.AtFiles.WZ
#print axioms AtPublicFiles.AtFiles.CoinG
#print axioms AtPublicFiles.AtFiles.pursesOf
#print axioms AtPublicFiles.AtFiles.provG
#print axioms AtPublicFiles.AtFiles.famG
#print axioms AtPublicFiles.AtFiles.fallG
#print axioms AtPublicFiles.AtFiles.TiedYes
#print axioms AtPublicFiles.AtFiles.TiedOut
#print axioms AtPublicFiles.AtFiles.TiedIn
#print axioms AtPublicFiles.AtFiles.FirstAt
#print axioms AtPublicFiles.AtFiles.RowsAt
#print axioms AtPublicFiles.AtFiles.ThreadsAt
#print axioms AtPublicFiles.AtFiles.PlainAt
#print axioms AtPublicFiles.AtFiles.ServesAt
#print axioms AtPublicFiles.AtFiles.NumReads
#print axioms AtPublicFiles.AtFiles.RunValsB
