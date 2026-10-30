-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeLink.lean: `AccAtTied` (E2E/BridgeAccept.lean), the acceptance statement for the prover of
one request's protocol (the session's prover), is proved from a hypothesis on the honest side's own
run. `AccAtTied` says: at tied inputs and at every coin of the prover's, `AccLaw`
(Johnson/Prover/Law/Defs.lean) holds: the interactive verifier accepts every transcript that is the
prover's own run but for nonces, at a verifier randomness that passes the proof-of-work tests and
lies outside the abort set and outside the fall's set at that coin. It is proved for `famAlong`
(E2E/BridgeAlong.lean), the family of honest provers of `ProofFile.Honest.honestBatchProverOfFile` read along a writing
map wr, and for the fall's set `fallAlong` (E2E/BridgeFalls.lean), at the protocol and the wiring of
the compiled verifier of the proof file, at any parameters T of the full size (`InnerCompilerInputAndAnalysisFieldsAtFullSize`,
Johnson/Flat/Dec/TwoSizesAt.lean). The hypothesis, `YesAt`, says that the description's decision
accepts the three views of the honest run. It follows in turn from what `ProofFile.Honest.yes_at_stratC`
asks, stated here as `DebtsAt` next to `Tied`. It is for files that have to show the field `accB` of
`OnBytes.Prover.HonFit` (Johnson/Prover/All/OfHonest.lean). General in the description F, the
writing map, the book of coins B (`ProverCoinCounts`), the rows G (`Sides`: for each sub-protocol the prover's
part and its simulator), the prover structure H (`ProofFile.Honest.Prover`) and the seam J (`KeyAndJoiningRoundMessages`).

A fall (`Fall`, Johnson/Desc/ProofFile/Honest/Side.lean) is a test at the place of one sub-protocol,
on the verifier's state before that place and on the place's own challenges; it is meant as a test
of the verifier's that an honest run may fail at some of the run's coins. The rows G hold a list of
falls for each of the three chains. The fall's set `fallBC … n w x c` is the set of verifier
randomness at which the run at the coin c meets a fall of these lists; it is set aside on the
acceptance side.

  `accAtTied_of_yes`: `AccAtTied` of the family `famAlong`, at the prover structure `G.prover H` (H
    with the prover's parts of the rows G), and of the fall's set `fallAlong`, at the wiring `T.W`
    and the relation `TiedX n w (wr a)`, from `YesAt` and four more hypotheses (see Hypotheses).
    TiedX is a free parameter
  `yesAt_of_debts`: `YesAt` at any relation TiedX that gives `Tied`
    (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean), from `DebtsAt` at every input of that
    relation and every coin, and from five hypotheses on the description, the rounds' data and the
    prover structure. `Tied` proves three hypotheses of `yes_at_stratC`, by its fields `key` (the
    equation of the two keys), `start` (the shared chain's first state) and `table` (the stored
    table)
  `YesAt … K chal TiedX`: a definition, used as a hypothesis, in the terms of the conclusion of
    `yes_at_stratC`: at every number n, private input w and instance x with `TiedX n w x`, at every
    coin c, at every verifier randomness ρ that passes the proof-of-work tests of the wiring
    `wiresOf C K chal D tF tJ t3` and lies outside the abort set of `honestProversByCopyNumber` at n and outside
    `fallBC … n w x c`: `F.run x` accepts the three views (`view₁`, `view₂`, `view₃`, at the
    external string `ext w`) of the transcript that the family's strategy writes at ρ
  `DebtsAt F B G H w x c`: a definition: what `yes_at_stratC` asks beyond `Tied`, at one input and
    one coin, as one proposition; its clauses are in its docstring
  `no_fall_of_not_mem`: at a verifier randomness outside `fallBC … n w x c`, the views of the run
    that `runC` returns meet no fall of G's three lists (`viewsFall` is `none`): the hypothesis
    hfall of `yes_at_stratC`
  `kOf T`: an abbreviation: the number K of hash blocks in the type of T (`chalP .two K` makes a
    challenge from K hash blocks)

By what. Honest/ is short for Johnson/Desc/ProofFile/Honest/. `ProofFile.Honest.yes_at_stratC`
(Honest/Law/ThreadStratC.lean) concludes: the description's decision accepts the three views of the
transcript that the honest strategy writes, at a verifier randomness outside the abort set at which
the run meets no fall. `yesAt_of_debts` calls it. `LPFFrame.frame_at_slot`
(Johnson/LPFFrame/Proofs.lean; its statement: Johnson/LPFFrame/Statements.lean) has the hypothesis:
at every verifier randomness that passes the proof-of-work tests, outside a set B, the test on the
three rounds without a challenge and the proof file's decision accept at the strategy's run. It
concludes `AccLaw` at the compiled verifier's own protocol and wiring, outside B. Of what `AccLaw`
asks it proves the part on the nonces and the test bits; the part on the reads (the draws are
complete; the stored table's symbols carry their positions) it proves under two hypotheses, `FullAt`
and `Carries`, which stay hypotheses here. `ProofFile.Honest.zip_partsC` (Honest/Law/StratFormC.lean) says
what the three rounds without a challenge hold in the strategies' transcript: the seam's three
values. `accAtTied_of_yes` calls `frame_at_slot` at B := the union of the abort set and the fall's
set, and `zip_partsC` for the test on the three rounds. Definitions: `honestProversByCopyNumber` (E2E/BridgeAlong.lean);
`fallBC` (E2E/BridgeFalls.lean); `Honest.withheld` (Iop/InteractiveOracleProof.lean: the abort set, the union of
`Bad` and `Hid`); `fallAt`, `viewsFall` (Honest/Fall.lean); `Sides` (Honest/Rule.lean); `runC`
(Honest/Walk.lean); `ready`, `Draws.due` (Honest/Frame.lean); `PlanServes`
(Honest/Law/RunsFile.lean); `ThreadsC` (Honest/Law/ThreadStratC.lean); `drawsAt`, `DataFits`
(Honest/Law/StratWords.lean); `halvedAll` (Honest/Law/Run.lean); `sealPlain`
(Honest/Law/Thread.lean); `FileDescription.run`, `planOk`, `okStart` (Johnson/Desc/Block.lean); `FullAt`,
`Carries` (Johnson/LPFFrame/Statements.lean); `silP`, `front₀`, `join₀` (OnBytes/Flat/FilesAt.lean);
`view₁`, `view₂`, `view₃` (OnBytes/Maker/WholeViews.lean); `wiresOf` (OnBytes/Maker/Wire.lean);
`ckP`, `chalP` (Run/PlanPull.lean).

Hypotheses of `accAtTied_of_yes`. hFull: `FullAt`, at the proof file's rounds' data: at every
verifier randomness of each chain, every stored table's part of a round's draws has as many draws as
it states. hCar: `Carries (ext w)` at every w: every symbol of the external string carries its
position. hrun: where the description's decision `F.run` accepts at what is written, `wr a`, the
object's decision on the proof file, runP, accepts at a, at the same three views. hsil: at tied
inputs and all run values r2 and r3, the object's test on the three rounds without a challenge
(`silP`) accepts the seam's three values: `front` and `seam` of `J n r2 r3`, `join` of
`J n r2 default`. hyes: `YesAt` at the proof file's rounds' data `DP.at frS.P.T.a`, its fixed plain
parts `front₀ rP`, `join₀ rP` and `ByteArray.empty`, the programs' way of drawing `ckP .two`, K and
`chalP .two K`. Of `yesAt_of_debts`. hp: the description's tests on the plan accept (`F.planOk`).
hq: `sealPlain F`: the first chain's last declared round states no item but roots, and no root. hD:
`DataFits F D`: the rounds' data D are the description's, as far as the views read them. h4:
`halvedAll`: `G.prover H` has a part of the prover's (`Placed`) at every sub-protocol one of whose
rounds states an item other than a root. hdue: at every verifier randomness the lists of challenges
`drawsAt` are such as the description's rounds can draw (`Draws.due`). hT: TiedX gives `Tied` at
`G.prover H`, `J n`, ext and sh, and at pubJ and Rel, two free parameters that nothing else here
reads. hdebt: `DebtsAt` wherever TiedX holds, at every coin.

Limits.
- Conditional. `DebtsAt` is shown of no prover structure: it contains the invariants for all
  sub-protocols. It is a statement of hypotheses: it is claimed of nothing.
- TiedX is a free parameter in `accAtTied_of_yes`, and is shown of no input here: at a relation that
  nothing meets the theorem is vacuous. That every valid pair of the object is tied, and the four
  hypotheses next to `YesAt`, are proved at three public files Z in E2E/BridgeLinkAtFiles.lean,
  under hypotheses of that file. "Tied" is proved there for a prover structure that has the
  committer's key and, at the item 0 only, its stored table (`Committer.proverAt` at 0,
  Johnson/Desc/ProofFile/Honest/CommitterAt.lean), under `ItemsZero` (E2E/ItemsZero.lean): every
  stored table that a round of the description declares is under the item 0. For the four it asks
  that Z is in scope, that the IOP's own test on the public files accepts, `LaidAt` of the
  description, and that the input is tied.
- `DebtsAt` is asked at every coin of a tied input: every purse and both run values.
- Pointwise in the verifier randomness: no measure.
- The lists of falls are free parameters (fields of the rows G). A fall whose test always returns
  something makes the statement vacuous. At a sub-protocol without a round, a fall whose test is
  "this sub-protocol's own step rejects" makes "the run meets no fall" contain a part of the
  conclusion. So the statement says something at a sub-protocol only next to each fall's test as
  written and its measured share (`FallSmall`, at each fixed coin): without the number it says
  nothing there.
- Nothing at public files: T is any value of `InnerCompilerInputAndAnalysisFieldsAtFullSize`, so the parameters are any
  parameters of the full size.
- On acceptance only: `AccAtTied` is a hypothesis of `accB_of` and `honFit_of`
  (E2E/BridgeAccept.lean). No statement of completeness is made here, and nothing on soundness or
  hiding.
-/
import E2E.BridgeFalls
import E2E.BridgeRunVals
import Johnson.LPFFrame.Proofs
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tied

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD chainsOf wiresOf view₁ view₂ view₃)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides fallAt drawsAt runC viewsFall)

section BC
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (G : Sides F B W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂]
  [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- A hypothesis, stated as a definition: at inputs that meet TiedX, at every coin, at every
verifier randomness that passes the wiring's proof-of-work tests and lies outside the abort set and
the fall's set at that coin, the description's decision accepts the three views of the honest run.
-/
def YesAt (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (TiedX : ℕ → W₀ × Rc × Sd → Xi → Prop) : Prop :=
  ∀ n w x (c : (honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).Coin), TiedX n w x →
    ∀ ρ, RoundsQueryLayout.pass _ _ (wiresOf C K chal D tF tJ t3).sh ρ = true →
      ρ ∉ ((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).at n).withheld w x ∪
        fallBC C D tF tJ t3 F silent B G H J sh ext n w x c →
      F.run x
        (view₁ C D tF tJ t3 (ext w)
          (((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).strat n w x c).run ρ).1)
        (view₂ C D tF tJ t3 (ext w)
          (((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).strat n w x c).run ρ).1)
        (view₃ C D tF tJ t3 (ext w)
          (((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).strat n w x c).run ρ).1) = true

/-- Outside the fall's set, the views of the run that `runC` returns meet no fall of G's three
lists. -/
theorem no_fall_of_not_mem (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃))
    (ρ : Rho (chainsOf C D tF tJ t3).sh)
    (h : ρ ∉ fallBC C D tF tJ t3 F silent B G H J sh ext n w x c) :
    ∀ r, runC F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) =
      .ok r → viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views = none := by
  intro r hr
  have h' : ¬ (fallAt G H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
      (drawsAt C D tF tJ t3 ρ)).isSome = true := h
  unfold ProofFile.Honest.fallAt at h'
  rw [hr] at h'
  exact Option.not_isSome_iff_eq_none.1 h'

open ProofFile.Honest (ready PlanServes ThreadsC Tied DataFits halvedAll sealPlain yes_at_stratC)

/-- What `yes_at_stratC` asks beyond `Tied`, at one input and one coin: the description's test on
the instance only (`okStart`) accepts; `ready` returns some R at the coin's three purses;
`PlanServes` holds of R; there is a `ThreadsC`, which holds the invariants for all sub-protocols,
whose three lists of falls are those of the rows G. A statement of hypotheses: it is claimed of
nothing. -/
def DebtsAt (w : W₀ × Rc × Sd) (x : Xi)
    (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)) : Prop :=
  F.okStart x = true ∧
    ∃ R, ready F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧
      PlanServes (G.prover H) w.1 w.2.1 R ∧
      ∃ Thr : ThreadsC F B (G.prover H) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
        Thr.f₁ = G.falls₁ ∧ Thr.f₂ = G.falls₂ ∧ Thr.f₃ = G.falls₃

/-- **`YesAt` from `DebtsAt`**, at any relation TiedX that gives `Tied`. `Tied` proves the equation
of the two keys, the shared chain's first state and the stored table. `DebtsAt` is asked where TiedX
holds and nowhere else. -/
theorem yesAt_of_debts (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover H) = true) (hdue : ∀ ρ, (drawsAt C D tF tJ t3 ρ).due F = true)
    {pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀ → Rc → Xi → Prop}
    {TiedX : ℕ → W₀ × Rc × Sd → Xi → Prop} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hT : ∀ n w x, TiedX n w x → Tied D F (G.prover H) (J n) ext (pubJ n) sh Rel w x)
    (hdebt : ∀ n w x (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)),
      TiedX n w x → DebtsAt F B G H w x c) :
    YesAt C D tF tJ t3 F silent B G H J sh ext K chal TiedX := by
  intro n w x c hx ρ _ hρ
  have ht := hT n w x hx
  obtain ⟨h0, R, hR, hP, Thr, e1, e2, e3⟩ := hdebt n w x c hx
  have hf := no_fall_of_not_mem C D tF tJ t3 F silent B G H J sh ext n w x c ρ
    (fun a => hρ (Or.inr a))
  exact (yes_at_stratC C D tF tJ t3 F silent B (G.prover H) (J n) sh ext w x c (ext w) ρ hR hp hq
    hD h4 h0 hP ht.key ht.start.symm ht.table (hdue ρ) (fun a => hρ (Or.inl a)) Thr
    (by rw [e1, e2, e3]; exact hf)).1

end BC

end AtPublicFiles.Bridge

/-! ## At the compiled verifier's protocol and wiring, at any parameters of the full size -/

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull Coding silP front₀ join₀)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize InnerCompilerInputAndAnalysisFieldsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides zip_partsC)

variable {X Xi : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → View → View → View → Bool}
  {runP : X × RecFull → View → View → View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List XO} {dec : RecFull × RecFull → View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
  (F : FileDescription Xi) (wr : X × RecFull → Xi)
  (silent : Xi → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (G : Sides F B (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Ky Tr X₀ X')
  (H : Prover (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) Xi Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd)
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed Xi Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → F.S₂)
  (ext : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
    ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
    (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)

/-- The number K of hash blocks in the type of T, by name. -/
abbrev kOf (_ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) : ℕ
  := K

/-- **`AccAtTied` at the compiled verifier's own protocol and wiring, from `YesAt`**, at any
parameters T of the full size. `AccAtTied` is the acceptance statement for the session's prover. -/
theorem accAtTied_of_yes
    {TiedX : ℕ → (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).I ×
      ((DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Pad × (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rnd) ×
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Seed → Xi → Prop}
    (hFull : LPFFrame.FullAt (ckP .two) (DP.at frS.P.T.a)) (hCar : ∀ w, LPFFrame.Carries (ext w))
    (hrun : ∀ a v₁ v₂ v₃, F.run (wr a) v₁ v₂ v₃ = true → runP a v₁ v₂ v₃ = true)
    (hsil : ∀ n r2 r3 w a, TiedX n w (wr a) →
      silP a ((J n r2 r3).front w.1 w.2.1 w.2.2 (wr a)) ((J n r2 default).join w.1 w.2.1 w.2.2)
        ((J n r2 r3).seam w.1 w.2.1 w.2.2 (wr a)) = true)
    (hyes : YesAt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty F silent B G
      H J sh ext K (chalP .two K) TiedX) :
    AccAtTied
      (famAlong A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B
        (G.prover H) J sh ext P)
      (fallAlong A (relationsAndEncodingOfClaims A E) DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B G
        H J sh ext P)
      T.W (fun n w a => TiedX n w (wr a)) := by
  intro n w a c ht
  refine LPFFrame.frame_at_slot T hFull a.1 a.2 (ext w) (hCar w) _ _
    (fun ρ hp hρ => ⟨?_, hrun a _ _ _ (hyes n w (wr a) c ht ρ hp hρ)⟩)
  let κ : (ProofFile.Honest.Purse B.shared × R₂) ×
    ((ProofFile.Honest.Purse B.first × ProofFile.Honest.Purse B.second) × R₃) := c
  obtain ⟨m1, -, m3, -, m5, -⟩ := zip_partsC (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty F B (G.prover H) (J n κ.1.2 default) (J n κ.1.2 κ.2.2) sh w κ.1.1 (wr a) κ.2.1 ρ
  have h := hsil n κ.1.2 κ.2.2 w a ht
  exact (congr (congr (congrArg (silP a) (congrArg Prod.snd m1)) (congrArg Prod.snd m3))
    (congrArg Prod.snd m5)).trans h

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Bridge.no_fall_of_not_mem
#print axioms AtPublicFiles.Bridge.yesAt_of_debts
#print axioms AtPublicFiles.AtFiles.accAtTied_of_yes
#print axioms AtPublicFiles.Bridge.YesAt
#print axioms AtPublicFiles.Bridge.DebtsAt
#print axioms AtPublicFiles.AtFiles.kOf
