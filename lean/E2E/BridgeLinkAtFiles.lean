-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeLinkAtFiles.lean: `AccAtTied` (E2E/BridgeAccept.lean), the acceptance statement for the
prover of one request's protocol (the session's prover), is proved at three public files Z from
`YesAt` only (`accAtTied_atFiles`), and so from the hypotheses of `yesAt_of_debts`
(`accAtTied_of_debts`). `AccAtTied` says: at tied inputs and at every coin of the prover's, `AccLaw`
(Johnson/Prover/Law/Defs.lean) holds: the interactive verifier accepts every transcript that is the
prover's own run but for nonces, at a verifier randomness that passes the proof-of-work tests and
lies outside the abort set and outside the fall's set at that coin. The proof is `accAtTied_of_yes`
(E2E/BridgeLink.lean) at the parameters from which the verifier is compiled,
`(dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀`, and at the committer's structure `cmAlong` of E2E/TiedAtFiles.lean,
with its external string and with what the three rounds without a challenge send there. That theorem
has four hypotheses next to `YesAt`; all four are proved here. The two main theorems are stated in
scope (`InScope Z = true`), where the IOP's own test on the public files accepts
(`protocolDataWellFormed (asDescriptionFiles Z) = true`), at a description (the IOP of the proof file as written in Lean:
`F0T OnBytes.secondHashFunction Zp Np cF`, Johnson/P5J/AtTerm.lean) of which `LaidAt`
(Johnson/P5J/LaidOpens.lean) holds at Z's files. General in the book of coins B (`ProverCoinCounts`), the rows G
(`Sides`: for each sub-protocol the prover's part and its simulator), the prover structure H
(`ProofFile.Honest.Prover`), the description's test `silent` on the three rounds without a challenge, the
types R₂, R₃ of the two coins r2, r3 with their maps run₂, run₃ into bytes, the digest c₀ and the
list of digests m₀.

`LaidAt` ties the description to the library's object `(filesAt Z).withProvers (dataAtFiles flashProveData Z).P`
(E2E/ObjectAtFiles.lean). Its field `value` says that the library makes the description
`F0T OnBytes.secondHashFunction Zp Np cF` of Z's files. Then, where the IOP's own test on the public files
accepts, the object's decision on the proof file, `(dataAtFiles flashProveData Z).runP`, is that description's
`run`, pulled back along the library's writing map `LPFD.Full.instanceAsPlainRecord`
(Johnson/Desc/Laid/ProofFull.lean).

  `accAtTied_atFiles`: `AccAtTied` of the family `famL` and the fall's set `fallL`
    (E2E/BridgeJoin.lean: short for `famAlong` and `fallAlong`), at the wiring
    `((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W` and the relation `TiedX n w (instanceAsPlainRecord a)`, from `YesAt` only.
    The fall's set at a coin is the set of verifier randomness at which the run at that coin meets a
    fall of the rows' lists; it is set aside on the acceptance side (what a fall is:
    E2E/BridgeLink.lean). TiedX is any relation that gives `TiedG`: so also one that shuts out the
    OOD (out-of-domain) seeds that are set aside
  `accAtTied_of_debts`: the same conclusion, with the hypotheses of `yesAt_of_debts`
    (E2E/BridgeLink.lean) in the place of `YesAt`: see Hypotheses
  `validTiedG_atFiles`: `ValidTied` (E2E/BridgePrivacy.lean) of `TiedG`, at the relation `RyesZ Z`,
    all indices and all OOD seeds: every pair that is valid for the object meets `TiedG`. That is:
    for an index i and a request x with `RyesZ Z i x`, at every number n of a stored copy, all coins
    r of the committer's and every OOD seed e, `TiedG` holds of (i, r, e) and of what `instanceAsPlainRecord`
    writes for x with the object's OOD sample `recOf i r e`. Its one hypothesis is hit: it asks
    neither scope nor `protocolDataWellFormed` nor `LaidAt`
  `TiedG … n w x`: a definition: `Tied` (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) at the
    prover structure `G.prover ((cmAlong …).proverAt 0 H)`: H with the committer's columns as its
    stored table at the item 0, no column at another item, the committer's key
    (`Committer.proverAt`, Johnson/Desc/ProofFile/Honest/CommitterAt.lean) and the prover's parts of
    the rows G. The other parameters of `Tied` are those of `tied_atFiles_along`
    (E2E/TiedAtFiles.lean): `seamZ`, `extZ`, `pubAt`, `shAt`, and `relAt` at `RyesZ Z`
  `full_atFiles`: `LPFFrame.FullAt` at the proof file's rounds' data at Z: at every verifier
    randomness of each chain, every stored table's part of a round's draws has as many draws as it
    states. In scope, where the IOP's own test accepts
  `carries_atFiles`: `LPFFrame.Carries (extZ Z w)` at every w: every symbol of the committer's
    external string carries its position. No hypothesis
  `run_atFiles`: where the description's decision `run` accepts at what is written, `instanceAsPlainRecord a`, the
    object's decision on the proof file accepts at a, at the same three views. Where the IOP's own
    test accepts, under `LaidAt`
  `sil_atFiles`: at a private input w and an instance a with `TiedG … n w (instanceAsPlainRecord a)`, at all r2 and
    r3, the object's test on the three rounds without a challenge (`silP`,
    OnBytes/Flat/FilesAt.lean) accepts the three values of `seamZ`: `front` and `seam` at (r2, r3),
    `join` at (r2, `default`)
  `seamZ Z run₂ run₃ n r2 r3`: an abbreviation: the `KeyAndJoiningRoundMessages` structure
    (Johnson/Desc/ProofFile/Honest/Strat.lean) that `Committer.seam` makes of `cmAlong` at Z: its
    key is the committer's field `ood` (the key of the private input's OOD sample); the three rounds
    without a challenge send `frontAt`, `joinAt` and `seamAt`. n: the copy's number
  `extZ Z`: an abbreviation: the external string of `cmAlong` at Z (`Committer.ext`), at the stored
    table's depth in the proof file's rounds' data

By what. `accAtTied_atFiles` is one call of `accAtTied_of_yes` with the four lemmas;
`accAtTied_of_debts` calls it with `yesAt_of_debts`. `full_atFiles`: in scope, where the IOP's own
test accepts, the proof file's rounds' data at Z are the library's written data
`Johnson.G.writtenPFull` (`AtPublicFiles.Reads.proof_data`, E2E/ReadsAtFiles.lean), and `FullAt` holds there
(`LPFFrame.fullAt_written`, Johnson/LPFFrame/Proofs.lean). `carries_atFiles`: by unfolding
`Committer.ext` (Johnson/Desc/ProofFile/Honest/Committer.lean). `run_atFiles`: by the field `run` of
`LaidAt`, `LaidAt.laidPOf` (Johnson/P5T/FenceAtMg.lean) and `run_eq_of_laid` (E2E/ProtocolOverDescription.lean),
the `run` of the pulled-back description `descAt Zp Np cF` is the object's decision;
`FileDescription.pull_run` (Johnson/Desc/Block.lean) unfolds the pulling back. `sil_atFiles`: `silP_along`
(E2E/TiedAtFiles.lean), the clause `seam` of `Tied`, and `pub_passes_along` (E2E/TiedAlong.lean).
`validTiedG_atFiles`: `tied_atFiles_along` at the prover structure `G.prover H`. It concludes `Tied`
at `(cmAlong …).proverAt 0 (G.prover H)`, which is the prover structure of `TiedG` by unfolding:
`Sides.prover` (Johnson/Desc/ProofFile/Honest/Rule.lean) replaces the three lists of the prover's
parts, `proverAt` the stored table and the key, so the order of the two does not matter.

Hypotheses of `accAtTied_atFiles`. scope: `InScope Z = true`. live: `protocolDataWellFormed (asDescriptionFiles Z) = true`. L:
`LaidAt` at Z's three files, some rounds' data D and decision r, and (Zp, Np, cF). hX: TiedX gives
`TiedG`. hyes: `YesAt` (E2E/BridgeLink.lean) at the proof file's rounds' data at Z, the description,
`silent`, B, G, the prover structure `(cmAlong …).proverAt 0 H`, `seamZ`, `shAt`, `extZ` and TiedX.
`accAtTied_of_debts` keeps scope, live, L and hX. Its others: hp: the description's tests on the
plan accept (`planOk`; L has the same as its field `planOk`). hq: `sealPlain` of the description.
hD: `DataFits` of the description and the proof file's rounds' data at Z. h4: `halvedAll` of the
description and the prover structure of `TiedG`. hdue: at every verifier randomness the lists of
challenges `drawsAt` are such as the description's rounds can draw (`Draws.due`). hdebt: `DebtsAt`
at every input of TiedX and every coin. What hq, hD, h4 and `DebtsAt` say is in E2E/BridgeLink.lean.
Of `validTiedG_atFiles`. hit: `AtPublicFiles.AtZero.ItemsZero` (E2E/ItemsZero.lean) of the description: every
stored table that a round of the description declares is under the item 0, the one item at which the
prover structure of `TiedG` has the committer's columns.

Limits.
- Conditional. `YesAt` and `DebtsAt` are hypotheses. `DebtsAt` contains the invariants for all
  sub-protocols of the description; it is shown of no rows.
- TiedX is a free parameter of the two main theorems: at a relation that nothing meets they are
  vacuous. That some pair is valid for the object at Z is not shown here.
- hit is a hypothesis: it is proved of no description here. `itemsZero_of_data` (E2E/ItemsZero.lean)
  proves it wherever the description's `data` returns, so from the field `data` of a `LaidAt`.
  `validTiedG_atFiles` holds at every (Zp, Np, cF) whose description meets hit, not only at one of
  which `LaidAt` holds at Z.
- No theorem of this folder says that the IOP's own tests on the public files pass at any files.
- The lists of falls are free parameters (fields of the rows G). A fall whose test always returns
  something makes the statement vacuous. At a sub-protocol without a round, a fall whose test is
  "this sub-protocol's own step rejects" makes "the run meets no fall" contain a part of the
  conclusion. So the statement says something at a sub-protocol only next to each fall's test as
  written and its measured share (`FallSmall`, at each fixed coin): without the number it says
  nothing there.
- Pointwise in the verifier randomness: no measure. The structure `HonFit` (`OnBytes.Prover.HonFit`,
  Johnson/Prover/All/OfHonest.lean) at Z is in E2E/BridgeJoinAtFiles.lean: `honFit_atFiles`, which
  calls the four lemmas of this file.
- On acceptance only: `AccAtTied` is a hypothesis of `accB_of` and `honFit_of`
  (E2E/BridgeAccept.lean). No statement of completeness is made here, and nothing on soundness or
  hiding.
-/
import E2E.BridgeJoin
import E2E.TiedAlong
import E2E.ReadsAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Tied relAt DataFits halvedAll sealPlain drawsAt)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  (silent : ProofFile.Inst → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (F0T OnBytes.secondHashFunction Zp Np cF) B FullSizeMatrix ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness TableKey Tr
    X₀ Xh)
  (H : Prover FullSizeMatrix ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- The `KeyAndJoiningRoundMessages` structure of `cmAlong` at Z, at the copy's number n and the two coins r2, r3: the
three rounds without a challenge send `frontAt`, `joinAt` and `seamAt` (E2E/TiedAtFiles.lean). -/
abbrev seamZ (n : ℕ) (r2 : R₂) (r3 : R₃) :=
  (cmAlong (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
    (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3)

/-- The committer's external string at Z: that of `cmAlong`, at the stored table's depth in the
proof file's rounds' data. -/
abbrev extZ := (cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a

/-- `Tied` at Z, at the prover structure H with the prover's parts of the rows G, the committer's
key and, at the item 0 only, the committer's columns as its stored table (`proverAt 0`). -/
def TiedG (n : ℕ)
    (w : FullSizeMatrix × ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness × ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).OutOfDomainSeed)
    (x : ProofFile.Inst) : Prop :=
  Tied ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF)
    (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)) (seamZ Z run₂ run₃ n) (extZ Z)
    (pubAt run₂ run₃ ansInst n) (shAt Zp Np cF)
    (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) LPFD.Full.instanceAsPlainRecord) w x

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
/-- **Every pair that is valid for the object at Z meets `TiedG`**, at every copy's number and every
OOD seed. hit: every stored table that a round of the description declares is under the item 0, the
one item at which the prover structure has the committer's columns. -/
theorem validTiedG_atFiles (hit : AtPublicFiles.AtZero.ItemsZero (F0T OnBytes.secondHashFunction Zp Np cF)) :
    ValidTied (L := (filesAt Z).withProvers (dataAtFiles flashProveData Z).P)
      (fun n w a => TiedG Z Zp Np cF run₂ run₃ B G H n w (LPFD.Full.instanceAsPlainRecord a))
      (fun _ => True) (fun _ => True) (RyesZ Z) :=
  fun n i r e x _ _ hx =>
    tied_atFiles_along Z (dataAtFiles flashProveData Z).P Zp Np cF run₂ run₃ n (G.prover H) (i, r, e)
      (x, ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).recOf i r e) hit ⟨rfl, hx⟩

theorem full_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LPFFrame.FullAt (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) :=
  (AtPublicFiles.Reads.proof_data Z scope live).symm ▸ LPFFrame.fullAt_written

theorem carries_atFiles (w) : LPFFrame.Carries (extZ Z w) := fun _ => rfl

theorem run_atFiles (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : XF × RecFull) (v₁ v₂ v₃)
    (h : (F0T OnBytes.secondHashFunction Zp Np cF).run (LPFD.Full.instanceAsPlainRecord a) v₁ v₂ v₃ = true) :
    (dataAtFiles flashProveData Z).runP a v₁ v₂ v₃ = true := by
  have e : (descAt Zp Np cF).run = (dataAtFiles flashProveData Z).runP :=
    L.run.symm.trans (run_eq_of_laid Z live (D, r) L.laidPOf).symm
  have e2 : (descAt Zp Np cF).run a v₁ v₂ v₃ =
      (F0T OnBytes.secondHashFunction Zp Np cF).run (LPFD.Full.instanceAsPlainRecord a) v₁ v₂ v₃ := by
    unfold descAt
    exact VerifiableInference.Desc.FileDescription.pull_run _ _ _ _ _ _
  exact (congrFun (congrFun (congrFun (congrFun e a) v₁) v₂) v₃).symm.trans (e2.trans h)

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
theorem sil_atFiles (n : ℕ) (r2 : R₂) (r3 : R₃) (w) (a : XF × RecFull)
    (ht : TiedG Z Zp Np cF run₂ run₃ B G H n w (LPFD.Full.instanceAsPlainRecord a)) :
    silP a ((seamZ Z run₂ run₃ n r2 r3).front w.1 w.2.1 w.2.2 (LPFD.Full.instanceAsPlainRecord a))
      ((seamZ Z run₂ run₃ n r2 default).join w.1 w.2.1 w.2.2)
      ((seamZ Z run₂ run₃ n r2 r3).seam w.1 w.2.1 w.2.2 (LPFD.Full.instanceAsPlainRecord a)) = true := by
  rw [silP_along]
  have e := ht.seam r2 r3
  have p := pub_passes_along run₂ run₃ n r2 r3 (LPFD.Full.instanceAsPlainRecord a)
  rw [← e] at p
  exact p

variable {TiedX : ℕ → FullSizeMatrix × ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).EncodingRandomness ×
    ((filesAt Z).withProvers (dataAtFiles flashProveData Z).P).OutOfDomainSeed → ProofFile.Inst → Prop}

/-- **`AccAtTied` at Z from `YesAt` only**, at any relation TiedX that gives `TiedG`. `AccAtTied` is
the acceptance statement for the session's prover. -/
theorem accAtTied_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (hX : ∀ n w x, TiedX n w x → TiedG Z Zp Np cF run₂ run₃ B G H n w x)
    (hyes : YesAt (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (F0T OnBytes.secondHashFunction Zp Np cF) silent B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)
      (kOf ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) (_root_.Run.chalP .two _) TiedX) :
    AccAtTied
      (famL (P := (dataAtFiles flashProveData Z).P) (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord silent B G
        ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (fallL (P := (dataAtFiles flashProveData Z).P) (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord silent B G
        ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W (fun n w a => TiedX n w (LPFD.Full.instanceAsPlainRecord a)) :=
  accAtTied_of_yes ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀) (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord
    silent B G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF)
    (extZ Z) (full_atFiles Z scope live) (carries_atFiles Z) (run_atFiles Z Zp Np cF live L)
    (fun n r2 r3 w a h => sil_atFiles Z Zp Np cF run₂ run₃ B G H n r2 r3 w a (hX n w _ h)) hyes

/-- **`AccAtTied` at Z from the hypotheses of `yesAt_of_debts`**, which are what the theorem on the
honest run (`ProofFile.Honest.yes_at_stratC`) asks. `DebtsAt` is asked where TiedX holds and nowhere else.
-/
theorem accAtTied_of_debts (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (hX : ∀ n w x, TiedX n w x → TiedG Z Zp Np cF run₂ run₃ B G H n w x)
    (hp : (F0T OnBytes.secondHashFunction Zp Np cF).planOk = true)
    (hq : sealPlain (F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hD : DataFits (F0T OnBytes.secondHashFunction Zp Np cF) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a))
    (h4 : halvedAll (F0T OnBytes.secondHashFunction Zp Np cF)
      (G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)) = true)
    (hdue : ∀ ρ, (drawsAt (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ).due
        (F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hdebt : ∀ n w x (c : (ProofFile.Honest.Purse B.shared × R₂) ×
        ((ProofFile.Honest.Purse B.first × ProofFile.Honest.Purse B.second) × R₃)),
      TiedX n w x →
        DebtsAt (F0T OnBytes.secondHashFunction Zp Np cF) B G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) w x
          c) :
    AccAtTied
      (famL (P := (dataAtFiles flashProveData Z).P) (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord silent B G
        ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (fallL (P := (dataAtFiles flashProveData Z).P) (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord silent B G
        ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W (fun n w a => TiedX n w (LPFD.Full.instanceAsPlainRecord a)) :=
  accAtTied_atFiles Z Zp Np cF silent run₂ run₃ B G H scope live L c₀ m₀ hX
    (yesAt_of_debts (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty
      (F0T OnBytes.secondHashFunction Zp Np cF) silent B G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
      (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) hp hq hD h4 hdue _ _ hX hdebt)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accAtTied_of_debts
#print axioms AtPublicFiles.AtFiles.validTiedG_atFiles
#print axioms AtPublicFiles.AtFiles.full_atFiles
#print axioms AtPublicFiles.AtFiles.carries_atFiles
#print axioms AtPublicFiles.AtFiles.run_atFiles
#print axioms AtPublicFiles.AtFiles.sil_atFiles
#print axioms AtPublicFiles.AtFiles.accAtTied_atFiles
#print axioms AtPublicFiles.AtFiles.seamZ
#print axioms AtPublicFiles.AtFiles.extZ
#print axioms AtPublicFiles.AtFiles.TiedG
