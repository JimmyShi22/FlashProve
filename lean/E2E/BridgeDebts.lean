-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeDebts.lean: the hypotheses of `premW_of_owed` (E2E/BridgeOwedLink.lean) as the fields of
one structure, `PremWDebts`, each field with a docstring on what it is about; and that theorem once
more, with the structure as its only hypothesis. The conclusion is `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean): all hypotheses of the statement of index privacy, at three public
files Z, at the parameters of `lettersZ Z c₀ m₀`. Files that import this one can pass the hypotheses
on as one value. As general as `premW_of_owed`: each of its parameters is a parameter here. The key
file's prover `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean) is a prover structure built by `honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here fixes (below: the
shell `offlineProverWithEncodedTable`), and so is each prover of the session's family `famG` (E2E/BridgeJoinAtFiles.lean).
The form that shows every hypothesis written out is `premW_of_owed`.

  `premW_of_debts`: `PremWDebts` gives `PremW` at the same parameters, with the numbers
    `indexPrivacyNumbers s1 zT 0 0 hT' 0 hO'` (E2E/PremisesAtFiles.lean): one call of `premW_of_owed`, field by
    field
  `PremWDebts`: a structure: the hypotheses by name. On the public files: `scope`, `live`, `laid`.
    On the relation: `below`. On numbers: `sessions`, `links`. On the key file's prover: `keyGood`,
    `keyStops`. On the session's prover: `rows`, `owns`, `sessionStops`. On lengths and run values:
    `lens`
  `LensAt`: a structure: the seven statements on lengths and run values, at general parameters
  `lensAt_plain`: the seven can hold together: at every number ℓ of free bits up to the length of a
    leaf's salt, with every run value counted as of the right form and with constant starts
    (`plainStart`, E2E/BridgeNoStop.lean)

`PremWDebts` occurs only as a hypothesis. It is none of the library's goals, and no theorem here has
it as its conclusion.

By what. `premW_of_debts` is `premW_of_owed` (E2E/BridgeOwedLink.lean) at the fields of its
hypothesis; the witnesses D and r of `laid` are that theorem's implicit arguments. That every stored
table which a round of the description declares is under the item 0 (`ItemsZero`,
E2E/ItemsZero.lean) is no field: `premW_of_owed` has it from the field `data` of `LaidAt`.
`lensAt_plain`: `plainStart_len` (E2E/BridgeNoStop.lean).

Limits.
- The fields are hypotheses; none is proved here.
- No value is shown to meet `PremWDebts`. `lensAt_plain` shows that the field `lens` can be met by
  itself, at a choice that is not the format's; that the fields can hold together, at any
  parameters, is shown nowhere, so `premW_of_debts` may be vacuous.
- The fields are not of equal weight and are not to be counted: `sessions` is one inequality on a
  free parameter; `rows` is the whole list of the fields of `ProofFile.Honest.Owed`
  (Johnson/Desc/ProofFile/Honest/Owed.lean).
- `laid` can be proved wherever `live` holds: there some (Zp, Np, cF) meets `LaidAt`
  (`laid_of_live`, E2E/TiedAtFiles.lean).
- That `scope` and `live` hold at the written files `storedPublicFiles` is a theorem of the side library
  (`AtFullSide.Tie.premises_zFull`, AtFullSide/Bind/LiveAtNamed.lean), which this folder cannot
  call.
- The conclusion is met at other provers: `premW_laid` (E2E/LinkLaidPrivacy.lean), for Z in scope,
  at the parameters of `homeR b Z`, under hypotheses of its own, proves `PremW` at the link's
  written prover and, for the other two, placeholders that send fixed messages. That is no value
  that meets `PremWDebts`: the conclusion can be met; the hypotheses may hold of nothing.
- The range ok is a free parameter, and the key file's simulator sT is a free parameter next to it.
  `keyGood` and `keyStops` are asked at the indices of ok only: at a range with one index sT may
  hold that index, and `PremW` then says nothing on hiding it. What E2E/BridgeExact.lean excludes
  (as far as `RyesZ Z` holds at more than one index, which is not shown there) it excludes for the
  session's simulator only. Whoever uses this theorem says which range it is, and that it holds two
  indices or more (the head of Johnson/WholeKey/Statement.lean).
- A way to meet the hypotheses that makes the statement vacuous and shows in no number: the public
  abort set `Bad`. `PremW` has no number for the honest provers' public abort sets. Not stated in
  Lean, and followed through the definitions in part only: provers whose public abort set holds
  every verifier randomness, and which so never answer, may meet all fields at zT = hT' = hO' = 0:
  nothing among the fields is seen to exclude that (the Limits of E2E/BridgePrivacy.lean say it of
  `OneExact` and `HidSmall`). What gives the public abort set a number is on the acceptance side
  (`BadSmall`, E2E/BridgeAccept.lean): E2E/BridgeBothOfDebts.lean has the acceptance side (`HonFit`)
  and the privacy side (`PremW`) at one value of the three provers.
- A second such way that shows in no number: provers that never abort and are never accepted. The
  honest prover's strategy cannot refuse to speak: where its run cannot be made ready, and after a
  rejection by the verifier's own step, it sends fixed substitutes, and none of that lies in an
  abort set (the Limits of E2E/BridgeNoStop.lean). Stated in Lean: where no `Part` names a stop,
  `keyStops` holds at hT' = 0 and `sessionStops` at hO' = 0 (`stopsT_keyZ`, `hidSmall_famG`,
  E2E/BridgeNoStop.lean, under `NoStopAll`, which is vacuous at a prover structure
  (`ProofFile.Honest.Prover`) that has no part for any sub-protocol (`Placed`)). Not stated in Lean: at
  such an HT the shell `offlineProverWithEncodedTable` shows the OOD answers, two run values and substitutes, so `keyGood`
  may then hold at error 0. Rows that lack the prover's part for a sub-protocol, or whose parts send
  well-formed messages that the first step rejects, may do the same for the session. `PremW` has no
  number for the share of rejected runs. What excludes that or gives it a number is on the
  acceptance side: the field `halved` of `PlainAt` (E2E/BridgeJoinAtFiles.lean), a test that each
  sub-protocol one of whose rounds states an item other than a root has its part of the prover's;
  `KeyFive` (E2E/BridgeNineCut.lean), `ThreadsAt` (E2E/BridgeJoinAtFiles.lean), `FallSmall`
  (E2E/BridgeAccept.lean).
- Three fields are vacuous at large numbers: `keyGood` at zT ≥ 1, `keyStops` at hT' ≥ 1 and
  `sessionStops` at hO' ≥ 1 hold whatever the provers are, and the three numbers are in the
  conclusion (`indexPrivacyNumbers`).
- `lensAt_plain`'s choice is not the format's: the format's starts are made of the run values and
  the first salt.
- At ℓ := 0 the seven statements hold and the statement of index privacy is vacuous. The length of a
  leaf's salt at the parameters of `lettersZ` is 256 + 8 · saltG, so at least 256, at every Z
  (`FlashProve.p_tOf`, `sMT_tOf`, Johnson/Prover/At/WiresAt.lean); under `scope` and `live` it is
  576 (`sMT_built`, E2E/ZetaSalt.lean). Neither is called here.
- `lens` asks its three statements on the starts at every round number. `CoinsFit`
  (Johnson/WholeKey/Premises.lean) asks them within the window only: so more is asked here than
  `PremW` needs. Constant starts meet it; whether the format's starts do is not examined.
- Of the parameter R₀ only these fields are read: dcT, dcL, b₀, capT, capL, capB, M, nm, rtail,
  fill. `restKey` (E2E/BridgePremWKey.lean) and `canon` (E2E/BridgeCoins.lean) overwrite all others,
  its enumerations of coins and salts among them: what a caller puts there is dropped without
  notice.
- The parameters of the shell `offlineProverWithEncodedTable` (Fx, BT, HT, val₂, val₃, shT) are free: no field says that they
  are made of the files Z: `laid` speaks of the proof file's description only. The tie of a key
  file's description to Z is stated in Lean (`KeyNamed`, E2E/KeyProtocolOverDescription.lean) and is not asked of
  Fx.
- All OOD seeds, seed by seed: `keyGood`, `keyStops`, `rows` and `sessionStops` are asked at every
  seed, with no mean over seeds and no seed set aside: one seed at which the abort set `Hid`, which
  may depend on the private input, has a large measure forces hT' or hO' up, and here nothing can
  take it out (the Limits of E2E/BridgeOneBundle.lean name a way out that is stated in Lean
  elsewhere).
- Two fields of `Owed` are asked though `laid` gives them (`plan` and `places`, the description's
  tests on its plan and on its places): the list is longer than it need be.
- All limits of E2E/BridgeOwedLink.lean hold here.
- What the conclusion says of the link's prover `linkProverAtFiles b Z` is proved in E2E/BridgePremWLink.lean,
  whose head says what it is and what it is not. Beyond that, nothing on completeness, soundness or
  hiding follows from this file alone.
-/
import E2E.BridgeOwedLink
import E2E.BridgeNoStop

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open _root_.Compile (Params)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse Owed relAt)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.WholeKey (PremW StopsSmall Sims CoinNums NumsW)
open OnBytes.LinkSim.AtHome (explicitLinkProver homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

/-! ## 1 Lengths and run values -/

/-- **The seven statements on lengths and run values.** p: the parameters. c: the numbers of the
coins (`CoinNums`, Johnson/WholeKey/Premises.lean). okV: "a run value of the right form". vT, vB:
the key file's and the session's run values. v₀: a constant that `atRecsAll`
(E2E/BridgePremWLink.lean) sets as the link's run value, as read off the coins and as read off the
plain parts alike. The three starts: the public start of a leaf's salt in each kind of run. -/
structure LensAt (p : Params) (c : CoinNums (List Bool)) (okV : ByteArray × ByteArray → Prop)
    {QT QB : Type} (vT : QT → ByteArray × ByteArray) (v₀ : ByteArray × ByteArray)
    (vB : QB → ByteArray × ByteArray)
    (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits) : Prop where
  /-- a table's leaf salt: its public start and the free bits together have the format's length -/
  pre : c.pre₀.length + c.ℓ = p.sMT
  /-- every run value of the key file's prover has the right form -/
  okT : ∀ q, okV (vT q)
  /-- so has the constant that is set as the link's -/
  okL : okV v₀
  /-- so has every run value of the session's prover -/
  okB : ∀ q, okV (vB q)
  /-- at a run value of the right form, every round number and a first salt of the right length, a
  start and the free bits together have the format's length: in the key file's run -/
  lenT : ∀ v i b s, okV v → s.length = p.sFS → (startT v i b s).length + c.ℓ = p.sMT
  /-- in the link's run -/
  lenL : ∀ v i b s, okV v → s.length = p.sFS → (startL v i b s).length + c.ℓ = p.sMT
  /-- in a session's run -/
  lenB : ∀ v i b s, okV v → s.length = p.sFS → (startB v i b s).length + c.ℓ = p.sMT

/-- **The seven can hold together**, at every number of free bits up to the length of a leaf's salt:
every run value counts as of the right form, the starts are constant, and `c.pre₀` is replaced by
the same constant. -/
theorem lensAt_plain (p : Params) (c : CoinNums (List Bool)) (hℓ : c.ℓ ≤ p.sMT) {QT QB : Type}
    (vT : QT → ByteArray × ByteArray) (v₀ : ByteArray × ByteArray)
    (vB : QB → ByteArray × ByteArray) :
    LensAt p { c with pre₀ := List.replicate (p.sMT - c.ℓ) false } (fun _ => True) vT v₀ vB
      (plainStart p c) (plainStart p c) (plainStart p c) where
  pre := by
    show (List.replicate (p.sMT - c.ℓ) false).length + c.ℓ = p.sMT
    rw [List.length_replicate]
    omega
  okT := fun _ => trivial
  okL := trivial
  okB := fun _ => trivial
  lenT := fun v i b s _ _ => plainStart_len p c hℓ v i b s
  lenL := fun v i b s _ _ => plainStart_len p c hℓ v i b s
  lenB := fun v i b s _ _ => plainStart_len p c hℓ v i b s

/-! ## 2 The hypotheses by name -/

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
  (c : CoinNums (List Bool))
  (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (okV : ByteArray × ByteArray → Prop) (v₀ : ByteArray × ByteArray)
  (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)

/-- **What is left to show for all hypotheses of the statement of index privacy, by name.** Yes: the
relation of which something is to be said. ok: the range of indices. sT: the key file's simulator.
s1: the number of sessions of a copy. zT, hT', hO': the three numbers that stay free parameters. -/
structure PremWDebts (Yes : FullSizeMatrix → XF → Prop) (ok : FullSizeMatrix → Prop) (sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z))
    (s1 : ℕ) (zT hT' hO' : ℝ≥0∞) : Prop where
  /-- On the public files: they are in scope: a Boolean test -/
  scope : InScope Z = true
  /-- On the public files: the IOP's own test on the public head accepts: a Boolean test -/
  live : protocolDataWellFormed (asDescriptionFiles Z) = true
  /-- On the public files: the description `descZ Zp Np cF`, the public part Zp and the places Np
  are what the library's own functions return for the files; the description passes its tests on the
  plan; its data and the tests that the library's lemmas ask (`lawsAsk`) are as `LaidAt`
  (Johnson/P5J/LaidOpens.lean) lists them -/
  laid : ∃ (D : WholeD) (r : LPFD.Full.RunPF),
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF
  /-- On the relation: Yes implies the library's object's relation `RyesZ Z` -/
  below : ∀ i x, Yes i x → RyesZ Z i x
  /-- On numbers: a copy has at most 688127 sessions -/
  sessions : s1 ≤ 688127
  /-- On numbers: the first table's M + 1 links are at most 710324 -/
  links : R₀.M + 1 ≤ 710324
  /-- On the key file's prover: its clause of `Sims.Good`, in that structure's own words: at every
  index of ok, every committer's randomness and every OOD seed, at verifier randomness whose test
  bits are 0: outside the abort set `Hid`, which may depend on the private input, its output is the
  simulator's, but for a set of measure at most zT -/
  keyGood : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∉
            (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e) ∧
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).output (i, r, e) ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ) ≠
          sT ((protocolAtFiles Z).recOf i r e)
            (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
              (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ)
            ((protocolAtFiles Z).offline.extAns ((protocolAtFiles Z).recOf i r e)
              (TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
                (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ) ((protocolAtFiles Z).encodeIndex i r))} ≤
                  zT
  /-- On the key file's prover: its clause of `StopsSmall`, in that structure's own words: at every
  index of ok, every committer's randomness and every OOD seed the abort set `Hid`, which may depend
  on the private input, has measure at most hT' -/
  keyStops : ∀ i r e, ok i → True →
      pr (unif (Rho (protocolAtFiles Z).offline.shape))
        {ρ | TypedOracleCompiler.Iop.RoundsQueryLayout.zero (protocolAtFiles Z).offline.shape (filesAt Z).annT
            (TypedOracleCompiler.Compile.Batch.Cms.wTC (lettersZ Z c₀ m₀).W).sh ρ ∈
          (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT).Hid (i, r, e) ((protocolAtFiles Z).recOf i r e)} ≤ hT'
  /-- On the session's prover: the hypothesis `Owed` on the rows G (`Sides`: for each sub-protocol
  the prover's part and its simulator), at the muted rows (each row's fields A and B set to "never":
  there `Good.plays` and `Good.acc` are vacuous), at the whole relation of the library's object, so
  at every OOD seed. Its prover structure is H with the committer's key and, at the item 0 only, the
  committer's stored table (`Committer.proverAt`, Johnson/Desc/ProofFile/Honest/CommitterAt.lean) -/
  rows : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
    (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) instanceAsPlainRecord)
  /-- On the session's prover: every entry of the book of coins B (`ProverCoinCounts`) has a part of a row for
  its owner: a Boolean test -/
  owns : G.owns = true
  /-- On the session's prover: the abort set `Hid`, which may depend on the private input, has
  measure at most hO' at tied inputs (`TiedIn`). The one proved road to it at a bound below 1 asks
  that H's trace has small cells at every K8 place (`sessionStops_at_files`' hP). That this premise
  cannot simply be dropped is not proved (Johnson/FrontRoad/TracePremisesTests.lean, Limits). It is
  met trivially at a bound of 1 or more, at an empty range, and at 0 under `NoStopAll`.
  (`sessionStops_at_files` is not imported here.) -/
  sessionStops : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
    (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok (fun _ => True) n w (instanceAsPlainRecord a)) hO'
  /-- On lengths and run values: the seven statements of `LensAt` -/
  lens : LensAt (lettersZ Z c₀ m₀).p c okV (fun q : Q₂ × Q₃ => (val₂ q.1, val₃ q.2)) v₀
    (fun q : R₂ × R₃ => (run₂ q.1, run₃ q.2)) startT startL startB

/-- **All hypotheses of the statement of index privacy (`PremW`), from the hypotheses by name.**
This file's head has the limits. -/
theorem premW_of_debts {Yes : FullSizeMatrix → XF → Prop} {ok : FullSizeMatrix → Prop} {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)}
    {s1 : ℕ} {zT hT' hO' : ℝ≥0∞}
    (d : PremWDebts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT' hO') :
    PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
      := 1)) (lettersZ Z c₀ m₀).p
      (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB)
      ⟨sT, homeSim Z, fun n a ρ ans =>
        (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
      ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') := by
  obtain ⟨D, r, L⟩ := d.laid
  exact premW_of_owed c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
    startL startB d.scope d.live L d.below s1 d.sessions zT hT' hO' d.links d.keyGood d.keyStops
    d.sessionStops d.rows d.owns d.lens.pre (fun q2 q3 => d.lens.okT (q2, q3)) d.lens.okL
    (fun r2 r3 => d.lens.okB (r2, r3)) d.lens.lenT d.lens.lenL d.lens.lenB

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.lensAt_plain
#print axioms AtPublicFiles.AtFiles.premW_of_debts
#print axioms AtPublicFiles.AtFiles.LensAt
#print axioms AtPublicFiles.AtFiles.PremWDebts
