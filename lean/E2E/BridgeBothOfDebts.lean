-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeBothOfDebts.lean: one conjunction, at three public files Z, at the parameters of
`lettersZ Z c₀ m₀`. Its first half is the acceptance side: `OnBytes.Prover.HonFit`
(Johnson/Prover/All/OfHonest.lean), which is what the prover of a whole request asks of three honest
provers and three families of falls (`Falls`: sets of verifier randomness that are set aside on the
acceptance side). Its second half is the privacy side: `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean), all hypotheses of the statement of index privacy. Both halves are
at one value of the three provers, `proversOf (offlineProverWithEncodedTable …) (linkProverAtFiles b Z) (famG …)`, and at one relation
Yes; `PremW` has that value as the field `Hs` of `atRecsAll` (`provers_atRecsAll`,
E2E/BridgeBothAtLink.lean: by definition). The privacy side is proved from `PremWDebts`
(E2E/BridgeDebts.lean), the structure that has its hypotheses as named fields. The theorem is
`both_atLink` (E2E/BridgeBothAtLink.lean) with `premW_of_debts` (E2E/BridgeDebts.lean) for its
second half. General in every parameter of `premW_of_debts`, and on the acceptance side in FT, Zs,
ζ, pT, zB, z and pF. The key file's prover `offlineProverWithEncodedTable` (E2E/BridgePremWKey.lean) is a prover structure
built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that nothing here
fixes (below: the shell `offlineProverWithEncodedTable`). So is each prover of the session's family `famG`
(E2E/BridgeJoinAtFiles.lean), except that the field `laid` ties its description `descZ Zp Np cF` to
Z. `linkProverAtFiles b Z` (E2E/BridgePremWLink.lean) is the link's honest prover, written out as a term.

  `both_of_debts`: `HonFit` with the bounds ζ, pT, 0 and zB + z + pF (for the OOD seeds that are set
    aside, the key file's prover, the link's and the session's), with no fall at the link; and
    `PremW` at all OOD seeds, with the numbers `indexPrivacyNumbers s1 zT 0 0 hT' 0 hO'`
    (E2E/PremisesAtFiles.lean) and the simulators sT, `homeSim Z`
    (Johnson/LinkSim/AtHome/SpecHome.lean) and, for the session, the one made of `simZ`
    (E2E/BridgeExact.lean)

Why both sides at one value. `PremW` by itself is tied to no prover that a verifier accepts: the
hypotheses from which it is proved here (`PremWDebts`) may be met by provers that never answer, and
by provers that never abort and are never accepted (the Limits of E2E/BridgeDebts.lean name both
ways). At the same three provers, the hypotheses for `HonFit` ask three things more of the session's
prover; none of the three is proved here. They ask that each sub-protocol one of whose rounds states
an item other than a root, or sends a root, have its part of the prover's (`Placed`; the fields
`halved` and `rooted` of `PlainAt`). They ask a bound zB on the measure of the public abort set
`Bad` (`BadSmall`), and zB is in the conclusion. They ask that the sub-protocols' steps accept
outside the rows' own falls (`ThreadsAt`) and a bound pF on the measure of these falls
(`FallSmall`), and pF is in the conclusion.

By what. Two calls. `honFit_atFiles` (E2E/BridgeJoinAtFiles.lean) at `nineFit_link`
(E2E/BridgeNineLink.lean) and `num_letters` (E2E/BridgeJoinAtFiles.lean), as in `both_atLink`; and
`premW_of_debts`. That every stored table which a round of the description declares is under the
item 0 (`ItemsZero`, E2E/ItemsZero.lean) is no hypothesis here: `honFit_atFiles`, and
`premW_of_owed` (E2E/BridgeOwedLink.lean), which `premW_of_debts` calls, each prove it from the
field `data` of `LaidAt`.

Hypotheses. d: `PremWDebts`; E2E/BridgeDebts.lean says what each field asks. These hypotheses of
`honFit_atFiles` are read off d, so they are asked once: `scope` (Z is in scope), `live` (the IOP's
own test on the public files accepts), `laid` (`LaidAt`) and `below` (Yes implies the object's
relation `RyesZ Z`). The others are for the acceptance side, as in `both_atLink`. k: `KeyFive`
(E2E/BridgeNineCut.lean): the clauses of `HonFit` on the key file's prover and on the measure ζ of
the OOD seeds that are set aside. h₀: the description's first test accepts one written instance. Q:
`PlainAt`. Sv: `ServesAt`. hthr: `ThreadsAt` at `TiedOut`. hb, hz, hf: three measures at the
session's prover: `BadSmall` at zB, `HidSmall` at z and at `TiedYes`, `FallSmall` at pF and at
`TiedOut`. The head of E2E/BridgeJoinAtFiles.lean says what these ask. No hypothesis is on the
link's prover: the head of E2E/BridgeBothAtLink.lean says what is proved of it on both sides.

Limits.
- A conjunction of two bundles of hypotheses of two conditional theorems. Neither theorem is called
  here: neither completeness nor index privacy of anything is concluded. No value is shown to meet
  the hypotheses on the key file's prover and on the session's, on either side, apart or together.
- One field is asked though a hypothesis of the acceptance side gives it: at hO' := z the field
  `sessionStops` follows from hz (`hidSmall_in`, E2E/BridgeJoinAtFiles.lean: `TiedIn` is `TiedYes`
  and two clauses more). The statement keeps both parameters.
- `HonFit` is only one hypothesis of the library's theorem on completeness (`complete_of_honFit`,
  Johnson/WholeKey/CompleteOfRecs.lean): `LawFit`, `WiresFit` and `SideFit` are next to it. That
  theorem also takes deciders for the abort sets, and that the honest side's strategies are those
  read off the three provers. `SideFit` reads fields of the
  scheme's honest side (`HonestSide`, Johnson/WholeKey/Defs.lean) other than its strategies:
  `HonFit` reads none of them, and nothing here ties that theorem's honest side to `atRecsAll`.
- At a Yes that holds of nothing, what is under Yes asks nothing and says nothing: among the
  hypotheses `below`, `sessionStops`, `ServesAt`, `ThreadsAt`, hz, hf and the clauses of `KeyFive`
  under Yes; in the two halves of the conclusion the clauses under Yes. What does not read Yes stays
  as it is: among the hypotheses `rows`, `owns`, `PlainAt`, `BadSmall`, the accept of the first
  test, `keyGood` and `keyStops`.
- The two sides speak of different sets of OOD seeds: Zs, what is set aside on the acceptance side,
  is a free parameter; the privacy side is stated at all seeds.
- ok, the privacy side's range of indices, is a free parameter, and nothing ties it to Yes: at a
  range that holds of no index the clauses of `PremW` on simulators, abort sets and run values are
  vacuous, while `HonFit` keeps its whole content.
- zB, z, pF, ζ and pT are free parameters: at large numbers the acceptance side's clauses on
  measures are vacuous too, and the numbers are in its half of the conclusion.
- Of the three provers only the link's is written out, as a term in b and Z only; `offlineProverWithEncodedTable` and `famG`
  are shells. sT, the key file's simulator, is a free parameter.
- Acceptance of the link is at the interactive protocol. (c₀, m₀) are fixed before the hash function
  is drawn.
- All limits of E2E/BridgeBothAtLink.lean and E2E/BridgeDebts.lean hold here. Nothing on soundness.
-/
import E2E.BridgeDebts
import E2E.BridgeBothAtLink

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
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.Prover (HonFit)
open OnBytes.WholeKey (PremW CoinNums sessionAt)
open OnBytes.LinkSim.AtHome (homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

variable (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
  (c : CoinNums (List Bool))
  (R₀ : RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (okV : ByteArray × ByteArray → Prop) (v₀ : ByteArray × ByteArray)
  (startT startL startB : ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)

/-- **The acceptance side (`HonFit`) and the privacy side (`PremW`) at one value of all three
provers**, the privacy side from the hypotheses by name (`PremWDebts`). The head of this file lists
the hypotheses. -/
theorem both_of_debts {Yes : FullSizeMatrix → XF → Prop} {ok : FullSizeMatrix → Prop} {sT : AtPublicFiles.KeyBridge.SimT (protocolAtFiles Z)}
    {s1 : ℕ} {zT hT' hO' : ℝ≥0∞}
    (d : PremWDebts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB Yes ok sT s1 zT hT' hO')
    (FT) (Zs) {ζ pT zB z pF : ℝ≥0∞}
    (k : KeyFive (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT Zs
      (lettersZ Z c₀ m₀).letters.Sd Yes ζ pT)
    (h₀ : ∃ z₀, (descZ Zp Np cF).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z Zp Np cF B G H) (Sv : ServesAt Z H Yes)
    (hthr : ThreadsAt Z Zp Np cF (R₂ := R₂) (R₃ := R₃) B G H (TiedOut Z Zp Np cF run₂ run₃ B G H Yes
      Zs))
    (hb : BadSmall (famG Z Zp Np cF run₂ run₃ B G H) zB)
    (hz : HidSmall (famG Z Zp Np cF run₂ run₃ B G H) (fun n w a => TiedYes Z Zp Np cF run₂ run₃ B G
      H Yes n w (instanceAsPlainRecord a)) z)
    (hf : FallSmall (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) (fun n w a
      => TiedOut Z Zp Np cF run₂ run₃ B G H Yes Zs n w (instanceAsPlainRecord a)) pF) :
    HonFit (proversOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) (famG Z Zp Np cF run₂ run₃ B G H))
        (fallsOf (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) _ FT (fun _ _ _ => ∅)
          (guardFall Zs (fallG Z Zp Np cF run₂ run₃ B G H)))
        (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd Yes Zs ζ pT 0 (zB + z + pF) ∧
      PremW (lettersZ Z c₀ m₀).W (lettersZ Z c₀ m₀).letters.Sd (OnBytes.Flat.codeA (v := frS.P.v) (s
        := 1)) (lettersZ Z c₀ m₀).p
        (atRecsAll c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
          startL startB)
        ⟨sT, homeSim Z, fun n a ρ ans =>
          (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe instanceAsPlainRecord _))⟩
        ok (fun _ => True) Yes c (indexPrivacyNumbers s1 zT 0 0 hT' 0 hO') := by
  obtain ⟨D, r, L⟩ := d.laid
  exact ⟨honFit_atFiles Z Zp Np cF run₂ run₃ B G H d.scope d.live L c₀ m₀
      (lettersZ Z c₀ m₀).letters.Sd (num_letters Z c₀ m₀) d.below
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z) FT (fun _ _ _ => ∅) Zs
      (nineFit_link c₀ m₀ b Z d.scope d.live (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT)
        (famG Z Zp Np cF run₂ run₃ B G H) (fallG Z Zp Np cF run₂ run₃ B G H) FT Zs k)
      h₀ Q Sv hthr hb hz hf,
    premW_of_debts c₀ m₀ b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB d⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.both_of_debts
