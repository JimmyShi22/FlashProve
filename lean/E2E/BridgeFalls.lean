-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeFalls.lean: `fallBC` is the set of verifier randomness at which an honest run over a
description meets a fall, in the type in which the prover of a whole request takes a family of falls
(`FallB`, E2E/BridgeAccept.lean, from which `fallsOf` builds the field `B` of `Falls`,
Johnson/Prover/All/OfHonest.lean). Two hypotheses of E2E/BridgeAccept.lean are proved: `FallZero` of
this set and `WithheldZero` of its prover. They say that neither the fall nor the abort set depends
on the proof-of-work test bits. It is for files that have to show the acceptance side (`HonFit`,
same file as `Falls`). First general in all parameters of `ProofFile.Honest.honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean); then at the library's object, along a writing map wr,
at the library's three protocols of the full size at any parameters (`threeProtocolsAtFullSize`). The parameters
at three public files Z are among these (`filesAt`, E2E/ObjectAtFiles.lean); no declaration here
names Z.

The two types. A fall (`Fall`, Johnson/Desc/ProofFile/Honest/Side.lean: a place, a test and a stated
number) is meant as a test of the verifier's that an honest run may fail at some of the run's coins.
`ProofFile.Honest.fallAt G H w₀ rc x k δ` (Johnson/Desc/ProofFile/Honest/Fall.lean) says where a run meets
one: at an input, the run's coins k (`Coins`) and lists δ of challenges (`Draws`). G: the rows
(`Sides`, Johnson/Desc/ProofFile/Honest/Rule.lean: for each sub-protocol the prover's part and its
simulator; for each chain a list of falls). H: a prover structure (`ProofFile.Honest.Prover`);
`G.prover H` is H with the prover's parts of G. A value of `FallB` takes the copy's number, the
private input, the instance and the prover's coin c, and returns a set of verifier randomness, which
is set aside on the acceptance side. The two fit: the prover's coin is a pair of (shared `Purse`, a
value in R₂) and ((first `Purse`, second `Purse`), a value in R₃); the run's coins are the three
values of `Purse`.

  `fallZero_along`: `FallZero` of `fallAlong`, at the family `famAlong` of the prover structure
    `G.prover H` and at the library's wiring `wireOfFullD`, at every K and depthReqT: where ρ with
    all test bits set to 0 is in the fall's set, so is ρ. No hypothesis
  `withheldZero_along`: `WithheldZero` of `famAlong`, at the same wiring: the same for the abort set
    (`withheld`: the public abort set `Bad` together with the abort set `Hid`, which may depend on
    the private input). For any prover structure H. No hypothesis
  `fallAlong`: a definition: `fallBC` at the proof file's rounds' data and fixed plain parts of
    `threeProtocolsAtFullSize`, at the instance `wr a`: a value of `FallB (famAlong …)`, in the object's types
  `fallBC`: a definition: the set of the ρ at which `fallAt G H w.1 w.2.1 x k (drawsAt … ρ)` is not
    `none`, k the three values of `Purse` in c; c is a coin of the family `honestProversByCopyNumber` of the prover
    structure `G.prover H`. The copy's number, `w.2.2` and the values in R₂ and R₃ are not read
  `fall_zero`: ρ with all test bits set to 0, under the wiring data `wiresOf C K chal D tF tJ t3`
    (OnBytes/Maker/Wire.lean), is in `fallBC …` just when ρ is
  `withheld_zero`: the same for the abort set of `honestProversByCopyNumber` at every number n, for any prover structure
    H'
  `drawsAt_zero`: the lists of challenges that the honest side reads off a verifier randomness
    (`ProofFile.Honest.drawsAt`, Johnson/Desc/ProofFile/Honest/Law/StratWords.lean) are the same with all
    test bits set to 0, under the same wiring data
  `prover_comm`: `Cm.proverAt 0 (G.prover H) = G.prover (Cm.proverAt 0 H)`: to set in a prover
    structure the committer's key and its stored table, at the item 0 and at no other item
    (`Committer.proverAt`, Johnson/Desc/ProofFile/Honest/CommitterAt.lean), and to set in it the
    prover's parts of the rows G (`Sides.prover`) commute: by unfolding

By what. `drawsAt` is the library's `drawnT` of the three chains' parts of ρ, with one empty
challenge after the first chain's. By `rho₁_zero`, `rho₂_zero` and `rho₃_zero`
(E2E/ReadsBlind.lean), to set the test bits of ρ to 0 is to set them to 0 in each of the three
parts; by `drawn_zeroLo` and `drawn_zeroSh` (same file) `drawnT` is then the same. `fallBC` reads ρ
through `drawsAt` only: so `fall_zero`. `withheld_zero` joins `AtPublicFiles.Reads.bad_zero` and
`AtPublicFiles.Reads.hid_zero` (E2E/DrawsBlind.lean). The two statements at the object are one direction of
`withheld_zero` and of `fall_zero`, at `ckP .two`, `DP.at frS.P.T.a` and `chalP .two K`; the types
fit by unfolding. Definitions: `Family` (E2E/HonestFamily.lean); `honestProversByCopyNumber`, `famAlong`
(E2E/BridgeAlong.lean); `FallB`, `WithheldZero`, `FallZero`, `FallSmall`, `AccAtTied`
(E2E/BridgeAccept.lean); `threeProtocolsAtFullSize`, `wireOfFullD` (Johnson/Flat/Dec/WiresAtSizes.lean).

Limits.
- `fallAt` returns `none` where the run ends for another reason (a stop, a fault), and it reads the
  lists of falls that G holds next to its rows (`falls₁`, `falls₂`, `falls₃`). That every rejection
  of an honest run is one of these is part of the acceptance statement (`AccAtTied`), which is shown
  of no prover in this folder: E2E/BridgeLink.lean and E2E/BridgeLinkAtFiles.lean prove it from
  hypotheses.
- A fall's test is a field of the rows G: nothing compares it with a test of the verifier's. A fall
  whose test returns something too often makes the set large, and with it the bound at which
  `FallSmall` can hold. Where G names no fall the set is empty and `fallZero_along` is vacuous.
- No measure of the set is shown.
- The object and the wiring are the library's; the honest side is arbitrary: the description F, the
  writing map wr, the rows G and the prover structure H are free parameters. Nothing ties them to
  the object but the proof file's rounds' data and fixed plain parts at which `honestProversByCopyNumber` is taken, and
  the configuration `DecR.configurationOfStoredTable A R` in the types of G, H, J and ext.
- The form. A fall depends on the prover's coins: it is a second set, which reads the coin, for
  completeness only, and is not folded into the abort set. `HonFit` asks for acceptance at every
  coin outside the abort set and the fall at that coin, and for the measure at each fixed coin; a
  mean over the coins of these bounds then bounds the error over verifier randomness and coins
  jointly, which is how the goals measure. It does not bound the set of verifier randomness at which
  some coin falls.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.BridgeAlong
import E2E.BridgeAccept
import Johnson.Desc.ProofFile.Honest.Fall
import Johnson.Desc.ProofFile.Honest.CommitterAt
import Johnson.Desc.ProofFile.Honest.Law.StratWords

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Reads
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open ProofFile.Honest (drawsAt Draws)

variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **The lists of challenges of `drawsAt` are the same with all test bits set to 0**, under the
wiring data `wiresOf`. -/
theorem drawsAt_zero (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    drawsAt C D tF tJ t3 (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ) =
      drawsAt C D tF tJ t3 ρ := by
  unfold ProofFile.Honest.drawsAt
  rw [rho₁_zero (wiresOf C K chal D tF tJ t3) ρ, rho₂_zero (wiresOf C K chal D tF tJ t3) ρ,
    rho₃_zero (wiresOf C K chal D tF tJ t3) ρ]
  have e₁ := drawn_zeroLo C K chal D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)
  have e₂ := drawn_zeroSh C K chal D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)
  have e₃ := drawn_zeroLo C K chal D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)
  exact congr (congr (congrArg Draws.mk
    (congrArg (· ++ [(⟨[], [], [], none⟩ : Fmt.Drawn)]) e₁)) e₂) e₃

end AtPublicFiles.Reads

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD chainsOf wiresOf)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides fallAt drawsAt Committer)

section BC
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ)
  (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool)
  (B : ProverCoinCounts) (G : Sides F B W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂]
  [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **The fall's set at the prover's coin c**: the ρ at which `fallAt`, at the three values of
`Purse` in c and at the challenges `drawsAt … ρ`, is not `none`. The copy's number is not read. -/
def fallBC (_ : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (c : (honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).Coin) :
    Set (Rho (batchOf C D tF tJ t3 F silent).loc.shape) :=
  {ρ | (fallAt G H w.1 w.2.1 x
    ⟨(c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)).2.1.1,
      (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)).1.1,
      (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)).2.1.2⟩
    (drawsAt C D tF tJ t3 ρ)).isSome = true}

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **The fall's set does not depend on the test bits.** -/
theorem fall_zero (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (c : (honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover H) J sh ext).Coin)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ ∈
        fallBC C D tF tJ t3 F silent B G H J sh ext n w x c ↔
      ρ ∈ fallBC C D tF tJ t3 F silent B G H J sh ext n w x c := by
  have e := AtPublicFiles.Reads.drawsAt_zero C D tF tJ t3 K chal ρ
  show (fallAt G H w.1 w.2.1 x _ (drawsAt C D tF tJ t3
    (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))).isSome = true ↔ _
  rw [e]
  exact Iff.rfl

/-- The same for the abort set, for any prover structure H'. -/
theorem withheld_zero (H' : Prover W₀ Rc Xi Ky Tr X₀ X) (n : ℕ) (w : W₀ × Rc × Sd) (x : Xi)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ ∈
        ((honestProversByCopyNumber C D tF tJ t3 F silent B H' J sh ext).at n).withheld w x ↔
      ρ ∈ ((honestProversByCopyNumber C D tF tJ t3 F silent B H' J sh ext).at n).withheld w x :=
  or_congr (AtPublicFiles.Reads.bad_zero C D tF tJ t3 K chal F silent B H' (J 0) sh ext ρ)
    (AtPublicFiles.Reads.hid_zero C D tF tJ t3 K chal F silent B H' (J n) sh ext w x ρ)

/-- To set the committer's key and its stored table, at the item 0 only (`Committer.proverAt`), and
to set the prover's parts of the rows G (`Sides.prover`) commute. -/
theorem prover_comm {Xr : Type} (Cm : Committer W₀ Rc Sd Xr Xi Ky) :
    Cm.proverAt 0 (G.prover H) = G.prover (Cm.proverAt 0 H) := rfl

end BC

end AtPublicFiles.Bridge

/-! ## At the library's object, along a writing map, at any parameters of the full size -/

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Bridge AtPublicFiles.Along
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides)

section General
variable {X Xi : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool)
  (runP : X × RecFull → View → View → View → Bool) (F : FileDescription Xi) (wr : X × RecFull → Xi)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (silent : Xi → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {Ky Tr X₀ X' R₂ R₃ : Type} (B : ProverCoinCounts)
  (G : Sides F B (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) Ky Tr X₀ X')
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) Xi Ky Tr X₀ X')
  [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (DecR.configurationOfStoredTable A R).Seed Xi Ky (OnBytes.Maker.FrontMsg (List OnBytes.E))
    (Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) ByteArray)
  (sh : Ky → F.S₂)
  (ext : (DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed →
    (Iop.oneExternalString (2 ^ (DP.at frS.P.T.a).a) _root_.Run.PQ.SgX).Str)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

/-- **The fall's sets along the writing map wr, in the object's types**: `fallBC` at the instance
`wr a`. -/
def fallAlong :
    FallB (famAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B
      (G.prover H) J sh ext P) :=
  fun n w a c => fallBC (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty F silent B G H J sh ext n w (wr a) c

/-- **`WithheldZero` of `famAlong`, at the library's wiring `wireOfFullD`**, with no hypothesis, for
any prover structure H. -/
theorem withheldZero_along :
    WithheldZero
      (famAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B H J sh ext P)
      (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) :=
  fun n w a ρ => (withheld_zero (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty F silent B J sh ext K (chalP .two K) H n w (wr a) ρ).1

/-- **`FallZero` of `fallAlong`, at the library's wiring `wireOfFullD`**, with no hypothesis. -/
theorem fallZero_along :
    FallZero
      (famAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B (G.prover H)
        J sh ext P)
      (fallAlong A R DK DP runK runP F wr ds xs dec rK rP depthReq early salt silent B G H J sh ext
        P)
      (wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT) :=
  fun n w a c ρ => (fall_zero (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty F silent B G H J sh ext K (chalP .two K) n w (wr a) c
    ρ).1

end General

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Reads.drawsAt_zero
#print axioms AtPublicFiles.Bridge.fall_zero
#print axioms AtPublicFiles.Bridge.withheld_zero
#print axioms AtPublicFiles.Bridge.prover_comm
#print axioms AtPublicFiles.AtFiles.withheldZero_along
#print axioms AtPublicFiles.AtFiles.fallZero_along
#print axioms AtPublicFiles.Bridge.fallBC
#print axioms AtPublicFiles.AtFiles.fallAlong
