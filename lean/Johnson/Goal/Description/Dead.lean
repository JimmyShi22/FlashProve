-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Dead.lean: where the test says no, verify says no.
One arm of the verifier's three suffices, the entry file's. `Steps.yes_append_no`,
`behindSteps_never`: of the fourteen tests behind the chain the last is the description's own
decision; where that says no to all, the fourteen together say no. `armLE_never`: so the entry's arm
is false where the link's decision says no to all (`linkW_never`). `fastStepsT_never`: so the twelve
steps together are false. `stepsYes_never`: so are the steps of Johnson/Goal/Tie/TieSteps.lean, at
any record of a plan and any item. `verify_never`: at every record of letters
L: in scope, where `L.dec` says no to all at these public files, `VerifierAndGoals.verify` at the built D*
says no to every commitment, prompt, output and bytes. `theLay_dec`, `theLay_dec_dead`: `flashProveData`'s
link decision is the gate, shut where `protocolDataWellFormed` says no. `theDescription_dead`,
`theDescription_dead32`, `theDescription_dead_oracle`: the instance at the name.
`theDescription_no_of_plan`, `theDescription_no_of_key`, `theDescription_no_of_proof`: where a seat
(KeyFold.lean,
ProofFold.lean)
refuses.
Limits. At `hashOf O` for a function O on bytes whose answers have 32 bytes, the format's own hash
among them: not at every hash function. In scope alone; out of scope see `theDescription_out`. At
the description's own parser and form alone: the goals range over every parser. No public files in
scope are known at which `protocolDataWellFormed` says no. The goal G8 does not rest on this file.

-/
import Johnson.Goal.Description.Description
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A list of tests whose last says no says no. -/
theorem Steps.yes_append_no (l : Steps) (s : String) (t : Thunk Bool) (h : t.get = false) :
    Steps.yes (l ++ [(s, t)]) = false := by
  unfold Steps.yes
  rw [List.all_append]
  simp [h]

/-- **The part behind the chain says no where the description's own decision says no to all.** -/
theorem behindSteps_never (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves)
    (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos) (g : Fam (typedOracleFamily lam K L))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)
    (never : ∀ y τ, Q.loc.accept x y τ = false) :
    (behindSteps (L := L) sMT sFS Q sh wl nOpen maxDepth embS embE depthReq cms x π own listed rd
        rdE g ρ rts
      ph).yes = false := by
  unfold behindSteps
  refine Steps.yes_append_no [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ ?_
  show onF _ _ = false
  cases bothF _ _ with
  | none => rfl
  | some F => exact never _ _

end OnBytes.Maker

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL)

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (K salt : ℕ)

local notation "LKe" => linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) ds frS.P.T.a xs dec
local notation "ALe" => _root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds)
local notation "LV" => LvOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "AT" => aTOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "CV" => carrierV LV (List Bool) AT ALe

/-- **The entry's arm says no where the link's decision says no to all.** -/
theorem armLE_never (never : ∀ rr v, dec rr v = false) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (cm : Dig 256)
    (rcd : RecFull) (e : EntryIn) (πL : OneProtocolProof 256 (batLV LV ALe)) :
    armLE DK DP runK runP rK rP sB early ds xs dec K salt p F cm rcd e πL = false := by
  unfold armLE stagesWL
  split
  · rfl
  · exact behindSteps_never _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun y τ => linkW_never (ckP _root_.Fmt.Fld.two) ds frS.P.T.a xs dec never _ y τ)

/-- **The twelve steps together say no there.** -/
theorem fastStepsT_never (never : ∀ rr v, dec rr v = false) (t : Tag) (cfg : List (Dig 256)) (shape
    : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    (fastStepsT DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
        F enc build hash commitment prompt output aux cm rcd copy fT e fB).yes = false := by
  unfold fastStepsT
  cases build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases enc ⟨cm, rcd⟩ with
    | none => rfl
    | some code =>
      dsimp only
      by_cases h : hash code = commitment
      · rw [if_pos h]
        generalize piTE DK DP runK runP rK rP sT sB early ds xs dec fT = a
        generalize piLE DK DP runK runP rK rP sB early ds xs dec e = b
        generalize piBE DK DP runK runP rK rP sB early ds xs dec fB = c
        rcases a with _ | πT <;> rcases b with _ | πL <;> rcases c with _ | πB <;>
          first
          | (simp [FastSteps.yes]; done)
          | (dsimp only
             simp [FastSteps.yes, armLE_never DK DP runK runP rK rP sB early ds xs dec K salt
                 never])
      · rw [if_neg h]; rfl

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open PV.Head (cThru sevenThru)
open PV.OkOwn (okOwnF)
open LPFD.Full (XF GF stepsFAt linkAt)
open PV.EntryFive (dsF xsF)

attribute [local irreducible] PV.EncId.encF

/-- The twelve steps say no where the link's decision says no to all. -/
theorem stepsYes_never (G : FilesParameters XF RecFull) (it : XF → ByteArray) (O : ByteArray → ByteArray)
    (c : ByteArray)
    (hc : c.size = 32) (seven : List ByteArray) (h₀ : HId) (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View
        → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool) (never : ∀ rr v, dec rr v = false)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) :
    stepsYes G it O c hc seven h₀ DK DP runK runP dec commitment prompt output f = false := by
  unfold stepsYes stepsFAt
  exact fastStepsT_never _ _ _ _ _ _ _ _ _ _ _ dec _ _ never _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _

/-- **At every record of letters: where the link's decision says no to all at these public files,
  the goals' verify at the built D* says no**: to every commitment, prompt, output and bytes; at
  every `hashOf O` whose eight answers have 32 bytes. -/
theorem verify_never (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (never : ∀ rr v, L.dec (asDescriptionFiles Z) rr v = false) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) = false := by
  cases hdec : decodeD (cThru O (asDescriptionFiles Z)) B with
  | none => exact verify_descriptionOfDataOnBytes_refused L Z scope O hO h7 commitment prompt output B hdec
  | some f =>
    have h1 : (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output
        B).evaluate (hashOf O) =
        (dataAtFiles L Z).innerCompiledVerifierAnswerOnDecodedProof (cThru O (asDescriptionFiles Z)) hO (sevenThru O recordGround (asDescriptionFiles Z) (cThru O
                                                                             (asDescriptionFiles Z)))
          (hashOf O) commitment prompt output f :=
      verify_descriptionOnBytes (dataAtFiles L) L.f₀ L.honest Z scope O hO h7 commitment prompt output B f hdec
    rw [h1]
    exact (innerCompiledVerifierAnswerOnDecodedProof_dataAtFilesFromRounds L (asDescriptionFiles Z) _ _ _ (L.fit_of (asDescriptionFiles Z)) _ hO _ O L.hStar commitment
        prompt output f).trans
      (stepsYes_never _ _ _ _ _ _ _ _ _ _ _ _ never _ _ _ _)

end FlashProve

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie
open PV.Head (cThru sevenThru)

/-- `flashProveData`'s link decision is the gate: by unfolding, said once, so that no proof below has to
  see through `flashProveData`. -/
theorem theLay_dec (Zk : OnBytes.K.Pub) : flashProveData.dec Zk = theLinkGate Zk := rfl

/-- The gate is shut where protocolDataWellFormed says no. -/
theorem theLay_dec_dead (Zk : OnBytes.K.Pub) (dead : protocolDataWellFormed Zk = false) (rr : RecFull × RecFull)
    (v : _root_.Run.PQ.View) :
    flashProveData.dec Zk rr v = false := by
  rw [theLay_dec]
  exact gate1_dead dead (linkDecisionAtFiles Zk) rr v

/-- **Where `protocolDataWellFormed` says no, verify at the name says no.** -/
theorem theDescription_dead (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (dead : protocolDataWellFormed
            (asDescriptionFiles Z) = false)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate (hashOf O) =
      false :=
  atName (P := fun more L => (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z ((descriptionOfDataWithReading more L).parse Z)
      commitment prompt output B).evaluate (hashOf O) = false)
    (verify_never flashProveData Z scope (theLay_dec_dead (asDescriptionFiles Z) dead) O hO h7 commitment prompt output
      B)

/-- At every O whose answers have 32 bytes. -/
theorem theDescription_dead32 (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (dead :
            protocolDataWellFormed (asDescriptionFiles Z) = false)
    (O : ByteArray → ByteArray) (h32 : ∀ b, (O b).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate (hashOf O) =
      false :=
  theDescription_dead Z scope dead O (size_cThru _ h32 _) (size_sevenThru _ h32 _ _ _) commitment
      prompt output B

/-- At the format's own hash. -/
theorem theDescription_dead_oracle (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (dead : protocolDataWellFormed (asDescriptionFiles Z) = false) (commitment : Commitment) (prompt output : List Token) (B
                                  : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate
      (hashOf _root_.Fmt.oracle) = false :=
  theDescription_dead32 Z scope dead _root_.Fmt.oracle _root_.Fmt.size_oracle commitment prompt
      output B

/-! ## The arms where a seat refuses

These and the laws above stand at `atSecondHashFunction theDescription`: the seats' names without o are the seats
at the format's second hash function. At every o: DeadParser.lean. -/

/-- **Where the plan's seat refuses, verify at the name says no.** -/
theorem theDescription_no_of_plan (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (e :
            String)
    (h : thePlanLaid (asDescriptionFiles Z) = .error e) (O : ByteArray → ByteArray) (h32 : ∀ b, (O
                   b).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate (hashOf O) =
      false :=
  theDescription_dead32 Z scope (theLive_no_of_plan (asDescriptionFiles Z) e h) O h32 commitment prompt
      output B

/-- **Where the key file's seat refuses, verify at the name says no.** -/
theorem theDescription_no_of_key (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (e :
            String)
    (h : theKeyLaid (asDescriptionFiles Z) = .error e) (O : ByteArray → ByteArray) (h32 : ∀ b, (O
                   b).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate (hashOf O) =
      false :=
  theDescription_dead32 Z scope (theLive_no_of_key (asDescriptionFiles Z) e h) O h32 commitment prompt
      output B

/-- **Where the proof file's seat refuses, verify at the name says no.** -/
theorem theDescription_no_of_proof (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (e :
            String)
    (h : theProofLaid (asDescriptionFiles Z) = .error e) (O : ByteArray → ByteArray) (h32 : ∀ b, (O
                   b).size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) :
    (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment prompt
        output
        B).evaluate (hashOf O) =
      false :=
  theDescription_dead32 Z scope (theLive_no_of_proof (asDescriptionFiles Z) e h) O h32 commitment prompt
      output B

end FlashProve
