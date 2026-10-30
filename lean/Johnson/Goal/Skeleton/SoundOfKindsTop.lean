-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfKindsTop.lean: `sound_of_kinds`: the goals' nearest form of soundness
for `VerifierAndGoals.theDescription`, from a closed list of named conditions. Stated at the composed
meaning's closed constant (`P5J.mgAtAll`) and at "reached, at a typed instance's public part".

THE CONDITIONS, each at one set of public files Z in scope at which `protocolDataWellFormed` accepts.
  (i) `KindsLaws`: one field for each kind of sub-protocol (K1 … K15, and the rows of the fold's own
    text, "frame"): that kind's share of the first chain's chain of promises, in the form in which
    its files end its law: `P5J.AtMgA.Kind` (Johnson/P5J/RowsAtAll.lean): `KindTiedR` at the closed
    constant, the first chain's own pieces, the table's own extractor, and `RchAt` with "the public
    part is a typed instance's". K12's field stands behind (v), as its files' theorems at that
    seat do.
  (ii) the key file: `KeySound`, whole. (Johnson/Goal/Conditions/KeySoundOfOpen.lean has it from
    three open laws by name, `KeyOpen`.)
  (iii) `five`: what is no law of a kind of the first chain and is not proved here: five rows
    (`P5J.AtMgA.Five`): head_cuts, reply_leaves, tables_fit, and the shared and the last chain's
    rows of laws (shared_joint_count, leads3_last_chains_table).
  (iv) `P5J.At.Conds Z`: the named conditions on the three public files that the head asks beside
    "in scope", "`protocolDataWellFormed` accepts" and "the files are read". At the entry tests over which this
    file was written (eight rows) NO TEST THAT `verify` RUNS ASKED THEM; at this tree's fourteen
    they follow from these three, because the like checks were moved into `verify`'s entry tests:
    they are not proved of the verifier with eight rows: `P5J.conds_of_laid` (CondsOfLaid.lean) at
    `P5J.owed_of_live` (OwedOfLive.lean).
  (v) `H2K12.LastTypedAt` at Z's three files (Johnson/Loose/H2K12/K12LawR.lean): the sized stages of
    the first chain's last proximity test are the typed list. A closed condition on the public
    files; at eight rows no test that `verify` runs asked it either; at this tree's fourteen it
    follows likewise from "in scope" and "`protocolDataWellFormed` accepts": `H2K12.lastTypedAt_of_live`
    (Johnson/Loose/H2K12/LastTypedOfLaid.lean).
(i) and (iii) are asked under every head `P5J.AtMgA` at the name (the letters Zp Np cF x at which
the laid value opens), at a filling 𝔏 of the tower's free letters OF THE PAYER's CHOICE
(`ProofKinds h`).
  `proofFileAt_of_kinds`: (i), (iii), (iv) and (v) AT Z give `ProofFileAt Z`: the proof file's
    share, at these files alone.
  `sound_of_kinds`: with (ii), and the four at every such Z: `NearestSound theDescription` at
    `VerifierAndGoals.soundnessErrorInQueries t 1`.

Limits. NO CONDITION IS SHOWN TO BE MET: THE THEOREM MAY BE EMPTY. `sound_of_kinds` asks its
conditions at EVERY Z in scope at which `protocolDataWellFormed` accepts: where one fails at one such Z, the
hypothesis is false and the theorem says nothing, at the release's files either. (iv) and (v)
follow, at this tree's fourteen entry tests, from "in scope", "the files are read" and "`protocolDataWellFormed`
accepts" (see (iv) and (v) above). 𝔏
is not a closed term. The shared and the last chain's laws are asked as whole rows, not kind by
kind. The full size alone. That `protocolDataWellFormed` accepts at the release's files as bytes is said by an
evaluation alone; at the written copies it is a theorem (AtFullSide/Top/). This file only calls
joinings of other files (`P5J.proofFileAt_of_owedA`, `top_sound_of_two`).

-/
import Johnson.Goal.TopOfTwo
import Johnson.P5J.ProofFileAtNameA
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Loose.H2K12.K12LawR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName

/- The names in scope are those of Johnson/P5J/ProofFileAtMg.lean, and `P5J`'s own. -/
open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifierAndGoals FlashProve FlashProve
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **(i) One law for each kind of sub-protocol.** -/
structure KindsLaws (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  k1 : h.Kind 𝔏 .K1
  k2 : h.Kind 𝔏 .K2
  k3 : h.Kind 𝔏 .K3
  k4 : h.Kind 𝔏 .K4
  k5 : h.Kind 𝔏 .K5
  k6 : h.Kind 𝔏 .K6
  k7 : h.Kind 𝔏 .K7
  k8 : h.Kind 𝔏 .K8
  k9 : h.Kind 𝔏 .K9
  k10 : h.Kind 𝔏 .K10
  k11 : h.Kind 𝔏 .K11
  k12 : H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 .K12
  k13 : h.Kind 𝔏 .K13
  k14 : h.Kind 𝔏 .K14
  k15 : h.Kind 𝔏 .K15
  frame : h.Kind 𝔏 .frame

/-- All kinds. -/
theorem KindsLaws.all {h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x}
    {𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok} (L : KindsLaws h 𝔏)
    (hT : H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) : ∀ K, h.Kind 𝔏 K
  | .K1 => L.k1
  | .K2 => L.k2
  | .K3 => L.k3
  | .K4 => L.k4
  | .K5 => L.k5
  | .K6 => L.k6
  | .K7 => L.k7
  | .K8 => L.k8
  | .K9 => L.k9
  | .K10 => L.k10
  | .K11 => L.k11
  | .K12 => L.k12 hT
  | .K13 => L.k13
  | .K14 => L.k14
  | .K15 => L.k15
  | .frame => L.frame

/-- **The proof file's conditions under one head at the name**: there is a filling of the tower's
free letters at which the lists' heads are the description's, and (i) and (iii) hold. -/
def ProofKinds (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x) : Prop :=
  ∃ (𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (_ : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str),
    𝔏.rP = recZ Z ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃ ∧
    KindsLaws h 𝔏 ∧ h.Five 𝔏 (depthZ Z)

/-- They are what the tower's last joining asks. -/
theorem ProofKinds.owed {h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x}
    (P : ProofKinds h) (hT : H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) : OwedAll h := by
  obtain ⟨𝔏, d, hr, q₁, q₂, q₃, L, V⟩ := P
  exact ⟨𝔏, d, hr, q₁, q₂, q₃, L.all hT, V⟩

/-- **The proof file's share at one set of public files, from the conditions at these files.** -/
theorem proofFileAt_of_kinds (Z : VerifierAndGoals.PublicFiles) (hs : InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (conds : At.Conds Z)
    (lastTyped : H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : ∀ Zp Np cF x (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
      ProofKinds h) : ProofFileAt Z := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hs
  exact proofFileAt_of_owedA Z hs hl hR conds
    fun Zp Np cF x h => (kinds Zp Np cF x h).owed lastTyped

/-- **SOUNDNESS FROM ONE LAW FOR EACH KIND OF SUB-PROTOCOL AND A CLOSED LIST OF NAMED
CONDITIONS.** -/
theorem sound_of_kinds (kS : KeySound)
    (conds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      ∀ Zp Np cF x (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        ProofKinds h) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  top_sound_of_two kS (proofSound_of_proofFileAt fun Z hs hl =>
    proofFileAt_of_kinds Z hs hl (conds Z hs hl) (lastTyped Z hs hl) (kinds Z hs hl))

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofFileAt_of_kinds
#print axioms VerifierAndGoals.AtTheName.sound_of_kinds
