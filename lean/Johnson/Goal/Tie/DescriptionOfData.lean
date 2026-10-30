-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/DescriptionOfData.lean: D* built at every set of public files from one record of letters.
`DescriptionData`: the letters, each a function of the public files, the plan's values `G` and the request's
item `it` among them. `roundsDataFit`: the three tests on data that `tAt` asks, as one test. `DescriptionData.live`: the
family's test; `hlive`: its yes gives `roundsDataFit`. `dataAtFiles`: the family: where `live` says yes, the
plan's values and the data that are laid; where it says no, `Gd`
and empty data. The branch stands in the data (`filesParametersOrDefault`, `keyRoundsOrEmpty`, `proofRoundsOrEmpty`), so the fields that do not
hang on the data are L's by `rfl` (`builtS_A` and the five beside it). `builtS_live`: the family
where `live` says yes. `descriptionOfDataOnBytes`, `descriptionOfDataOnDecodedProof`: the description at the form of bytes and at the
typed form; `descriptionOfDataWithReading`: the first of them at a further public reading that is a letter;
`descriptionOfDataOnBytesIgnoringSecondHashArgument`: as the goals take it. `verify_descriptionOfDataOnBytes`, `verify_descriptionOfDataOnDecodedProof`: the goals'
verify at them. `DescriptionData.filler`, `fixedCommitterAndProver`: a filler, named as one: a coding that encodes nothing,
silent provers, an extractor that finds nothing.
Limits. `descriptionOfDataOnBytesIgnoringSecondHashArgument` does not read its argument, and `descriptionOfDataOnBytes` stands at `VerifierAndGoals.readMoreAt`,
which names the second hash function. No L is shown at which the hypotheses of a theorem on
soundness hold.

-/
import Johnson.Goal.Tie.DescriptionOnBytes
import Johnson.Top.Fire.Code.TieFilled
import Johnson.Goal.Tie.RunPureFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open OnBytes.Maker.Page (kindsAndWorkBelow256)
open PV.Head (cThru sevenThru)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR tAt tFilled codingH namedH)
open PV.EntryFive (dsF xsF)

/-- The right side of verify_descriptionOnDecodedProof, as a function of the letters at one Z. -/
def DescriptionDataAtFiles.innerCompiledVerifierAnswerOnDecodedProof {Zk : OnBytes.K.Pub} (s : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size = 32) (seven :
                                                                          List ByteArray)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token) (f :
        DecodedProof) : Bool :=
  (innerCompiledVerifier (innerCompilerInputAtFullSize (s.inputFieldsAtReadingsAsBytes c hc seven)) commitment prompt output
    ((innerCompilerInputAtFullSize (s.inputFieldsAtReadingsAsBytes c hc seven)).back (s.proofOf c f))).evaluate hash

/-- tAt's three tests on data, as one test. -/
def roundsDataFit (DK DP : WholeD) : Bool :=
  kindsAndWorkBelow256 (DK.at frS.P.T.a) && kindsAndWorkBelow256 (DP.at frS.P.T.a) && decide (KF DK DP + 1 + 1 < 2 ^ 49)

theorem fit3_iff (DK DP : WholeD) : roundsDataFit DK DP = true ↔
    kindsAndWorkBelow256 (DK.at frS.P.T.a) = true ∧ kindsAndWorkBelow256 (DP.at frS.P.T.a) = true ∧ KF DK DP + 1 + 1 < 2 ^ 49
        := by
  unfold roundsDataFit
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- The letters. -/
structure DescriptionData where
  /-- THE CLAIMS: where the claim on the output lives (A.Rel) -/
  A : OnBytes.K.Pub → (frS.toDecR frZ 402653181).Claims XF
  /-- how an index is held -/
  E : (Zk : OnBytes.K.Pub) → Coding (A Zk)
  /-- the key file's rounds' data -/
  DK : OnBytes.K.Pub → WholeD
  /-- the proof file's -/
  DP : OnBytes.K.Pub → WholeD
  runK : OnBytes.K.Pub → RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : OnBytes.K.Pub → XF × RecFull → PQ.View → PQ.View → PQ.View → Bool
  /-- THE ENTRY FILE's DECISION -/
  dec : OnBytes.K.Pub → RecFull × RecFull → PQ.View → Bool
  /-- THE PLAN's VALUES that are laid where the test says yes -/
  G : OnBytes.K.Pub → FilesParameters XF RecFull
  /-- the statement's item "request" at an instance -/
  it : OnBytes.K.Pub → XF → ByteArray
  /-- the provers, at whatever data are laid -/
  P : (Zk : OnBytes.K.Pub) → (G : FilesParameters XF RecFull) → (DK DP : WholeD) →
    (FsAtR (A Zk) (E Zk) G DK DP (runK Zk) (runP Zk) (dec Zk)).Provers
  /-- the named side -/
  N : (Zk : OnBytes.K.Pub) → (G : FilesParameters XF RecFull) → (DK DP : WholeD) →
    NamedSideOfFullD (A Zk) (E Zk) DK DP (runK Zk) (runP Zk) dsF xsF (dec Zk) G.rec₀ G.z₀.2 (sBG
        G).logLeaves
      G.early (saltG G) (P Zk G DK DP)
  /-- the extractor -/
  ext : OnBytes.K.Pub → (s : IntegerTransformer.Settings) → Commitment → QueryLog → Option
      (ModelWeights s)
  /-- the honest side, at the form of bytes -/
  honest : CommitterAndProver FormBytes
  hStar : HId
  d₀ : Dig 256
  f₀ : DecodedProof
  /-- its further tokens are no tokens of the vocabulary: SO WHERE A DECODER REFUSES verify SAYS
    no AT EVERY DescriptionData -/
  hf₀ : f₀.aux = auxNo
  /-- THE FAMILY's TEST AT THE PUBLIC FILES: where it says no, dataAtFiles lays empty data and Gd -/
  live : OnBytes.K.Pub → Bool
  /-- its yes gives tAt's three tests at the data that are laid -/
  hlive : ∀ Zk, live Zk = true → roundsDataFit (DK Zk) (DP Zk) = true
  /-- the G of the branch that refuses -/
  Gd : OnBytes.K.Pub → FilesParameters XF RecFull

/-- The bytes of the request tree's salt, off the plan's values. -/
def sROf (G : FilesParameters XF RecFull) : ℕ := G.k.oneTime.binding.saltBytes

/-- DescriptionDataAtFiles at given data that pass the test. -/
def dataAtFilesFromRounds (L : DescriptionData) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) (h : roundsDataFit DK DP =
                                           true) :
    DescriptionDataAtFiles Zk where
  G := G
  A := L.A Zk
  E := L.E Zk
  DK := DK
  DP := DP
  runK := L.runK Zk
  runP := L.runP Zk
  dec := L.dec Zk
  P := L.P Zk G DK DP
  hStar := L.hStar
  it := L.it Zk
  sR := sROf G
  hDK := ((fit3_iff DK DP).1 h).1
  hDP := ((fit3_iff DK DP).1 h).2.1
  hK := ((fit3_iff DK DP).1 h).2.2
  N := L.N Zk G DK DP
  d₀ := L.d₀
  ext := L.ext Zk

/-- The data of three empty lists. -/
def emptyRoundsData : WholeD := OnBytes.Maker.WholeD.of 0 (OnBytes.Three.Whole.of [] [] [])

/-- The test says yes at it twice. -/
theorem fit3_empty : roundsDataFit emptyRoundsData emptyRoundsData = true := by decide +kernel

/-- The plan's values that are laid: THE BRANCH STANDS IN THE DATA, NOT BETWEEN TWO RECORDS: so
  the fields of dataAtFiles L Z that do not hang on the data are L's BY rfl. -/
def DescriptionData.filesParametersOrDefault (L : DescriptionData) (Zk : OnBytes.K.Pub) : FilesParameters XF RecFull := if L.live Zk then L.G Zk else L.Gd Zk

def DescriptionData.keyRoundsOrEmpty (L : DescriptionData) (Zk : OnBytes.K.Pub) : WholeD := if L.live Zk then L.DK Zk else emptyRoundsData

def DescriptionData.proofRoundsOrEmpty (L : DescriptionData) (Zk : OnBytes.K.Pub) : WholeD := if L.live Zk then L.DP Zk else emptyRoundsData

theorem DescriptionData.fit_of (L : DescriptionData) (Zk : OnBytes.K.Pub) : roundsDataFit (L.keyRoundsOrEmpty Zk) (L.proofRoundsOrEmpty Zk) = true := by
  unfold DescriptionData.keyRoundsOrEmpty DescriptionData.proofRoundsOrEmpty
  cases h : L.live Zk with
  | true => simpa using L.hlive Zk h
  | false => simpa using fit3_empty

/-- **THE FAMILY, AT EVERY Z.** -/
def dataAtFiles (L : DescriptionData) (Z : PublicFiles) : DescriptionDataAtFiles (asDescriptionFiles Z) :=
  dataAtFilesFromRounds L (asDescriptionFiles Z) (L.filesParametersOrDefault (asDescriptionFiles Z)) (L.keyRoundsOrEmpty (asDescriptionFiles Z)) (L.proofRoundsOrEmpty (asDescriptionFiles Z)) (L.fit_of
                                                                                                                (asDescriptionFiles Z))

/-- dataAtFilesFromRounds at equal data. -/
theorem dataAtFilesFromRounds_congr (L : DescriptionData) (Zk : OnBytes.K.Pub) {G G' : FilesParameters XF RecFull} {DK DK' DP DP' :
                                           WholeD} (eG : G = G')
    (eK : DK = DK') (eP : DP = DP') (h : roundsDataFit DK DP = true) (h' : roundsDataFit DK' DP' = true) :
    dataAtFilesFromRounds L Zk G DK DP h = dataAtFilesFromRounds L Zk G' DK' DP' h' := by
  subst eG eK eP
  rfl

theorem builtS_live (L : DescriptionData) (Z : PublicFiles) (h : L.live (asDescriptionFiles Z) = true) :
    dataAtFiles L Z = dataAtFilesFromRounds L (asDescriptionFiles Z) (L.G (asDescriptionFiles Z)) (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z))
        (L.hlive _ h) :=
  dataAtFilesFromRounds_congr L (asDescriptionFiles Z) (by unfold DescriptionData.filesParametersOrDefault; rw [h]; rfl) (by unfold DescriptionData.keyRoundsOrEmpty; rw [h]; rfl)
    (by unfold DescriptionData.proofRoundsOrEmpty; rw [h]; rfl) _ _

/-- What does not hang on the data is L's, by rfl. -/
theorem builtS_A (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).A = L.A (asDescriptionFiles Z) := rfl
theorem builtS_E (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).E = L.E (asDescriptionFiles Z) := rfl
theorem builtS_runK (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).runK = L.runK (asDescriptionFiles Z) := rfl
theorem builtS_runP (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).runP = L.runP (asDescriptionFiles Z) := rfl
theorem builtS_dec (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).dec = L.dec (asDescriptionFiles Z) := rfl
theorem builtS_ext (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).ext = L.ext (asDescriptionFiles Z) := rfl

/-- At these letters T is `tAt`. -/
theorem inputFieldsAtReadingsAsBytes_dataAtFilesFromRounds (L : DescriptionData) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) (h :
                                                                 roundsDataFit DK DP = true)
    (c : ByteArray)
    (hc : c.size = 32) (seven : List ByteArray) :
    (dataAtFilesFromRounds L Zk G DK DP h).inputFieldsAtReadingsAsBytes c hc seven =
      tAt (L.A Zk) (L.E Zk) G c hc DK DP (L.runK Zk) (L.runP Zk) (L.dec Zk) (L.P Zk G DK DP)
          L.hStar (L.it Zk) (sROf G)
        (PV.RunArgsF.pdLOf seven) (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1)
        ((fit3_iff DK DP).1 h).1 ((fit3_iff DK DP).1 h).2.1 ((fit3_iff DK DP).1 h).2.2 (L.N Zk G DK
            DP) L.d₀ := rfl

/-- The honest side: hollow. -/
def fixedCommitterAndProver : CommitterAndProver FormBytes where
  Shown := Unit
  shown := fun _ _ => ()
  Rand := Unit
  sample := .done ()
  commit := fun _ _ _ _ => .done fun _ => false
  prove := fun _ _ _ _ _ _ => .done ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty,
      ByteArray.empty, ByteArray.empty⟩

/-- **A FILLER, NAMED AS ONE.** -/
def DescriptionData.filler (A : OnBytes.K.Pub → (frS.toDecR frZ 402653181).Claims XF) (DK DP : OnBytes.K.Pub →
                WholeD)
    (runK : OnBytes.K.Pub → RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : OnBytes.K.Pub → XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : OnBytes.K.Pub → RecFull × RecFull → PQ.View → Bool) (hStar : HId) (d₀ : Dig 256)
    (f₀ : DecodedProof) : DescriptionData where
  A := A
  E := fun Zk => codingH (A Zk)
  DK := DK
  DP := DP
  runK := runK
  runP := runP
  dec := dec
  P := fun Zk G dk dp => Files.fixedMessageProvers (FsAtR (A Zk) (codingH (A Zk)) G dk dp (runK Zk) (runP Zk)
                   (dec Zk))
  N := fun Zk G dk dp => namedH (A Zk) (codingH (A Zk)) G dk dp (runK Zk) (runP Zk) (dec Zk)
    (Files.fixedMessageProvers (FsAtR (A Zk) (codingH (A Zk)) G dk dp (runK Zk) (runP Zk) (dec Zk))) G.z₀.1
  ext := fun _ _ _ _ => none
  honest := fixedCommitterAndProver
  hStar := hStar
  d₀ := d₀
  f₀ := { f₀ with aux := auxNo }
  hf₀ := rfl
  live := fun Zk => roundsDataFit (DK Zk) (DP Zk)
  hlive := fun _ h => h
  G := GF
  it := fun Zk x => (PV.RunArgsF.spF Zk.pol Zk.KL x).1
  Gd := GF

/-- At the filler T is `tFilled`. -/
theorem tBytes_filler (A : OnBytes.K.Pub → (frS.toDecR frZ 402653181).Claims XF) (DKf DPf :
    OnBytes.K.Pub → WholeD)
    (runK : OnBytes.K.Pub → RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : OnBytes.K.Pub → XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : OnBytes.K.Pub → RecFull × RecFull → PQ.View → Bool) (hStar : HId) (d₀ : Dig 256)
    (f₀ : DecodedProof) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD) (h : roundsDataFit DK DP =
                        true) (c : ByteArray)
    (hc : c.size = 32) (seven : List ByteArray) :
    (dataAtFilesFromRounds (DescriptionData.filler A DKf DPf runK runP dec hStar d₀ f₀) Zk G DK DP h).inputFieldsAtReadingsAsBytes c hc seven =
      tFilled (A Zk) G c hc DK DP (runK Zk) (runP Zk) (dec Zk) hStar
        (fun x => (PV.RunArgsF.spF Zk.pol Zk.KL x).1) (sROf G)
        (PV.RunArgsF.pdLOf seven) (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1)
        ((fit3_iff DK DP).1 h).1 ((fit3_iff DK DP).1 h).2.1 ((fit3_iff DK DP).1 h).2.2 G.z₀.1 d₀ :=
            rfl

/-- **THE VALUE, THE FORM BYTES.** -/
def descriptionOfDataOnBytes (L : DescriptionData) : Description := descriptionOnBytes (dataAtFiles L) L.f₀ L.honest

/-- The same at a further public reading that is a letter. -/
def descriptionOfDataWithReading (more : PublicFiles → Digest → DeterministicAlgorithm (List (Dig 256))) (L : DescriptionData) :
    Description := descriptionOnBytesWithReading (dataAtFiles L) L.f₀ L.honest more

/-- `descriptionOfDataOnBytes` is that at `VerifierAndGoals.readMoreAt`. -/
theorem descriptionOfDataOnBytes_eq_descriptionOfDataWithReading (L : DescriptionData) :
    descriptionOfDataOnBytes L = descriptionOfDataWithReading (fun Z c => readMoreAt recordGround Z c) L := rfl

/-- **THE VALUE, THE FORM WHAT A RUN HANDS THE TERM.** -/
def descriptionOfDataOnDecodedProof (L : DescriptionData) (Hf : CommitterAndProverOfDecodedProof) : Description := descriptionOnDecodedProof (dataAtFiles L) Hf

/-- As the goals take it. IT DOES NOT READ o: the second hash stays concrete in what the plan and
  sp's item are made of. -/
def descriptionOfDataOnBytesIgnoringSecondHashArgument (L : DescriptionData) : SecondHashFunctionType → Description := fun _ => descriptionOfDataOnBytes L

theorem descriptionOfDataOnBytes_within (L : DescriptionData) (Z : PublicFiles) : Parser.Within ((descriptionOfDataOnBytes L).parse Z) 1 :=
  parseBytes_within (dataAtFiles L) L.f₀ L.honest Z

/-- **The goals' verify at the built D*, the form bytes.** -/
theorem verify_descriptionOfDataOnBytes (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : L.live (asDescriptionFiles Z) = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) (f : DecodedProof)
    (hdec : decodeD (cThru O (asDescriptionFiles Z)) B = some f) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) =
      (dataAtFilesFromRounds L (asDescriptionFiles Z) (L.G (asDescriptionFiles Z)) (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z)) (L.hlive _
                                                                     live)).innerCompiledVerifierAnswerOnDecodedProof
        (cThru O (asDescriptionFiles Z)) hO
        (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (hashOf O) commitment prompt
            output f := by
  have h1 : (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output
      B).evaluate (hashOf O) =
      (dataAtFiles L Z).innerCompiledVerifierAnswerOnDecodedProof (cThru O (asDescriptionFiles Z)) hO (sevenThru O recordGround (asDescriptionFiles Z) (cThru O
                                                                           (asDescriptionFiles Z)))
        (hashOf O) commitment prompt output f :=
    verify_descriptionOnBytes (dataAtFiles L) L.f₀ L.honest Z scope O hO h7 commitment prompt output B f hdec
  rw [h1, builtS_live L Z live]

/-- **THE SAME, THE FORM WHAT A RUN HANDS THE TERM: AT EVERY f.** -/
theorem verify_descriptionOfDataOnDecodedProof (L : DescriptionData) (Hf : CommitterAndProverOfDecodedProof) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : L.live (asDescriptionFiles Z) = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) :
    (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
        f).evaluate (hashOf O) =
      (dataAtFilesFromRounds L (asDescriptionFiles Z) (L.G (asDescriptionFiles Z)) (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z)) (L.hlive _
                                                                     live)).innerCompiledVerifierAnswerOnDecodedProof
        (cThru O (asDescriptionFiles Z)) hO
        (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (hashOf O) commitment prompt
            output f := by
  have h1 : (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
      f).evaluate (hashOf O) =
      (dataAtFiles L Z).innerCompiledVerifierAnswerOnDecodedProof (cThru O (asDescriptionFiles Z)) hO (sevenThru O recordGround (asDescriptionFiles Z) (cThru O
                                                                           (asDescriptionFiles Z)))
        (hashOf O) commitment prompt output f :=
    verify_descriptionOnDecodedProof (dataAtFiles L) Hf Z scope O hO h7 commitment prompt output f
  rw [h1, builtS_live L Z live]

end FlashProve
