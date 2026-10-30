-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkWL.lean: THE FORM TO RUN of the strict link's probe over letters. stagesW (StrictLinkW.lean) is
written at the fields of the wire record wqW, whose field ext is weX a: a record that holds the list of all 2 * 2 ^ a external
positions, built when the record is built. At a = 32 that does not end. Here the pieces are laid outright, as wqXL
lays them at a description (OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean:110-115): the rounds' wires; (weXL a []).less for the external
wiring without its list; the two numbers.
  shW, nOpenW, maxDepthW   the pieces
  mkRdWL     the read leaves, at shW
  stagesWL   the chain, then the fourteen named tests: THE FORM TO RUN
  **stagesWL_is**   stagesWL .. = stagesW ..: by cases on the chain's value, each case by rfl
  stagesWL_yes   so the law stagesW_yes holds of it
  vLA_stagesL    and verifyLinkProof's value at every family is its fourteen lines' yes
Limits. That no list of length 2 ^ a is built by stagesWL is by reading its text and that of what it calls; no theorem speaks of
cost. It has not been run. It runs only at arguments that have code: the letters C, ds, a, xs themselves (at the written letters of
innerCompiledVerifier's object ds has none), the carrier L, which is handed over as a value, and the family F. All the
limits of StrictLinkW.lean and StrictLinkVLA.lean: ONE SET OF LETTERS ON BOTH SIDES. Nothing on soundness.

-/
import Johnson.RunOne.StrictLinkVLA

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.StrictW
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (wqX SOf)
open _root_.Run.PQ (View SgX weX CK XO)
open TypedOracleCompiler.Slice
open OnBytes.Flat (linkSkeletonOfRoundData linkProtocolOfRoundData)
open OnBytes.Maker (Steps behindSteps)
open OnBytes.RunA (RestR LrG wSib bodiesSib)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wireOf2 typedOracleCarrier verifyLinkProof cmsLA)
open Johnson.RunOne.StrictB

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The rounds' wires, laid outright. -/
def shW : RoundsQueryLayout 256 (K + 1) (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann :=
  (PQ.wire0S C K chal, PQ.wiresSL C K chal ds)

/-- The number of openings allowed. -/
def nOpenW : ℕ := PQ.nOpen ds + (xs.map (·.count)).sum

/-- The depth allowed. -/
def maxDepthW : ℕ := max (PQ.maxDepth ds) a

/-- The read leaves, at the wires laid outright. -/
def mkRdWL (x : X) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (pl : Plains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) : Leaves :=
  TypedOracleCompiler.Run.Thin.rdOfR (linkSkeletonOfRoundData C ds a xs dec).S (linkSkeletonOfRoundData C ds a xs dec).ann
    (shW C ds a xs dec K chal) ((linkSkeletonOfRoundData C ds a xs dec).reads x ρ pl)

variable {I XC : Type} (L : BatchProtocolWithLeafBody I XC) (sMT sFS : ℕ)
  (embS : (p : OPos (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) →
    OSym (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape p → Body L)
  (embP : PlainPart (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option XC) (embE : (twoExternalStrings (2 ^ a) SgX).Sym → Body L) (depthReq : ℕ)

/-- **THE FORM TO RUN.** none: the chain returns nothing. -/
def stagesWL (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (tab tx : Tab) : Option Steps :=
  match (Johnson.RunOne.Ask.runOk (L := L) (K := K + 1) (fun _ _ => true) F
      (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
        (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (shW C ds a xs dec K chal) embP 0 .first π.roots π.plains) #[] true).1 with
  | none => none
  | some (ρ, rts, ph) =>
    some (behindSteps (L := L) (K := K + 1) sMT sFS (linkSkeletonOfRoundData C ds a xs dec).up
      (shW C ds a xs dec K chal) (weXL a []).less (nOpenW ds xs) (maxDepthW ds a) embS embE depthReq
      cms x π (ownW ds tab) (listedOfTx a tx)
      (mkRdWL C ds a xs dec K chal x ρ
        (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
      (lstW C ds a xs dec x ρ) F ρ rts ph)

/-- **The form to run is stagesW.** -/
theorem stagesWL_is (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256))
    (x : X) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (tab tx : Tab) :
    stagesWL C ds a xs dec K chal L sMT sFS embS embP xin embE depthReq F cms x π tab tx =
      stagesW C ds a xs dec K chal L sMT sFS embS embP xin embE depthReq F cms x π tab tx := by
  unfold stagesWL stagesW
  have e : (Johnson.RunOne.Ask.runOk (L := L) (K := K + 1) (fun _ _ => true) F
      (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
        (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh embP 0 .first π.roots π.plains) #[] true).1 =
    (Johnson.RunOne.Ask.runOk (L := L) (K := K + 1) (fun _ _ => true) F
      (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
        (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (shW C ds a xs dec K chal) embP 0 .first π.roots π.plains) #[] true).1 := rfl
  rw [e]
  cases (Johnson.RunOne.Ask.runOk (L := L) (K := K + 1) (fun _ _ => true) F
      (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
        (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (shW C ds a xs dec K chal) embP 0 .first π.roots π.plains) #[] true).1 with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    rfl

/-- The law, at the form to run. -/
theorem stagesWL_yes (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256))
    (x : X) (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    ((stagesWL C ds a xs dec K chal L sMT sFS embS embP xin embE depthReq F cms x π tab tx).map
        OnBytes.Maker.Steps.yes).getD false =
      (verifyOneProtocol (L := L) (K := K + 1) sMT sFS .link (linkSkeletonOfRoundData C ds a xs dec).up
        (wqW C ds a xs dec K chal) embS embP xin embE depthReq cms x π).det F := by
  rw [stagesWL_is]
  exact stagesW_yes C ds a xs dec K chal L sMT sFS embS embP xin embE depthReq F cms x cfg o tab tx
    π h

end

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List PQ.RD} {xs : List XO}
  {dec : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT)) (wB : ProtocolQueryLayout 256 (K + 1) T.bat)
  (depthReq depthReqT depthReqL salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))

/-- **verifyLinkProof's value is the yes of the fourteen lines of the form to run.** -/
theorem vLA_stagesL (cA : Ans → List (Dig 256)) (p : Params) (cm cm' : Dig 256)
    (rec rec' : Seed × Ans)
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1)
      (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))
    (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    (verifyLinkProof (WSib T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB) cA p cm cm'
        rec rec' π).det F =
      ((stagesWL C ds a xs dec K chal
          (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) p.sMT p.sFS
          (TypedOracleCompiler.StringsList.embT salt C ds) id (fun _ => none)
          (TypedOracleCompiler.Run.PQ.bodyS a salt).embE depthReqL F
          (cmsLA (L := LrG T) cA cm cm' rec.2 rec'.2) (rec, rec') π tab tx).map
        OnBytes.Maker.Steps.yes).getD false := by
  rw [stagesWL_is]
  exact vLA_stages T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB cA p cm cm'
    rec rec' F cfg o tab tx π h

end

end Johnson.RunOne.StrictW

#print axioms Johnson.RunOne.StrictW.stagesWL_is
#print axioms Johnson.RunOne.StrictW.stagesWL_yes
#print axioms Johnson.RunOne.StrictW.vLA_stagesL
#check @Johnson.RunOne.StrictW.stagesWL_is
#check @Johnson.RunOne.StrictW.vLA_stagesL
