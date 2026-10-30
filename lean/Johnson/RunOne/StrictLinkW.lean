-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkW.lean: THE STRICT LINK's LISTED FORM AND ITS LAW OVER LETTERS: the probe of
Johnson/RunOne/StrictLinkB.lean and the laws of StrictLinkBLaws.lean said again with everything that stood fixed there as a
letter: the kit C, the rounds' data ds, the depth a, the stored openings xs (the written link over letters: linkSkeletonOfRoundData,
OnBytes/Flat/LinkSib.lean) · the carrier L : BatchProtocolWithLeafBody I XC · the number of blocks K and chal · sMT, sFS · embS, embP, xin,
embE, depthReq. The family, the list of outer roots and the instance were letters already.
  wqW          the wire: the five fields of wqX C K chal ds a xs (as Johnson/EntryRec/OklaSib.lean's wSib lays them)
  assembleW    assembleT's text over letters
  ownW, lstW, mkRdW   the lists
  stagesW      the chain, then the fourteen named tests
  listedOK_assembleW · ext_listed_assembleW · leavesOK_W · lstW_is   four of the five premises of verifyBSL_eq (the fifth,
               weX_all, ships)
  **stagesW_yes**   behind a chain that returns the fourteen lines all say yes just where verifyOneProtocol says yes
That what ran is the instance at a description's own letters: in a file outside this library.
Limits. THE LAW STANDS AT ONE SET OF LETTERS C, ds, a, xs ON BOTH SIDES: it carries nothing from one set of letters to another.
stagesW IS A FORM FOR STATEMENTS: it names the true wire wqW, whose ext is weX a with its list of all 2 * 2 ^ a positions; no run
evaluates it (the run evaluated stagesB; the form to run over letters: StrictLinkWL.lean). Nothing on soundness.

-/
import OnBytes.Flat.LinkSib
import Johnson.RunOne.StrictLinkBLaws

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.StrictW
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE bodyS wqX SOf)
open _root_.Run.PQ (View SgX weX CK XO)
open _root_.Run (bytesToBits bytesToDig rootsB)
open TypedOracleCompiler.Slice
open OnBytes.Flat (linkSkeletonOfRoundData)
open OnBytes.Maker (Steps behindSteps)
open Johnson.RunOne.StrictB

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- The wire: the five fields of the written link's, at K blocks. -/
def wqW (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ProtocolQueryLayout 256 (K + 1) (linkSkeletonOfRoundData C ds a xs dec).up :=
  ⟨(wqX C K chal ds a xs fun _ => true).sh, (wqX C K chal ds a xs fun _ => true).ext,
    (wqX C K chal ds a xs fun _ => true).decO, (wqX C K chal ds a xs fun _ => true).nOpen,
    (wqX C K chal ds a xs fun _ => true).maxDepth⟩

/-- assembleT's text over letters. -/
def assembleW (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab) :
    Option (OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) :=
  match o.run, PQ.plainsSL C ds o.rounds.toList with
  | some run, some pl =>
    some
      { salt := bytesToBits run
        roots := (rootsB o).map bytesToDig
        plains := ((), pl)
        opens := fun p => match p with
          | .inl e => e.elim
          | .inr q => opLS C (lookE run tab) 0 ds q
        ext := extE a cfg tx
        rtreq := fun _ => false
        slot := 0
        path := []
        rsalt := [] }
  | _, _ => none

/-- Where own openings can stand. -/
def ownW (tab : Tab) : Leaves := ([], []) :: ds.map fun d => ([], d.trees.map (placesOf tab))

/-- The external positions that the link reads at ρ, in the order of ix2. -/
def lstW (_ : X) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) : List (Fin (2 ^ a) ⊕ Fin (2 ^ a)) :=
  sortU (ix2 (2 ^ a))
    ((PQ.xWanted a ds xs (PQ.drawnSL C ds ρ.2)).filterMap (_root_.Run.PQ.xPos (2 ^ a)))

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The read leaves. -/
def mkRdW (x : X) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (pl : Plains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) : Leaves :=
  TypedOracleCompiler.Run.Thin.rdOfR (linkSkeletonOfRoundData C ds a xs dec).S (linkSkeletonOfRoundData C ds a xs dec).ann
    (wqW C ds a xs dec K chal).sh ((linkSkeletonOfRoundData C ds a xs dec).reads x ρ pl)

/-- **(hO)** -/
theorem listedOK_assembleW (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    ListedOK (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh π.opens (ownW ds tab) := by
  unfold assembleW at h
  split at h
  · cases h
    exact ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h),
      listedOK_opLS C K chal _ tab ds 0⟩
  · cases h

/-- **(hE)** -/
theorem ext_listed_assembleW (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    ∀ p, π.ext p ≠ none → p ∈ listedOfTx a tx := by
  unfold assembleW at h
  split at h
  · cases h
    exact ext_listed a cfg tx
  · cases h

/-- **(hR)** -/
theorem leavesOK_W (x : X) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (pl : Plains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) :
    LeavesOK (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh
      (isReadOf (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x ρ pl)
      (mkRdW C ds a xs dec K chal x ρ pl) :=
  TypedOracleCompiler.Run.Thin.leavesOK_rdOfR (linkSkeletonOfRoundData C ds a xs dec).S (linkSkeletonOfRoundData C ds a xs dec).ann
    (wqW C ds a xs dec K chal).sh
    ⟨PQ.placeOK_wire0S C K chal, PQ.placeOKS_wiresSL C K chal ds⟩
    ((linkSkeletonOfRoundData C ds a xs dec).reads x ρ pl) _ fun _ => decide_eq_true_iff

/-- **(hRE)** -/
theorem lstW_is (x : X) (ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) :
    lstW C ds a xs dec x ρ =
      (wqW C ds a xs dec K chal).ext.all.filter
        (isReadEOf (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x ρ) := by
  refine TypedOracleCompiler.Run.Thin.eq_of_sorted_mem (ix2 (2 ^ a)) _ _ (sortU_sorted _ _)
    ((weX_sorted a).filter _) fun p => ?_
  rw [List.mem_filter]
  constructor
  · intro hp
    exact ⟨weX_all a p,
      decide_eq_true (List.mem_toFinset.2 ((sortU_mem _ (ix2_inj _) p _).1 hp))⟩
  · rintro ⟨-, hp⟩
    exact (sortU_mem _ (ix2_inj _) p _).2 (List.mem_toFinset.1 (of_decide_eq_true hp))

variable {I XC : Type} (L : BatchProtocolWithLeafBody I XC) (sMT sFS : ℕ)
  (embS : (p : OPos (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) →
    OSym (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape p → Body L)
  (embP : PlainPart (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option XC) (embE : (twoExternalStrings (2 ^ a) SgX).Sym → Body L) (depthReq : ℕ)

/-- **The chain, then the fourteen named tests**, over letters. none: the chain returns nothing. -/
def stagesW (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (tab tx : Tab) : Option Steps :=
  match (Johnson.RunOne.Ask.runOk (L := L) (K := K + 1) (fun _ _ => true) F
      (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
        (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh embP 0 .first π.roots π.plains) #[] true).1 with
  | none => none
  | some (ρ, rts, ph) =>
    some (behindSteps (L := L) (K := K + 1) sMT sFS (linkSkeletonOfRoundData C ds a xs dec).up
      (wqW C ds a xs dec K chal).sh (wqW C ds a xs dec K chal).ext.less
      (wqW C ds a xs dec K chal).nOpen (wqW C ds a xs dec K chal).maxDepth embS embE depthReq cms x
      π (ownW ds tab) (listedOfTx a tx)
      (mkRdW C ds a xs dec K chal x ρ
        (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
      (lstW C ds a xs dec x ρ) F ρ rts ph)

/-- **THE TOP, OVER LETTERS.** -/
theorem stagesW_yes (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) (cms : List (Dig 256))
    (x : X) (cfg : ByteArray) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (h : assembleW C ds a xs dec cfg o tab tx = some π) :
    ((stagesW C ds a xs dec K chal L sMT sFS embS embP xin embE depthReq F cms x π tab tx).map
        OnBytes.Maker.Steps.yes).getD false =
      (verifyOneProtocol (L := L) (K := K + 1) sMT sFS .link (linkSkeletonOfRoundData C ds a xs dec).up
        (wqW C ds a xs dec K chal) embS embP xin embE depthReq cms x π).det F := by
  rw [← verifyBSL_eq (L := L) (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) sMT sFS depthReq x
    π (ownW ds tab) (listedOfTx a tx) embS embE cms .link embP xin (mkRdW C ds a xs dec K chal)
    (lstW C ds a xs dec) (listedOK_assembleW C ds a xs dec K chal cfg o tab tx π h)
    (ext_listed_assembleW C ds a xs dec cfg o tab tx π h) (weX_all a)
    (leavesOK_W C ds a xs dec K chal x) (lstW_is C ds a xs dec K chal x)]
  unfold stagesW verifyBSL
  rw [Johnson.RunOne.Ask.runOk_fst, OComp.det_bind]
  cases (recomputeChain (L := L) (K := K + 1) .link cms (xin x) π.salt π.rtreq
      (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh embP 0 .first π.roots π.plains).det F with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    show (behindSteps (L := L) (K := K + 1) sMT sFS (linkSkeletonOfRoundData C ds a xs dec).up
        (wqW C ds a xs dec K chal).sh (wqW C ds a xs dec K chal).ext.less
        (wqW C ds a xs dec K chal).nOpen (wqW C ds a xs dec K chal).maxDepth embS embE depthReq cms
        x π (ownW ds tab) (listedOfTx a tx)
        (mkRdW C ds a xs dec K chal x ρ
          (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
        (lstW C ds a xs dec x ρ) F ρ rts ph).yes =
      (if strictBBL sMT sFS (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal).sh
          (wqW C ds a xs dec K chal).ext.less depthReq π (ownW ds tab) (listedOfTx a tx)
          (mkRdW C ds a xs dec K chal x ρ
            (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
          (lstW C ds a xs dec x ρ) rts ph = true then
        afterBOL (L := L) (K := K + 1) (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal).sh
          (wqW C ds a xs dec K chal).ext.less (wqW C ds a xs dec K chal).nOpen
          (wqW C ds a xs dec K chal).maxDepth embS embE depthReq cms x π
          (mkRdW C ds a xs dec K chal x ρ
            (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
          (lstW C ds a xs dec x ρ) ρ rts ph
      else pure false).det F
    rw [OnBytes.Maker.behindSteps_yes, OnBytes.Maker.det_ite]
    cases strictBBL sMT sFS (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal).sh
      (wqW C ds a xs dec K chal).ext.less depthReq π (ownW ds tab) (listedOfTx a tx)
      (mkRdW C ds a xs dec K chal x ρ
        (effPlains (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann rts π.plains))
      (lstW C ds a xs dec x ρ) rts ph <;> rfl

end

end Johnson.RunOne.StrictW

#print axioms Johnson.RunOne.StrictW.stagesW_yes
#check @Johnson.RunOne.StrictW.stagesW_yes
