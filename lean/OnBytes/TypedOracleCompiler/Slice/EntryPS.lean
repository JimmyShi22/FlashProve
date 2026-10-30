-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryPS.lean: THE ENTRY's WRITTEN LINK WITH AN INSTANCE AS A SKELETON: PSXE D
dec : Twin.PS, WITH (PSXE D dec).up = ofProto (LinkX D dec) AND THE WIRING CARRIED: ONE EQUATION,
ONCE. So what is stated at a skeleton's P.up (chainP_det, lax_thin | lax_ext, verifyLX,
chain_end_lo) applies to ZXE (Slice/EntryX.lean).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. RoundSplits.allLocal (uL C ds) = Twin.allLo (SL C ds) is not rfl at a variable ds. ZXE's Z.Q is
BatchInteractiveOracleProof.ofProto (LinkX D dec): its marking is RoundSplits.allLocal; its wiring wqLX takes the fields of
wq0, which comes through wireTo (psofX_up …): a cast. A skeleton's marking is Twin.allLo.
  PSXE D dec         skeletonOverBothExternalStrings's skeleton, what is read as skeletonOverBothExternalStrings reads it (no look at the decision),
    accept at dec x. COMPUTABLE
  psxe_loc               (PSXE D dec).up.loc = LinkX D dec: by definition
  psxe_up            (PSXE D dec).up = BatchInteractiveOracleProof.ofProto (LinkX D dec): along the library's
    allLo_eq
  wqXE D dec         its wiring: the fields of wX D (fun _ => true). COMPUTABLE
  wireTo_mk              a wiring carried along an equation of markings: its wires carried; the four
    other fields as they are
  wqLX_eq            wqLX D dec = wireTo (psxe_up D dec) (wqXE D dec)
  verifyB_ann        the LAX verifier does not change when the marking is replaced by an equal
    one and wiring, string and the map on plain parts are carried along (the sibling's verifyBS_ann,
    for verifyB)
  toPS π                 a string of Z.Q as a string of (PSXE D dec).up: the same nine fields
    (reAnn);  ofPS: back
  ZXE_verifier       (ZXE …).verifier cms x π = verifyB .link (PSXE D dec).up (wqXE D dec) E.emb
    (pbTo allLo_eq) some B.embE 0 cms x (toPS π)
  ZXE_run            for idx one to one: ((ZXE …).verifier cms x π).det F = verifyLX (fun _ =>
    LXE …) F (maskOf idx) (maskBit idx) early none .link (PSXE D dec) (wqXE D dec) E.emb (pbTo …)
    some B.embE 0 cms x (toPS π): THE JUDGE's SECOND HALF AS AN EVALUABLE TERM
WHAT IS NOT SAID. The judge's first half (the seeds' chains). Any family, page, typing or file. That
the evaluable term comes home at a size.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryX
import OnBytes.TypedOracleCompiler.Run.LaxThin

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE skeletonOverBothExternalStrings wX psofX_up wireTo wireTo_okg wireTo_ext
    reAnn pbTo SOf)
open _root_.Run.PQ (View SgX weX)
open _root_.Run.Twin (PS)
open TypedOracleCompiler.Run.Thin (verifyLX lax_ext)
open _root_.Run.Thin (maskOf maskBit)

/-! ## General: the lax verifier along an equation of markings -/

section
variable {Y : Type} {E : ExtSpec} {lam K : ℕ}

/-- a wiring carried along an equation of markings -/
theorem wireTo_mk (loc : InteractiveOracleProof Y E) {A A' : RoundSplits loc.shape} (h : A = A')
    (w : ProtocolQueryLayout lam K ⟨loc, A⟩) :
    wireTo (congrArg (BatchInteractiveOracleProof.mk loc) h) w =
      (⟨h ▸ w.sh, w.ext, w.decO, w.nOpen, w.maxDepth⟩ : ProtocolQueryLayout lam K ⟨loc, A'⟩) := by
  subst h
  rfl

/-- The lax compiled verifier along an equation of markings. -/
theorem verifyB_ann {I X : Type} {L : BatchProtocolWithLeafBody I X} (t : Tag) (loc : InteractiveOracleProof Y E)
    (A A' : RoundSplits loc.shape) (h : A = A') (wq : ProtocolQueryLayout lam K ⟨loc, A⟩)
    (embS : (p : OPos loc.shape) → OSym loc.shape p → Body L)
    (embP : PlainPart loc.shape A → PlainPart (shapeOf L t) (annOf L t))
    (embP' : PlainPart loc.shape A' → PlainPart (shapeOf L t) (annOf L t))
    (hP : ∀ z, embP z = embP' (pbTo h z))
    (xin : Y → Option X) (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam ⟨loc, A⟩) :
    verifyB t ⟨loc, A⟩ wq embS embP xin embE depthReq cms x π =
      verifyB t ⟨loc, A'⟩ (wireTo (congrArg (BatchInteractiveOracleProof.mk loc) h) wq) embS embP' xin embE
        depthReq cms x (reAnn A' π) := by
  subst h
  have hE : embP = embP' := funext hP
  subst hE
  rfl

end

/-! ## The skeleton -/

variable {X : Type} (D : XD) (dec : X → View → Bool)

/-- The written link with an instance, as a skeleton. -/
@[reducible] def PSXE : PS X (twoExternalStrings (2 ^ D.a) SgX) where
  S := SOf D.C D.ds
  blinded := (skeletonOverBothExternalStrings D.C D.ds D.a D.xs fun _ => true).blinded
  extReads := fun _ ρ => (skeletonOverBothExternalStrings D.C D.ds D.a D.xs fun _ => true).extReads () ρ
  reads := fun _ ρ π => (skeletonOverBothExternalStrings D.C D.ds D.a D.xs fun _ => true).reads () ρ π
  accept := fun x y τ => (skeletonOverBothExternalStrings D.C D.ds D.a D.xs (dec x)).accept () y τ
  ann := _root_.Run.Twin.allLo (SOf D.C D.ds)

theorem psxe_loc : (PSXE D dec).up.loc = LinkX D dec := rfl

/-- The one equation. -/
theorem psxe_up : (PSXE D dec).up = BatchInteractiveOracleProof.ofProto (LinkX D dec) :=
  congrArg (BatchInteractiveOracleProof.mk (LinkX D dec)) (_root_.Run.Twin.allLo_eq (SOf D.C D.ds))

/-- Its wiring: the fields of the description's own. -/
def wqXE : ProtocolQueryLayout 256 (D.K + 1) (PSXE D dec).up :=
  ⟨(wX D fun _ => true).sh, (wX D fun _ => true).ext, (wX D fun _ => true).decO,
      (wX D fun _ => true).nOpen,
    (wX D fun _ => true).maxDepth⟩

/-- The wiring wqLX is this one, carried along the equation. -/
theorem wqLX_eq : wqLX D dec = wireTo (psxe_up D dec) (wqXE D dec) := by
  have e0 : wq0 D (fun _ => true) = _ :=
    wireTo_mk (Link0 D fun _ => true) (_root_.Run.Twin.allLo_eq (SOf D.C D.ds)) (wX D fun _ => true)
  have e1 : wireTo (psxe_up D dec) (wqXE D dec) = _ :=
    wireTo_mk (LinkX D dec) (_root_.Run.Twin.allLo_eq (SOf D.C D.ds)) (wqXE D dec)
  unfold wqLX
  rw [e0, e1]
  rfl

/-- a string of ZXE's protocol as a string of the skeleton's: the same fields -/
def toPS (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) : OneProtocolProof 256 (PSXE D dec).up :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path, π.rsalt⟩

/-- and back -/
def ofPS (π : OneProtocolProof 256 (PSXE D dec).up) : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec)) :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path, π.rsalt⟩

theorem ofPS_toPS (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) :
    ofPS D dec (toPS D dec π) = π := rfl
theorem toPS_ofPS (π : OneProtocolProof 256 (PSXE D dec).up) : toPS D dec (ofPS D dec π) = π := rfl

variable {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (early : X → X)
  (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX)) (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- how a plain part of the skeleton's marking is written into a query of the interface -/
def embPXE : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
    PlainPart (shapeOf (LXE (Bd := Bd) D early T) .link) (annOf (LXE (Bd := Bd) D early T) .link) :=
  pbTo (_root_.Run.Twin.allLo_eq (SOf D.C D.ds))

/-- ZXE's lax verifier is the lax verifier at the skeleton. -/
theorem ZXE_verifier (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) :
    (ZXE D dec B E early T wT eT pT).verifier cms x π =
      verifyB (L := LXE (Bd := Bd) D early T) .link (PSXE D dec).up (wqXE D dec) E.emb
          (embPXE D early T) some B.embE 0
        cms x (toPS D dec π) := by
  have h := verifyB_ann (L := LXE (Bd := Bd) D early T) .link (LinkX D dec)
      (_root_.Run.Twin.allLo (SOf D.C D.ds))
    (RoundSplits.allLocal _) (_root_.Run.Twin.allLo_eq (SOf D.C D.ds)) (wqXE D dec) E.emb
        (embPXE D early T) id (fun _ => rfl)
    some B.embE 0 cms x (toPS D dec π)
  rw [h]
  unfold WrittenE.verifier
  show verifyB (L := LXE (Bd := Bd) D early T) (K := D.K + 1) .link
      (BatchInteractiveOracleProof.ofProto (LinkX D dec)) (wqLX D dec) E.emb id
    some B.embE 0 cms x π = _
  rw [wqLX_eq]
  rfl

/-- The judge's second half as an evaluable term. -/
theorem ZXE_run (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early T)))
    (idx : (twoExternalStrings (2 ^ D.a) SgX).Pos → ℕ) (hi : Function.Injective idx)
        (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) :
    ((ZXE D dec B E early T wT eT pT).verifier cms x π).det F =
      verifyLX (fun _ => LXE (Bd := Bd) D early T) F (maskOf idx) (maskBit idx) early none .link
          (PSXE D dec) (wqXE D dec)
        E.emb (embPXE D early T) some B.embE 0 cms x (toPS D dec π) := by
  rw [ZXE_verifier]
  exact (lax_ext (LXE (Bd := Bd) D early T) F idx hi .link (PSXE D dec) (wqXE D dec) E.emb
      (embPXE D early T) some B.embE 0
    cms x (toPS D dec π)).symm

end TypedOracleCompiler.Slice
