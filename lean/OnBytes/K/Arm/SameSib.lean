-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/SameSib.lean: the written link over letters (`linkProtocolOfRoundData`, OnBytes/Flat/LinkSib.lean), with
the wire record that has the five fields of `wqX` (OnBytes/TypedOracleCompiler/Run/PlanQX.lean) at the same letters,
has `SameRun2` (OnBytes/K/TwoCarrySame2.lean) with the skeleton `(PSXE D dec).up` and its wiring
`wqXE D dec`, once both instances are fixed: if the letters are the description's own, by proofs.

The letters: a kit C, rounds' data ds, a depth a, stored openings xs, a number K of blocks with its
way chal from blocks to verifier messages. An object with records for the entry's arm has `linkProtocolOfRoundData` at
letters as its Link. At the sizes in use the letters are equal to those of the description by
theorems, not by unfolding. For proofs only; the program does not import this file.

Main definitions: `sibQ`, `sibW`.
Main theorem.
 `sameRun_sib`    `SameRun2` of (`sibQ`, `sibW`, embS2, embP2, π2) at x2 with (the skeleton, its
                  wiring, embS, embP, π) at x. Asked: the six letters are D's; the two decisions
                  agree at the two instances; the two pairs of maps and the nine fields of the typed
                  strings agree. So of the twenty fields of `SameRun2` the five on the protocol and
                  the four on the wiring are shown here; the two on the maps and the nine on the
                  string are premises.

What is not claimed. That the letters at any size are a description's. Nothing on soundness.


-/
import OnBytes.K.TwoCarrySame2
import OnBytes.K.FixInstance
import OnBytes.Flat.LinkSib

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Carry OnBytes.Flat
open TypedOracleCompiler.Run.PQ (XD SOf wqX)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (chalP)
open _root_.Run.PQ (View SgX CK XO)

variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) {Y2 : Type} (dec2 : Y2 → View → Bool)

/-- The written link over letters, every round marked local. -/
abbrev sibQ : BatchInteractiveOracleProof Y2 (twoExternalStrings (2 ^ a) SgX) :=
  ⟨linkProtocolOfRoundData C ds a xs dec2, _root_.Run.Twin.allLo (SOf C ds)⟩

/-- Its wire record: the five fields of `wqX` at the same letters. -/
def sibW : ProtocolQueryLayout 256 (K + 1) (sibQ C ds a xs dec2) :=
  ⟨(wqX C K chal ds a xs fun _ => true).sh, (wqX C K chal ds a xs fun _ => true).ext,
    (wqX C K chal ds a xs fun _ => true).decO, (wqX C K chal ds a xs fun _ => true).nOpen,
    (wqX C K chal ds a xs fun _ => true).maxDepth⟩

variable {I X' X : Type} {L : BatchProtocolWithLeafBody I X'}

/-- **The written link over letters and the skeleton: the lax verifier cannot tell them apart.** -/
theorem sameRun_sib (D : XD) (dec : X → View → Bool) (x : X) (x2 : Y2) (hC : C = D.C)
    (hds : ds = D.ds) (ha : a = D.a) (hxs : xs = D.xs) (hK : K = D.K)
    (hchal : HEq chal (chalP D.base.plan.field D.K)) (hdec : dec2 x2 = dec x)
    (embS2 : (p : OPos (_root_.Run.Twin.up (SOf C ds))) →
      OSym (_root_.Run.Twin.up (SOf C ds)) p → Body L)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L) (hS : HEq embS2 embS)
    (embP2 : PlainPart (_root_.Run.Twin.up (SOf C ds)) (_root_.Run.Twin.allLo (SOf C ds)) →
      PlainPart (shapeOf L .link) (annOf L .link))
    (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
      PlainPart (shapeOf L .link) (annOf L .link)) (hP : HEq embP2 embP)
    (π2 : OneProtocolProof 256 (sibQ C ds a xs dec2)) (π : OneProtocolProof 256 (PSXE D dec).up)
    (h1 : π2.salt = π.salt) (h2 : π2.roots = π.roots) (h3 : HEq π2.plains π.plains)
    (h4 : HEq π2.opens π.opens) (h5 : HEq π2.ext π.ext) (h6 : π2.rtreq = π.rtreq)
    (h7 : π2.slot = π.slot) (h8 : π2.path = π.path) (h9 : π2.rsalt = π.rsalt) :
    SameRun2 (L := L) (t := .link) (fixB (sibQ C ds a xs dec2) x2) (fixB (PSXE D dec).up x)
      (fixW (sibW C ds a xs K chal dec2) x2) (fixW (wqXE D dec) x) embS2 embS embP2 embP
      (fixP π2 x2) (fixP π x) := by
  subst hC hds ha hxs hK
  obtain rfl := eq_of_heq hchal
  exact
    { shape := rfl
      ann := HEq.rfl
      extReads := HEq.rfl
      reads := HEq.rfl
      accept := by
        show HEq (fun _ : Unit => (linkProtocolOfRoundData D.C D.ds D.a D.xs dec2).accept x2)
          (fun _ : Unit => (PSXE D dec).up.loc.accept x)
        have e : (linkProtocolOfRoundData D.C D.ds D.a D.xs dec2).accept x2 = (PSXE D dec).up.loc.accept x := by
          show (fun y τ => (PQ.skeletonOverBothExternalStrings D.C D.ds D.a D.xs (dec2 x2)).up.loc.accept () y τ) =
            fun y τ => (PQ.skeletonOverBothExternalStrings D.C D.ds D.a D.xs (dec x)).up.loc.accept () y τ
          rw [hdec]
        rw [e]
      sh := HEq.rfl
      ext := HEq.rfl
      nOpen := rfl
      maxDepth := rfl
      embS := hS
      embP := hP
      salt := h1
      roots := h2
      plains := h3
      opens := h4
      pext := h5
      rtreq := h6
      slot := h7
      path := h8
      rsalt := h9 }

end OnBytes.K.Arm
