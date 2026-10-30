-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/SameSibK.lean: the written link over letters, with the wire record `sibW` at any
number K of blocks, has `SameRun2` with the skeleton `(PSXE D dec).up` wired with the same number of
blocks (`wqXK D dec K chal`, OnBytes/K/Arm/WireK.lean), once both instances are fixed: if the
letters but K are the description's own, by proofs.

OnBytes/K/Arm/SameSib.lean has this against the wiring `wqXE D dec`; it asks that K is the
description's own number `D.K` and that the way from blocks to verifier messages is the library's at
that number. Here K is a letter on both sides, and so is that way. The text is that file's. For
proofs only; the program does not import this file.

Main theorem.
 `sameRun_sibK`   `SameRun2` of (`sibQ`, `sibW` at K and chal2, embS2, embP2, π2) at x2 with (the
                  skeleton, `wqXK D dec K chal`, embS, embP, π) at x. Asked: the four letters C,
                  ds, a, xs are D's; the two ways from blocks to messages agree; the two decisions
                  agree at the two instances; the two pairs of maps and the nine fields of the typed
                  strings agree.

What is not claimed. That the letters at any size are a description's. Nothing on soundness.


-/
import OnBytes.K.Arm.WireK

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Carry OnBytes.Flat
open TypedOracleCompiler.Run.PQ (XD SOf wqX)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX CK XO)

variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) (K : ℕ)
  (chal2 : ∀ e k, (Fin K → Dig 256) → C.Ch e k) {Y2 : Type} (dec2 : Y2 → View → Bool)
  {I X' X : Type} {L : BatchProtocolWithLeafBody I X'}

/-- The written link over letters and the skeleton, both wired with K blocks: the lax verifier
cannot tell them apart. -/
theorem sameRun_sibK (D : XD) (dec : X → View → Bool) (x : X) (x2 : Y2) (hC : C = D.C)
    (hds : ds = D.ds) (ha : a = D.a) (hxs : xs = D.xs)
    (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k) (hchal : HEq chal2 chal)
    (hdec : dec2 x2 = dec x)
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
      (fixW (sibW C ds a xs K chal2 dec2) x2) (fixW (wqXK D dec K chal) x) embS2 embS embP2 embP
      (fixP π2 x2) (fixP π x) := by
  subst hC hds ha hxs
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
