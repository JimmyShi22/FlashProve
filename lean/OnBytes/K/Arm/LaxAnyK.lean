-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LaxAnyK.lean: what is owed so that the lax compiled verifier of an entry's link says
yes on the typed string that the typing makes of what was read, at the skeleton wired with any
number K of blocks in a verifier's message; and that it is enough.

OnBytes/K/Arm/LaxAny.lean has the record `LaxDebtsAny` and the join `lax_any` at the wiring
`wqXE D dec`, which has the description's own number `D.K` of blocks. Here both are said at
`wqXK D dec K chal` (OnBytes/K/Arm/WireK.lean) and oracle functions with K + 1 blocks, by that
file's text. One field has turned: in the place of "no round has more than 64 bits of work" stands
what it served for, "the rounds' wires obey the sibling's laws" (`wires`; `wqS_okgP` has it at the
library's way of making a message, if `D.K ≤ K` and no round has more than 64 bits of work). For
proofs only; the program does not import this file.

Main definition: `LaxDebtsAnyK`.
Main theorems.
 `lax_anyK`       then the lax verifier at the skeleton `(PSXE D dec).up`, the wiring
                  `wqXK D dec K chal` and the instance x says yes, at every depth of the request
                  tree.
 `lax_anyK_fix`   the same at the protocol with the instance fixed (OnBytes/K/FixInstance.lean).

What is not claimed. That any field holds at a file or at any oracle functions. Nothing on
soundness.


-/
import OnBytes.K.TwoCarryFix
import OnBytes.K.Arm.WireK

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf RowsL)
open _root_.Run.PQ (View SgX)
open OnBytes.K (fixB fixW fixP)

variable {I X' X : Type} {L : BatchProtocolWithLeafBody I X'} (D : XD) (dec : X → View → Bool) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k) (g : Fam (typedOracleFamily 256 (K + 1) L))
  (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
    OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
  (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option X') (embE : SgX → Body L) (cms : List (Dig 256))

/-- What is owed so that the lax verifier says yes, over the carrier L, under oracle functions
g, on the typed string π that the typing makes of what was read (o), at the list cms of outer roots
and an instance x. ρ, v: what the chain draws, and its last value. -/
structure LaxDebtsAnyK (x : X) (o : _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (PSXE D dec).up)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits) : Prop where
  /-- the typing's yes -/
  str : assembleS D dec o = some π
  /-- the chain, over L, at g -/
  chain : (recomputeChainOfProof (L := L) .link (PSXE D dec).up (wqXK D dec K chal) embP xin cms x π).det g =
    some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList), Phase.loc v)
  /-- of the wiring: the rounds' wires obey the sibling's laws -/
  wires : (PQ.wqS D.C K chal D.ds fun _ => true).OKG
  /-- of the description: the stored openings are in order -/
  okx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true
  /-- OWN: round by round, tree by tree: "read" means "listed in the file's opening" -/
  rows : ∃ sb, RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) sb D.ds
    o.rounds.toList fun q =>
      (haveI := (wqXK D dec K chal).decO
       decide (Sum.inr q ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
          ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains)))
  /-- OWN: the columns have their forms' widths -/
  cols : ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored)
  /-- EXT: a position that is read in a stored table is listed in a stored opening of that table -/
  listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
    (haveI := (wqXK D dec K chal).ext.dec
     decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))
  /-- WALKS: every opening's walk, over L, at g (OnBytes/TypedOracleCompiler/Slice/ArmWalks.lean) -/
  walks : ArmWalks.Walks D g embS embE cms o
  /-- the decision -/
  accept : (PSXE D dec).up.loc.accept x
      ((wqXK D dec K chal).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXK D dec K chal).sh
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true

variable {D dec K chal g embS embP xin embE cms}

/-- Then the lax verifier says yes, at every depth of the request tree. -/
theorem lax_anyK {x : X} {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAnyK D dec K chal g embS embP xin embE cms x o π ρ v) (depthReq : ℕ) :
    (verifyB (L := L) .link (PSXE D dec).up (wqXK D dec K chal) embS embP xin embE depthReq cms x
      π).det g = true := by
  obtain ⟨sb, hrows⟩ := h.rows
  obtain ⟨a, ha⟩ := assembleS_ownK D dec K chal h.str (L := L) embS
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList)
    (fun p => (haveI := (wqXK D dec K chal).decO
      decide (p ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
          ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains))))
    sb o.rounds.toList hrows h.cols
  obtain ⟨b, hb⟩ := assembleS_extK D dec K chal h.str (L := L) embE cms _ h.listed
  obtain ⟨-, w2, w3⟩ := walks_runK D dec K chal h.walks h.str _ _ a b ha hb
  exact verifyB_yes g .link (PSXE D dec).up (wqXK D dec K chal) embS embP xin embE depthReq cms x π
    ρ ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) (Phase.loc v) a b h.chain ha hb
    (entry_fewK D dec K chal h.wires h.okx _ _ _ x π ρ _ a b ha hb)
    (entry_formedK D dec K chal h.wires h.okx _ _ _ _ _ _ π a b ha hb w3) w2 rfl h.accept

/-- The same at the protocol with the instance fixed. -/
theorem lax_anyK_fix {x : X} {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAnyK D dec K chal g embS embP xin embE cms x o π ρ v) (depthReq : ℕ) :
    (verifyB (L := L) .link (fixB (PSXE D dec).up x) (fixW (wqXK D dec K chal) x) embS embP
      (fun _ => xin x) embE depthReq cms () (fixP π x)).det g = true :=
  (congrArg (fun A => OComp.det g A)
    (TypedOracleCompiler.Compile.Batch.Carry.verifyB_fix (L := L) .link (PSXE D dec).up
      (wqXK D dec K chal) embS embP xin embE depthReq cms x π)).trans (lax_anyK h depthReq)

end OnBytes.K.Arm
