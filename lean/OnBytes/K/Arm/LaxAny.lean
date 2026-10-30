-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LaxAny.lean: what is owed so that the lax compiled verifier of an entry's link says
yes on the typed string that the typing makes of what was read, over any carrier, at any oracle
functions, any list of outer roots and whatever the chain is handed in the field x; and that it is
enough.

OnBytes/K/Left/Lax.lean has the record `LaxDebts` at one carrier (`Ls D d₁`), with the answers in
the field x of the first query and the two roots as the list. The lemmas that it joins
(OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean, EntryWhole.lean; OnBytes/TypedOracleCompiler/Run/LaxYes.lean) are general in
the carrier. Here the record and the join are said with the carrier L, the oracle functions g, the
maps embS, embP, embE, xin and the list cms as letters. Seven of the nine fields do not name them:
`str`, `work`, `okx`, `rows`, `cols`, `listed`, `accept`. They are written after those of
`LaxDebts`, with its `ownOps o` and `stoOps o` written out; this file does not import that one, and
no lemma says that they are the same. Two fields name the letters: `chain` and `walks`. For proofs
only; the program does not import this file.

Main definition: `LaxDebtsAny`.
Main theorems.
 `lax_any`        then the lax verifier at the skeleton `(PSXE D dec).up`, the wiring `wqXE D dec`
                  and the instance x says yes, at every depth of the request tree.
 `lax_any_fix`    the same at the protocol with the instance fixed (OnBytes/K/FixInstance.lean).

What is not claimed. That any field holds at a file or at any oracle functions. Nothing on
soundness.


-/
import OnBytes.K.TwoCarryFix
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.TypedOracleCompiler.Slice.ArmWalks

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf RowsL)
open _root_.Run.PQ (View SgX)
open OnBytes.K (fixB fixW fixP)

variable {I X' X : Type} {L : BatchProtocolWithLeafBody I X'} (D : XD) (dec : X → View → Bool)
  (g : Fam (typedOracleFamily 256 (D.K + 1) L))
  (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
    OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
  (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option X') (embE : SgX → Body L) (cms : List (Dig 256))

/-- **What is owed so that the lax verifier says yes**, over the carrier L, under oracle functions
g, on the typed string π that the typing makes of what was read (o), at the list cms of outer roots
and an instance x. ρ, v: what the chain draws, and its last value. -/
structure LaxDebtsAny (x : X) (o : _root_.Fmt.ChainOut) (π : OneProtocolProof 256 (PSXE D dec).up)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits) : Prop where
  /-- the typing's yes -/
  str : assembleS D dec o = some π
  /-- THE CHAIN, over L, at g -/
  chain : (recomputeChainOfProof (L := L) .link (PSXE D dec).up (wqXE D dec) embP xin cms x π).det g =
    some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList), Phase.loc v)
  /-- of the description: no round has more than 64 bits of work -/
  work : ∀ r ∈ D.ds, r.entry.work ≤ 64
  /-- of the description: the stored openings are in order -/
  okx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true
  /-- OWN: round by round, tree by tree: "read" means "listed in the file's opening" -/
  rows : ∃ sb, RowsL D.C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored)) sb D.ds
    o.rounds.toList fun q =>
      (haveI := (wqXE D dec).decO
       decide (Sum.inr q ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
          ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains)))
  /-- OWN: the columns have their forms' widths -/
  cols : ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored)
  /-- EXT: a position that is read in a stored table is listed in a stored opening of that table -/
  listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
    (haveI := (wqXE D dec).ext.dec
     decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))
  /-- WALKS: every opening's walk, over L, at g (OnBytes/TypedOracleCompiler/Slice/ArmWalks.lean) -/
  walks : ArmWalks.Walks D g embS embE cms o
  /-- THE DECISION -/
  accept : (PSXE D dec).up.loc.accept x
      ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true

variable {D dec g embS embP xin embE cms}

/-- **THEN THE LAX VERIFIER SAYS YES**, at every depth of the request tree. -/
theorem lax_any {x : X} {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAny D dec g embS embP xin embE cms x o π ρ v) (depthReq : ℕ) :
    (verifyB (L := L) .link (PSXE D dec).up (wqXE D dec) embS embP xin embE depthReq cms x π).det
      g = true := by
  obtain ⟨sb, hrows⟩ := h.rows
  obtain ⟨a, ha⟩ := assembleS_own D dec h.str (L := L) embS
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList)
    (fun p => (haveI := (wqXE D dec).decO
      decide (p ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
          ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains))))
    sb o.rounds.toList hrows h.cols
  obtain ⟨b, hb⟩ := assembleS_ext D dec h.str (L := L) embE cms _ h.listed
  obtain ⟨-, w2, w3⟩ := h.walks.run dec h.str _ _ a b ha hb
  exact verifyB_yes g .link (PSXE D dec).up (wqXE D dec) embS embP xin embE depthReq cms x π ρ
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) (Phase.loc v) a b h.chain ha hb
    (entry_few D dec h.work h.okx _ _ _ x π ρ _ a b ha hb)
    (entry_formed D dec h.work h.okx _ _ _ _ _ _ π a b ha hb w3) w2 rfl h.accept

/-- **The same at the protocol with the instance fixed.** -/
theorem lax_any_fix {x : X} {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAny D dec g embS embP xin embE cms x o π ρ v) (depthReq : ℕ) :
    (verifyB (L := L) .link (fixB (PSXE D dec).up x) (fixW (wqXE D dec) x) embS embP
      (fun _ => xin x) embE depthReq cms () (fixP π x)).det g = true :=
  (congrArg (fun A => OComp.det g A)
    (TypedOracleCompiler.Compile.Batch.Carry.verifyB_fix (L := L) .link (PSXE D dec).up (wqXE D dec) embS
      embP xin embE depthReq cms x π)).trans (lax_any h depthReq)

end OnBytes.K.Arm
