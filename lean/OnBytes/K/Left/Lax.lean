-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Lax.lean: what is enough so that the lax verifier of an entry file's link says yes on
the typed string that the typing makes of what the strict reader read, as one record of nine fields;
and the join. General in the description.

Why. The entry file's verifier on plain data (`verifyE`, OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean) asks,
among other things, that the evaluable lax verifier `laxE` (OnBytes/TypedOracleCompiler/Slice/EntryRun.lean) says
yes. To tie a yes of the program on bytes to that, the lax verifier's clauses are shown one by one,
in the order of its text. The tools lie in OnBytes/TypedOracleCompiler/: the chain (Slice/EntryChain.lean), that
every read position has an opening (Slice/EntryOpened.lean), number, form and walks of the checks
(Slice/EntryWhole.lean), the clauses together (Run/LaxYes.lean). This file names what they ask at
one reading, and joins them.

Main names:
  `ownOps o`, `stoOps o`: the openings of the chain's own trees, and of the two stored tables, in
    what was read.
  `LaxDebts D hok d₁ F dec c₀ c₁ x o π ρ v`: the record: the typing; the chain; two conditions on
    the description; three fields on which positions are read; the walks; the decision.
  `lax_of_debts`: then `laxE` says yes under the family F.

Not claimed. That the record is met by any reading: each field is a debt, paid in the other files of
this folder. An implication between two yeses, at one family of oracle functions: nothing on
soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryChain
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.RowsE2
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf wX bodyS RowsT RowsL)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

variable {lg s : ℕ} (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (d₁ : Sd1 lg s)
  (F : Fam (typedOracleFamily 256 (D.K + 1) (Ls D d₁))) (dec : XE (List T3) lg s → View → Bool)

/-- The openings of the chain's own trees in what was read. -/
def ownOps (o : _root_.Fmt.ChainOut) : List OpAt := (opsOf 1 o).filter fun op => !op.sh.stored

/-- The openings of the two stored tables in what was read. -/
def stoOps (o : _root_.Fmt.ChainOut) : List OpAt := (opsOf 1 o).filter fun op => op.sh.stored

/-- What is owed so that the lax verifier says yes, under a family F, on the typed string π that
the typing makes of what was read (o), at two outer roots and an instance x. ρ, v: what the chain
draws, and its last value. All fields speak at the same x, ρ and F. At the use
(OnBytes/K/Left/LaxAt.lean) x holds both tables' answers and the seeds of what the converter hands
over, F is the family that a run evaluates, and ρ draws what the reader drew and passes all tests of
work: two facts that stand in no field, and that whoever shows `rows`, `listed` or `accept` needs.
-/
structure LaxDebts (c₀ c₁ : Dig 256) (x : XE (List T3) lg s) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (PSXE D dec).up) (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits) :
    Prop where
  /-- the typing's yes -/
  str : assembleS D dec o = some π
  /-- The chain -/
  chain : (recomputeChainOfProof (L := Ls D d₁) .link (PSXE D dec).up (wqXE D dec)
      (embPXE D (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))) some [c₀, c₁] x
      π).det F =
    some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList), Phase.loc v)
  /-- of the description: no round has more than 64 bits of work -/
  work : ∀ r ∈ D.ds, r.entry.work ≤ 64
  /-- of the description: the stored openings are in order -/
  okx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true
  /-- Own: round by round, tree by tree: "read" means "listed in the file's opening" -/
  rows : ∃ sb, RowsL D.C (tblOf (ownOps o)) sb D.ds o.rounds.toList fun q =>
    (haveI := (wqXE D dec).decO
     decide (Sum.inr q ∈ (PSXE D dec).up.loc.reads x ρ
      (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains)))
  /-- Own: the columns have their forms' widths -/
  cols : ColsFit (ownOps o)
  /-- Ext: a position that is read in a stored table is listed in a stored opening of that table -/
  listed : ListedX D D.a (stoOps o) fun p =>
    (haveI := (wqXE D dec).ext.dec
     decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))
  /-- Walks: every opening's walk, at F -/
  walks : ∃ (vert : ByteArray → ByteArray → ByteArray) (e1 : Enc1 (Body (Ls D d₁)))
      (Fm : ℕ → _root_.Fmt.Shape → Prop) (Rt : ℕ → Dig 256 → Prop),
    NodeLaw F vert ∧ (∀ q a, (ownES D hok).emb (.inr q) a = embLS D.C (liftT e1) D.ds q a) ∧
    FormsOn Fm 0 D.ds ∧
    (∀ run, o.run = some run → ∀ op ∈ ownOps o, OwnOkE F vert e1 run Fm Rt op) ∧
    (∀ op ∈ stoOps o,
      StoOkE F vert (bodyS D.a D.base.plan.salt).embE D.a D.base.cfg [c₀, c₁] D op) ∧
    RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList)
  /-- The decision -/
  accept : (PSXE D dec).up.loc.accept x
      ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
        ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains ρ π.opens) = true

/-- Then the lax verifier says yes. -/
theorem lax_of_debts (c₀ c₁ : Dig 256) (x : XE (List T3) lg s) (o : _root_.Fmt.ChainOut)
    (π : OneProtocolProof 256 (PSXE D dec).up) (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits)
    (h : LaxDebts D hok d₁ F dec c₀ c₁ x o π ρ v) :
    laxE D dec (bodyS D.a D.base.plan.salt) (ownES D hok)
      (earlyTwo (A := List T3 × List T3) d₁) (fun _ => TSE D (seedEntry lg s)) F [c₀, c₁] x π =
      true := by
  obtain ⟨sb, hrows⟩ := h.rows
  obtain ⟨vert, e1, Fm, Rt, N, hemb, hF, hOwn, hSto, hR⟩ := h.walks
  obtain ⟨a, ha⟩ := assembleS_own D dec h.str (L := Ls D d₁) (ownES D hok).emb
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList)
    (fun p => (haveI := (wqXE D dec).decO
      decide (p ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
          ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) π.plains))))
    sb o.rounds.toList hrows h.cols
  obtain ⟨b, hb⟩ := assembleS_ext D dec h.str (L := Ls D d₁) (bodyS D.a D.base.plan.salt).embE
    [c₀, c₁]
    (fun p => (haveI := (wqXE D dec).ext.dec
      decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))) h.listed
  obtain ⟨-, w2, w3⟩ := assembleS_walks D dec N h.str (ownES D hok).emb hemb hF hOwn hSto
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) hR _ _ a b ha hb
  have hy := verifyB_yes F .link (PSXE D dec).up (wqXE D dec) (ownES D hok).emb
    (embPXE D (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s))) some
    (bodyS D.a D.base.plan.salt).embE 0 [c₀, c₁] x π ρ
    ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList) (Phase.loc v) a b h.chain ha hb
    (entry_few D dec h.work h.okx _ _ _ x π ρ _ a b ha hb)
    (entry_formed D dec h.work h.okx _ _ _ _ _ _ π a b ha hb w3) w2 rfl h.accept
  rw [laxE_eq D dec (bodyS D.a D.base.plan.salt) (ownES D hok)
    (earlyTwo (A := List T3 × List T3) d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
    (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _), ZXE_verifier]
  exact hy

end OnBytes.K.Left
