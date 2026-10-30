-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean: AT THE ENTRY's TYPED STRING (Slice/EntryTyping.lean: assembleS)
THE LAX VERIFIER's CLAUSES ON THE CHECKS OF OPENINGS: "walks", "formed", "few": FROM FACTS ON EACH
OPENING OF THE FILE, THE ROW LAWS, THE WIRING's LAWS AND "THE RUN's RECORD OF ROOTS IS THE ROOTS
SENT". The entry's like of Slice/Batch3SWholeF.lean, at the skeleton PSXE D dec
(Slice/EntryPS.lean).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Of the record LaxYes (written in a file of this project that is not in this library; its
clauses stand one by one in OnBytes/TypedOracleCompiler/Run/LaxYes.lean, `verifyB_yes`) the fields own, ext, few,
formed, walks are wanted at one chain.
  OwnOkE g vert e1 run Fm Rt op   AN OPENING OF A TREE OF THE CHAIN's OWN; the typing's table is
    keyed by the form's own number, so each clause is asked at every (n, s) with "tree n has the
    form s" (Fm n s) and s.tree = op.sh.tree: (depth) s.a = op.sh.a; (root) the record's root for
    tree n is the root in which the opening's walk ended; (rows) each listed place Climbs, with the
    digest that g gives at the typed leaf ⟨e1 s x sym, run then the file's salt⟩
  StoOkE g vert embE a cfg cms D op   an opening of a stored table: depth a; the outer root of
    ITS table (whichOf D op) is the root in which its walk ended; each listed place Climbs, with the
    digest that g gives at ⟨embE (place, column), cfg then salt⟩
  lookGood_E, extE_yes          Batch3SWhole's one hypothesis LookGood for lookE; checksExt_all's
    hypothesis for extE at the wire weX a
  assembleS_walks           NodeLaw; all own openings OwnOkE; all stored ones StoOkE; the bodies
    are a per-tree way lifted (hemb); FormsOn; RtsL ⇒ whatever checksB | checksExt make of the
    string at wqXE: (runChecks (a ++ b)).det g = true ∧ all runCheckF ∧ all well formed
  ownOkE_of_read, stoOkE_of_read    the two records from "the format's reader of an opening said
    yes" (ReadAs: OwnRead | StoredReadAt of OnBytes/Tie/TraceStrict.lean), WITH THE LEAF LAWS ASKED
    ONLY WHERE A PAGE CAN HAVE THEM: own: at D's form, place and column bounded by type, salt.size =
    sB; stored: x < 2 ^ depth, col.length = W, salt.size = sB
  wqXE_okg                      the skeleton's wiring is lawful, under the sibling's two conditions
    on a description (as wq0_okg, Slice/EntryX.lean)
  entry_few, entry_formed   "few" and "formed" whole, from wqXE_okg (Run/LaxYes.lean)
WHAT IS NOT SAID. "own" | "ext" (= some: every read position has an opening): Slice/EntryOpened.lean
is to say it. The chain; "alone"; "accept". Any row law at a family. RtsL at the chain's record.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.TypedOracleCompiler.Run.LaxYes

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf wX)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom rootsB)

section
variable {I X' : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X'} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L))
  (vert : ByteArray → ByteArray → ByteArray)

/-- An opening of a tree of the chain's own. -/
structure OwnOkE (e1 : Enc1 (Body L)) (run : ByteArray) (Fm : ℕ → _root_.Fmt.Shape → Prop)
    (Rt : ℕ → Dig 256 → Prop)
    (op : OpAt) : Prop where
  depth : ∀ n s, Fm n s → s.tree = op.sh.tree → s.a = op.sh.a
  root : ∀ n s c, Fm n s → s.tree = op.sh.tree → Rt n c → c = bytesToDig op.out.root
  rows : ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts), ∃ lf, Climbs vert op z.1 lf ∧
    ∀ (n : ℕ) (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64), Fm n s →
        s.tree = op.sh.tree →
      x.val = z.1 → List.ofFn sym = z.2.1 →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 s x sym, leafSalt run z.2.2⟩ : LeafIn L) : Dig 256)
          = bytesToDig lf

/-- An opening of a stored table. -/
structure StoOkE (embE : SgX → Body L) (a : ℕ) (cfg : ByteArray) (cms : List (Dig 256)) (D : XD)
    (op : OpAt) : Prop where
  depth : op.sh.a = a
  root : cms.getD (whichOf D op) default = bytesToDig op.out.root
  rows : ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts), ∃ lf, Climbs vert op z.1 lf ∧
    (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨embE (z.1, z.2.1), leafSalt cfg z.2.2⟩ : LeafIn L) :
        Dig 256) =
      bytesToDig lf

variable {g vert}

theorem lookGood_E (N : NodeLaw g vert) {e1 : Enc1 (Body L)} {run : ByteArray}
    {Fm : ℕ → _root_.Fmt.Shape → Prop}
    {Rt : ℕ → Dig 256 → Prop} {ops : List OpAt} (hO : ∀ op ∈ ops, OwnOkE g vert e1 run Fm Rt op)
    {tab : List ((ℕ × ℕ) × Row)} (ht : tabOf (fun op => op.sh.tree) ops = some tab) :
    LookGood (Yes g) e1 Fm Rt (lookE run tab) := fun n s x o c hF hR hl => by
  obtain ⟨col, salt, hlk, hcol, hsalt⟩ := lookF_some (runOf := fun _ => run) (n := s.tree) hl
  obtain ⟨op, hop, hn, hz, hpath⟩ := tabOf_lookup ht hlk
  obtain ⟨lf, hc, hleaf⟩ := (hO op hop).rows _ hz
  have R := hc.row hpath
  rw [← (hO op hop).depth n s hF hn.symm] at R
  rw [(hO op hop).root n s c hF hn.symm hR, hsalt]
  exact runCheck_row N R _ (hleaf n s x o.sym hF hn.symm rfl hcol)

theorem extE_yes (N : NodeLaw g vert) {embE : SgX → Body L} {a : ℕ} {cfg : ByteArray}
    {cms : List (Dig 256)} {D : XD}
    {ops : List OpAt} (hO : ∀ op ∈ ops, StoOkE g vert embE a cfg cms D op)
        {tx : List ((ℕ × ℕ) × Row)}
    (ht : tabOf (whichOf D) ops = some tx) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) (o : Opening 256 SgX)
    (ho : extE a cfg tx p = some o) :
    Yes g (⟨⟨embE o.sym, o.salt⟩, (weX a).leaf p, o.path, cms.getD ((weX a).which p) default,
        (weX a).depth⟩ :
      Check 256 L) := by
  obtain ⟨op, hop, z, hz, hn, hq, hs, hsalt, hpath⟩ := extE_some ht ho
  obtain ⟨lf, hc, hleaf⟩ := (hO op hop).rows z hz
  have R := hc.row hpath
  rw [(hO op hop).depth] at R
  have hw : (weX a).which p = whichOf D op := by rw [hn]; cases p <;> rfl
  have hl : (weX a).leaf p = z.1 := by rw [hq]; cases p <;> rfl
  rw [hw, hl, (hO op hop).root, hs, hsalt]
  exact runCheck_row N R _ hleaf

end

/-! ## The two records from the reader's yes -/

section
variable {I X' : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X'} {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)}
  {h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray}

theorem ownOkE_of_read (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg run : ByteArray}
    {e1 : Enc1 (Body L)} {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop}
        {op : OpAt} (sB : ℕ)
    (R : ReadAs h cfg run op) (hform : ∀ n s, Fm n s → s.tree = op.sh.tree → s = op.sh)
    (hroot : ∀ n s c, Fm n s → s.tree = op.sh.tree → Rt n c → c = bytesToDig op.out.root)
    (hsalt : ∀ sl ∈ op.out.salts, sl.size = sB)
    (hleaf : ∀ (x : Fin (2 ^ op.sh.a)) (sym : Fin op.sh.W → UInt64) (salt : ByteArray),
        salt.size = sB →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 op.sh x sym, leafSalt run salt⟩ : LeafIn L) :
          Dig 256) =
        bytesToDig (leafAtH h op.sh run x.val (List.ofFn sym) salt)) :
    OwnOkE g (fun l r => h 166 0 0 cfg (l ++ r)) e1 run Fm Rt op :=
  ⟨fun n s hF ht => by rw [hform n s hF ht], hroot, fun z hzm =>
    ⟨_, climbs_of_read hz R z hzm, fun n s x sym hF ht hx hs => by
      obtain rfl := hform n s hF ht
      rw [hleaf x sym z.2.2 (hsalt _ (List.of_mem_zip (List.of_mem_zip hzm).2).2), hx, hs]⟩⟩

theorem stoOkE_of_read (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n)
    {cfg : ByteArray}
    {embE : SgX → Body L} {a : ℕ} {cms : List (Dig 256)} {D : XD} {op : OpAt} (sB : ℕ)
        (R : ReadAs h cfg cfg op)
    (hd : op.sh.a = a) (hr : cms.getD (whichOf D op) default = bytesToDig op.out.root)
    (hcol : ∀ c ∈ op.out.cols, c.length = op.sh.W) (hsalt : ∀ sl ∈ op.out.salts, sl.size = sB)
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), x < 2 ^ op.sh.a →
        col.length = op.sh.W → salt.size = sB →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨embE (x, col), leafSalt cfg salt⟩ : LeafIn L) :
          Dig 256) =
        bytesToDig (leafAtH h op.sh cfg x col salt)) :
    StoOkE g (fun l r => h 166 0 0 cfg (l ++ r)) embE a cfg cms D op :=
  ⟨hd, hr, fun z hzm =>
    have hc := climbs_of_read hz R z hzm
    ⟨_, hc, hleaf z.1 z.2.1 z.2.2 hc.1 (hcol _ (List.of_mem_zip (List.of_mem_zip hzm).2).1)
      (hsalt _ (List.of_mem_zip (List.of_mem_zip hzm).2).2)⟩⟩

end

/-! ## At the skeleton's wiring -/

section
variable {X : Type} (D : XD) (dec : X → View → Bool) {I X' : Type} {L : BatchProtocolWithLeafBody I X'}
  {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) L)}
      {vert : ByteArray → ByteArray → ByteArray}

/-- "walks", and the first half of "formed". -/
theorem assembleS_walks (N : NodeLaw g vert) {o : _root_.Fmt.ChainOut}
    {π : OneProtocolProof 256 (PSXE D dec).up}
    (hπ : assembleS D dec o = some π) {e1 : Enc1 (Body L)}
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
        OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (hemb : ∀ q a, embS (.inr q) a = embLS D.C (liftT e1) D.ds q a)
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} (hF : FormsOn Fm 0 D.ds)
    (hOwn : ∀ run, o.run = some run → ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
        OwnOkE g vert e1 run Fm Rt op)
    {embE : SgX → Body L} {cms : List (Dig 256)}
    (hSto : ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
        StoOkE g vert embE D.a D.base.cfg cms D op)
    (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds))) (hR : RtsL Rt D.C 0 D.ds rts.2)
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
        (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (a b : List (Check 256 L))
    (ha : checksB (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
        (wqXE D dec).sh embS rts isRead
      π.opens = some a)
    (hb : TypedOracleCompiler.Compile.Batch.checksExt (wqXE D dec).ext embE cms isReadE π.ext
        (wqXE D dec).ext.all = some b) :
    (runChecks (K := D.K + 1) (a ++ b)).det g = true ∧ (a ++ b).all (runCheckF g) = true ∧
      (a ++ b).all (fun c => c.wellFormed) = true := by
  obtain ⟨run, pl, tab, tx, h1, -, e3, e4, -, -, -, hop, hext, -⟩ := assembleS_some D dec hπ
  have H := lookGood_E N (hOwn run h1) e3
  have e5 : (fun q => embS (.inr q)) = embLS D.C (liftT e1) D.ds := funext fun q =>
      funext fun a => hemb q a
  have e6 : (fun q => π.opens (.inr q)) = opLS D.C (lookE run tab) 0 D.ds := funext hop
  have G : GoodAt (Yes g) (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds))
      (wqXE D dec).sh embS rts
      isRead π.opens := by
    refine ⟨comp_none _ _ _ _ _, comp_none _ _ _ _ _, ?_⟩
    show GoodAt (Yes g) (PQ.uL D.C D.ds) (_root_.Run.Twin.allLo (PQ.SL D.C D.ds))
      (PQ.wiresSL D.C D.K (_root_.Run.chalP D.base.plan.field D.K) D.ds)
          (fun q => embS (.inr q)) rts.2
      (fun q => isRead (.inr q)) (fun q => π.opens (.inr q))
    rw [e5, e6]
    exact goodAt_L H D.C D.K (_root_.Run.chalP D.base.plan.field D.K) D.ds 0 rts.2 _ hF hR
  rw [hext] at hb
  have Y := checks_yes g _ _ (wqXE D dec).sh embS rts isRead π.opens (wqXE D dec).ext embE
      cms isReadE _ G
    (fun p op _ ho => extE_yes N hSto e4 p op ho) a b ha hb
  exact ⟨Y.1, by rw [← runChecks_detF]; exact Y.1, Y.2⟩

/-- The skeleton's wiring is lawful. -/
theorem wqXE_okg (hwork : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true) :
    (wqXE D dec).OKG :=
  have h : (wX D fun _ => true).OKG :=
    TypedOracleCompiler.Run.PQ.wqX_okg D.C D.K (_root_.Run.chalP D.base.plan.field D.K) D.ds D.a D.xs
        (fun _ => true) (fun _ => true)
      (TypedOracleCompiler.Run.PQ.okX_own D.ds D.a D.xs hokx)
      (TypedOracleCompiler.Run.planPull_okg D.base.plan.field D.K D.ds (fun _ => true)
        (TypedOracleCompiler.Run.PQ.blocks_le_kOf D.base) hwork)
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

theorem wqXE_depth : (wqXE D dec).ext.depth ≤ (wqXE D dec).maxDepth :=
  le_max_right (TypedOracleCompiler.Run.PQ.maxDepth D.ds) D.a

/-- "few". -/
theorem entry_few (hwork : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
        OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (embE : SgX → Body L) (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (a b : List (Check 256 L))
    (own : (haveI := (wqXE D dec).decO; checksB (PSXE D dec).up.loc.shape (PSXE D dec).up.ann
        (wqXE D dec).sh embS rts
      (fun p => decide (p ∈ (PSXE D dec).up.loc.reads x ρ
        (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))) π.opens) = some a)
    (ext : (haveI := (wqXE D dec).ext.dec; TypedOracleCompiler.Compile.Batch.checksExt
        (wqXE D dec).ext embE cms
      (fun p => decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)) π.ext (wqXE D dec).ext.all) = some b)
          :
    (a ++ b).length ≤ (wqXE D dec).nOpen :=
  few_of_okg (PSXE D dec).up (wqXE D dec) (wqXE_okg D dec hwork hokx) embS embE cms x π ρ
      rts a b own ext

/-- "formed", whole. -/
theorem entry_formed (hwork : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (hokx : TypedOracleCompiler.Run.PQ.okX D.ds D.a D.xs = true)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
        OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
    (embE : SgX → Body L) (cms : List (Dig 256)) (rts : RootsOfChain 256 (_root_.Run.Twin.up (SOf D.C D.ds)))
    (isRead : OPos (_root_.Run.Twin.up (SOf D.C D.ds)) → Bool)
        (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (π : OneProtocolProof 256 (PSXE D dec).up) (a b : List (Check 256 L))
    (own : checksB (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh embS rts isRead
        π.opens = some a)
    (ext : TypedOracleCompiler.Compile.Batch.checksExt (wqXE D dec).ext embE cms isReadE π.ext
        (wqXE D dec).ext.all = some b)
    (wf : (a ++ b).all (fun c => c.wellFormed) = true) :
    (a ++ b).all (fun c => c.wellFormed && decide (c.depth ≤ (wqXE D dec).maxDepth)) = true :=
  formed_of_okg (PSXE D dec).up (wqXE D dec) (wqXE_okg D dec hwork hokx) (wqXE_depth D dec) embS
      embE cms rts isRead isReadE π
    a b own ext wf

end

end TypedOracleCompiler.Slice
