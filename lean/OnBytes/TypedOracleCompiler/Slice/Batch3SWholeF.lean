-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SWholeF.lean: AT THE TYPING's STRING (Slice/Batch3STyping.lean: assemble3
| assembleF) THE LAX VERIFIER's CHECKS OF THE OPENINGS SAY YES UNDER g: FROM FACTS ON EACH OPENING
OF THE FILE, THE ROW LAWS, THE FRONT's CHECK AND "THE RUN's RECORD OF ROOTS IS THE ROOTS SENT".
The join of Run/WholePaths.lean, Slice/Batch3SWhole.lean and the typing.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. This file says WHAT EXACTLY IS STILL OWED for the forests' half, as two records of hypotheses,
opening by opening, and shows that no more is owed.
  Climbs vert op x lf      ONE LISTED PLACE OF AN OPENING: x < 2 ^ depth; the leaf's digest lf has
    32 bytes; and, as a third clause, THE CONCLUSION OF THE LIBRARY's opening_paths
    (Run/WalkPaths.lean) TO THE LETTER: a list p with pathFrom op.sh.a op.out.seen x = some (p as
    digests), of the tree's depth, of 32 bytes each, octF vert depth [x] [lf] p = [op.out.root]
  OwnOk g vert e1 D num runOf Rt op   AN OPENING OF A TREE OF THE PROVER's: (depth) D's form of
    its tree in the whole has its depth; (root) the root that the run's record holds for that tree
    is the root in which its walk ended; (rows) each listed place Climbs, with a digest lf that g
    gives at the typed leaf: body := e1 at D's form, the place and the column as a symbol; typed
    salt := the sender's run, then the file's salt
  StoOk g vert embE a cfg cm op       an opening of the stored copy: its depth is a; its walk
    ended in the outer root cm; each listed place Climbs, with the digest that g gives at the leaf
    ⟨embE (place, column), cfg then the file's salt⟩
  lookGood_F           all own openings OwnOk, NodeLaw ⇒ Batch3SWhole's one hypothesis LookGood,
    at "says yes and is well formed", for the typing's lookF
  ext_yes              all stored openings StoOk, NodeLaw ⇒ checksExt_all's hypothesis for the
    typing's extF at the wire we1 a
  assemble3_checks     BOTH, WITH THE FRONT's CompGood AND D.RtsOk, AT π := WHAT assemble3
    GIVES: whatever checksB | checksExt make of π at D's wires: (runChecks (a ++ b)).det g = true,
    and all are well formed
WHO IS TO GIVE WHAT. Climbs: its third clause is the library's opening_paths at the twin's yes for
that opening (a theorem; it wants h's answers of the right length and given digests of 32 bytes);
its first (x < 2 ^ depth) is the reader's own test of the list (listOK), its second (32 bytes) the
library's leafV_size: neither is in opening_paths' conclusion. (depth): the port's descriptions are
D's lists. (root): the strict reader compares each walk's end with the root sent, and the chain's
half says that the run's record holds the roots sent. The digest at the leaf, and NodeLaw: the
page's row laws. The front: a file of this project that is not in this library with the hypothesis
FRONT.
WHAT IS NOT SAID. Any of these facts. That checksB | checksExt give "some" (every read position has
an opening: by the chain's half, typed draws = the reader's). afterB's other clauses. A LATER
OPENING THAT SHOWS ANOTHER COLUMN AT A PLACE is not looked at: the table's first row is typed
(ClashF's matter). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SWhole

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)
open _root_.Run (bytesToBits bytesToDig leafSalt pathFrom)

/-- one listed place of an opening: the conclusion of the library's opening_paths -/
def Climbs (vert : ByteArray → ByteArray → ByteArray) (op : OpAt) (x : ℕ) (lf : ByteArray) : Prop :=
  x < 2 ^ op.sh.a ∧ lf.size = 32 ∧ ∃ p : List ByteArray,
    pathFrom op.sh.a op.out.seen x = some (p.map bytesToDig) ∧ p.length = op.sh.a ∧
        (∀ q ∈ p, q.size = 32) ∧
    Octopus.octF vert op.sh.a [x] [lf] p = [op.out.root]

theorem Climbs.row {vert : ByteArray → ByteArray → ByteArray} {op : OpAt} {x : ℕ} {lf : ByteArray}
    (h : Climbs vert op x lf) {path : List (Dig 256)}
        (hp : pathFrom op.sh.a op.out.seen x = some path) :
    RowOk vert op.sh.a op.out.root lf x path := by
  obtain ⟨hx, hl, p, h1, h2, h3, h4⟩ := h
  obtain rfl : p.map bytesToDig = path := Option.some.inj (h1.symm.trans hp)
  exact rowOk_of_oct hx hl h2 h3 h4

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L))
  (vert : ByteArray → ByteArray → ByteArray)

/-- An opening of a tree of the prover's. -/
structure OwnOk (e1 : Enc1 (Body L)) (D : BD) (num : OpAt → ℕ) (runOf : ℕ → ByteArray)
    (Rt : ℕ → Dig 256 → Prop)
    (op : OpAt) : Prop where
  depth : ∀ s, D.FormIs (num op) s → s.a = op.sh.a
  root : ∀ c, Rt (num op) c → c = bytesToDig op.out.root
  rows : ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts), ∃ lf, Climbs vert op z.1 lf ∧
    ∀ (s : _root_.Fmt.Shape) (x : Fin (2 ^ s.a)) (sym : Fin s.W → UInt64),
        D.FormIs (num op) s → x.val = z.1 →
      List.ofFn sym = z.2.1 →
      (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨e1 s x sym, leafSalt (runOf (num op)) z.2.2⟩ :
                          LeafIn L) : Dig 256) =
        bytesToDig lf

/-- An opening of the stored copy. -/
structure StoOk (embE : PQ.SgX → Body L) (a : ℕ) (cfg : ByteArray) (cm : Dig 256)
    (op : OpAt) : Prop where
  depth : op.sh.a = a
  root : cm = bytesToDig op.out.root
  rows : ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts), ∃ lf, Climbs vert op z.1 lf ∧
    (g TypedOracleCompiler.Compile.Batch.OracleName.leaf (⟨embE (z.1, z.2.1), leafSalt cfg z.2.2⟩ : LeafIn L) :
        Dig 256) =
      bytesToDig lf

variable {g vert}

/-- The one hypothesis on the table of openings holds of the typing's. -/
theorem lookGood_F (N : NodeLaw g vert) {e1 : Enc1 (Body L)} {D : BD} {num : OpAt → ℕ}
    {runOf : ℕ → ByteArray}
    {Rt : ℕ → Dig 256 → Prop} {ops : List OpAt} (hO : ∀ op ∈ ops, OwnOk g vert e1 D num runOf Rt op)
    {tab : List ((ℕ × ℕ) × Row)} (ht : tabOf num ops = some tab) :
    LookGood (Yes g) e1 D.FormIs Rt (lookF runOf tab) := fun n s x o c hF hR hl => by
  obtain ⟨col, salt, hlk, hcol, hsalt⟩ := lookF_some hl
  obtain ⟨op, hop, rfl, hz, hpath⟩ := tabOf_lookup ht hlk
  obtain ⟨lf, hc, hleaf⟩ := (hO op hop).rows _ hz
  have R := hc.row hpath
  rw [← (hO op hop).depth s hF] at R
  rw [(hO op hop).root c hR, hsalt]
  exact runCheck_row N R _ (hleaf s x o.sym hF rfl hcol)

/-- The stored copy's openings. -/
theorem ext_yes (N : NodeLaw g vert) {embE : PQ.SgX → Body L} {a : ℕ} {cfg : ByteArray}
    {cm : Dig 256}
    {ops : List OpAt} (hO : ∀ op ∈ ops, StoOk g vert embE a cfg cm op) {tx : List ((ℕ × ℕ) × Row)}
    (ht : tabOf (fun _ => 0) ops = some tx) (p : Fin (2 ^ a)) (o : Opening 256 PQ.SgX)
        (ho : extF a cfg tx p = some o) :
    Yes g (⟨⟨embE o.sym, o.salt⟩, (we1 a).leaf p, o.path, [cm].getD ((we1 a).which p) default,
        (we1 a).depth⟩ :
      Check 256 L) := by
  unfold extF at ho
  obtain ⟨row, hlk, rfl⟩ := Option.map_eq_some_iff.1 ho
  obtain ⟨op, hop, -, hz, hpath⟩ := tabOf_lookup ht hlk
  obtain ⟨lf, hc, hleaf⟩ := (hO op hop).rows _ hz
  have R := hc.row hpath
  rw [(hO op hop).depth] at R
  show Yes g (⟨⟨embE (p.val, row.1), leafSalt cfg row.2.1⟩, p.val, row.2.2, cm, a⟩ : Check 256 L)
  rw [(hO op hop).root]
  exact runCheck_row N R _ hleaf

/-- AT THE TYPING's STRING THE CHECKS OF THE OPENINGS SAY YES. -/
theorem assemble3_checks (N : NodeLaw g vert) {Xi : Type} (D : BD)
    (dec : Xi → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
    {num : OpAt → ℕ} {w : Own D} {q : Req} {d cfg : ByteArray} {o₁ o₂ o₃ : _root_.Fmt.ChainOut}
    {π : OneProtocolProof 256 (BatchPS D dec).up} (hπ : assemble3 D dec num w q d cfg o₁ o₂ o₃ = some π)
    {e1 : Enc1 (Body L)} {Rt : ℕ → Dig 256 → Prop} {embE : PQ.SgX → Body L} {cm : Dig 256}
    (hOwn : ∀ run₁ run₂ run₃, o₁.run = some run₁ → o₂.run = some run₂ → o₃.run = some run₃ →
      ∀ op ∈ (opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter (fun op => !op.sh.stored),
        OwnOk g vert e1 D num (D.runOf run₁ run₂ run₃) Rt op)
    (hSto : ∀ op ∈ (opsOf 1 o₁ ++ (opsOf 2 o₂ ++ opsOf 3 o₃)).filter (fun op => op.sh.stored),
      StoOk g vert embE D.G.a cfg cm op)
    (K' : ℕ) (hK : K = K' + 1) (chal : ∀ e k, (Fin K' → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (ef : (p : D.F.r.Pos) → D.F.r.Sym p → Body L) (rts : RootsOfChain 256 D.shS) (isRead : OPos D.shS → Bool)
    (isReadE : Fin (2 ^ D.G.a) → Bool)
    (hF : CompGood (r := D.F.r) (Yes g) D.F.posAt D.F.depths ef (rts.1.2.getD [])
        (fun p => isRead (.inl p)) w.fOpen)
    (hR : D.RtsOk Rt rts) (a b : List (Check 256 L))
    (ha : checksB D.shS D.annS (hK ▸ D.wiresS K' chal o) (D.embSS (liftT e1) ef) rts isRead
        π.opens = some a)
    (hb : checksExt (we1 D.G.a) embE [cm] isReadE π.ext (we1 D.G.a).all = some b) :
    (runChecks (K := K) (a ++ b)).det g = true ∧ (a ++ b).all (fun c => c.wellFormed) = true := by
  subst hK
  obtain ⟨run₁, run₂, run₃, a₁, a₂, a₃, tab, tx, h1, h2, h3, -, -, -, e4, e5, -, -, -,
      hop, hext, -⟩ :=
    assemble3_some D dec hπ
  rw [hop] at ha
  rw [hext] at hb
  have H := lookGood_F N (hOwn run₁ run₂ run₃ h1 h2 h3) e4
  exact checks_yes g D.shS D.annS (D.wiresS K' chal o) (D.embSS (liftT e1) ef) rts isRead _
      (we1 D.G.a) embE [cm]
    isReadE _ (D.goodAt H K' chal o ef w.fOpen rts isRead D.forms.1 D.forms.2.1 D.forms.2.2 hF hR)
    (fun p op _ ho => ext_yes N hSto e5 p op ho) a b ha hb

end

end TypedOracleCompiler.Slice
