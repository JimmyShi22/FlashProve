-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/TreeCommit.lean: a committer for the Merkle tree of one stored table, written as a
Lean definition, with a proof of which hash queries it makes.
Purpose. `word_at_path` (OnBytes/K/Arm/TreeWord.lean) assumes three things about a query log. This
file defines `commitM cfg k a rows`, which makes its hash queries to an oracle: given 2 ^ a rows (a
column and a salt each) it queries each leaf, then each inner node, level by level, and returns the
root. Two of the three assumptions are proved for its own log.
States. `commit_log`: a log that contains a run of `commitM` has, for every position, the leaf's
query and the node queries on the path from its answer to the returned root. `commit_own`: for all
oracle functions g, `commitM`'s own log contains such a run. `vertexQ_is`, `leafQ_is`: a node's
query, and a leaf's at its own salt's length, is the one query of the format's routine
(`Fmt.vertexW`, `Fmt.leafW`). `word_of_commit`: the table read back from that log under that root
has, at position p, the symbol x that hb relates to row p.
Under. One premise in `commit_log`: there are 2 ^ a rows. Fourteen in `word_of_commit`: hM (see 8);
hW (the wire record W is well formed, `QueryLayout.OKG`); hn (nb = 8 * k); hr (2 ^ W.depth rows); for row
p: hy (its sizes pass `storedOK`), h0 (its salt has k bytes), hb (x is a symbol whose encoded body
is the row's string `storedStr`); and the seven that the encoding in `word_at_path` needs (hcfg,
hp0, hp1, hpL, hinj, hlen, htr).
Does not show:
 1. that `commitM` is the honest committer of VerifiableInference/, or the scheme's: no theorem;
 2. anything about salts, keys, commitment IDs or encoding: it samples nothing and encodes nothing;
    rows, salts and k are inputs;
 3. that any program that ships hashes a table in this way;
 4. that the format's own builder and walk order left and right as `ClimbsStr` does;
 5. anything about the rows' widths, words or salts, or the length of cfg: all are arbitrary;
 6. that every salt has k bytes (asked only at p, by h0); else a leaf's string is not the format's;
 7. what fills the rows beyond the table's length, up to 2 ^ depth;
 8. hM (the queries read back avoid the hash event `EM`): it is assumed, and it depends on g;
 9. that any g satisfies hM (so `word_of_commit` may hold of nothing), how likely hM is, or how many
    queries are made;
10. hW, hn, hr, hy, h0, hb, or the encoding's own seven: they are assumed as well;
11. that hb, hn and the depth hold for any concrete parameters; no example is given here;
12. that the whole table decodes, or that a key file's root is this root: one position, one tree;
13. anything about a log other than this definition's own;
14. anything about soundness;
15. anything that the executable `verify-on-bytes` runs: it does not import this file.

Notes in full, with every limit at length, are at the end of this file. They are the whole text.
Wherever this summary and the notes differ on a limit or a premise, the stronger limit holds, and
one that only one of the two names holds too; the notes hold for everything else.
Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.TreeLog

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.SeedPage
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Slice.ArmRead TypedOracleCompiler.Slice.ArmLinkCode
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The bits of the string of a stored table's leaf. k: the number that stands for the bytes of a
salt in the label and in the fill (the format's routine takes the salt's own size: the two are one
where s0 has k bytes); a: the tree's depth; x: the position; col: the column; s0: the salt. -/
def leafStr (cfg : ByteArray) (k a x : ℕ) (col : List UInt64) (s0 : ByteArray) : List Bool :=
  bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 col.length (k / 8)) (2 ^ a + x) cfg
    (_root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length k) ++ s0))

/-- The strings of a list of rows (column, salt), the first at the position n. -/
def strsFrom (cfg : ByteArray) (k a : ℕ) : ℕ → List (List UInt64 × ByteArray) → List (List Bool)
  | _, [] => []
  | n, r :: rs => leafStr cfg k a n r.1 r.2 :: strsFrom cfg k a (n + 1) rs

theorem strsFrom_length (cfg : ByteArray) (k a : ℕ) :
    ∀ (rows : List (List UInt64 × ByteArray)) (n : ℕ),
      (strsFrom cfg k a n rows).length = rows.length
  | [], _ => rfl
  | _ :: rs, n => congrArg (· + 1) (strsFrom_length cfg k a rs (n + 1))

theorem strsFrom_getD (cfg : ByteArray) (k a : ℕ) :
    ∀ (rows : List (List UInt64 × ByteArray)) (n i : ℕ), i < rows.length →
      (strsFrom cfg k a n rows).getD i [] =
        leafStr cfg k a (n + i) (rows.getD i default).1 (rows.getD i default).2
  | [], _, i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, _, 0, _ => rfl
  | _ :: rs, n, i + 1, h => by
    have e := strsFrom_getD cfg k a rs (n + 1) i (Nat.lt_of_succ_lt_succ h)
    rw [show n + (i + 1) = n + 1 + i by omega]
    simpa only [strsFrom, List.getD_cons_succ] using e

/-- One query at each string, in order; the answers. -/
def leavesM : List (List Bool) → OComp (rom 256) (List (Dig 256))
  | [] => .pure []
  | s :: ss => (OComp.ask () s).bind fun u => (leavesM ss).bind fun us => .pure (u :: us)

/-- In every trace in which the leaves' queries run: as many answers as strings, and each string's
entry with its answer. -/
theorem leavesM_log {σ : Trace (rom 256)} :
    ∀ (strs : List (List Bool)) (out : List (Dig 256)), RunsIn σ (leavesM strs) out →
      out.length = strs.length ∧ ∀ i, i < strs.length →
        (⟨(), strs.getD i [], out.getD i default⟩ : QA (rom 256)) ∈ σ
  | [], out, h => by
    obtain rfl := runsIn_pure_iff.1 h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | s :: ss, out, h => by
    have h : RunsIn σ ((OComp.ask () s).bind fun u =>
        (leavesM ss).bind fun us => .pure (u :: us)) out := h
    obtain ⟨u, hu, h⟩ := (runsIn_bind_iff _ _ _).1 h
    obtain ⟨us, hus, h⟩ := (runsIn_bind_iff _ _ _).1 h
    obtain rfl := runsIn_pure_iff.1 h
    obtain ⟨hl, hi⟩ := leavesM_log ss us hus
    refine ⟨congrArg (· + 1) hl, fun i hi' => ?_⟩
    cases i with
    | zero => exact runsIn_ask_iff.1 hu
    | succ i =>
      simpa only [List.getD_cons_succ] using hi i (Nat.lt_of_succ_lt_succ hi')

theorem leavesM_noCoin : ∀ strs : List (List Bool), (leavesM strs).NoCoin
  | [] => trivial
  | s :: ss => by
    show ((OComp.ask () s).bind fun u =>
      (leavesM ss).bind fun us => OComp.pure (u :: us)).NoCoin
    exact OComp.NoCoin.bind (fun _ => trivial) fun _ =>
      OComp.NoCoin.bind (leavesM_noCoin ss) fun _ => trivial

/-- **The written committer**: the leaves' queries, the library's tree over their answers at the
format's vertex, the root. Meant at 2 ^ a rows; at another number the limits of the library's tree
hold (the head of Compile/MerkleM.lean). -/
def commitM (cfg : ByteArray) (k a : ℕ) (rows : List (List UInt64 × ByteArray)) :
    OComp (rom 256) (Dig 256) :=
  (leavesM (strsFrom cfg k a 0 rows)).bind fun l =>
    (levelsM (vertexQ cfg) a l).bind fun lv => .pure (rootOf lv)

/-- A vertex's query is the one query of the format's routine at the asking hash. -/
theorem vertexQ_is (cfg : ByteArray) (x y : Dig 256) :
    Rom.toRom (_root_.Fmt.vertexW (_root_.Fmt.HM askB) cfg (digToBytes x) (digToBytes y)) =
      (vertexQ cfg x y).bind fun d => .pure (digToBytes d) := by
  rw [vertexW_asks]
  rfl

/-- So is a leaf's, at the length of its own salt. -/
theorem leafQ_is (cfg : ByteArray) (a x : ℕ) (col : List UInt64) (s0 : ByteArray) :
    Rom.toRom (_root_.Fmt.leafW (_root_.Fmt.HM askB) (_root_.Fmt.leafNo true) 0 a x cfg col s0) =
      (OComp.ask () (leafStr cfg s0.size a x col s0)).bind fun d => .pure (digToBytes d) := by
  rw [leafW_asks]
  rfl

/-- **What every trace holds in which the committer runs.** -/
theorem commit_log (cfg : ByteArray) (k a : ℕ) (rows : List (List UInt64 × ByteArray))
    {σ : Trace (rom 256)} {cm : Dig 256} (h : RunsIn σ (commitM cfg k a rows) cm)
    (hr : rows.length = 2 ^ a) (x : ℕ) (hx : x < 2 ^ a) :
    ∃ (u : Dig 256) (path : List (Dig 256)),
      (⟨(), leafStr cfg k a x (rows.getD x default).1 (rows.getD x default).2, u⟩ :
        QA (rom 256)) ∈ σ ∧ path.length = a ∧ ClimbsStr σ cfg path x u cm := by
  unfold commitM at h
  obtain ⟨l, hl, h⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain ⟨lv, hlv, h⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain rfl := runsIn_pure_iff.1 h
  obtain ⟨e1, e2⟩ := leavesM_log _ l hl
  rw [strsFrom_length] at e1 e2
  obtain ⟨p1, p2⟩ := levels_log cfg a l lv (e1.trans hr) hlv x hx
  have hx' : x < rows.length := by rw [hr]; exact hx
  have e3 := e2 x hx'
  rw [strsFrom_getD cfg k a rows 0 x hx', Nat.zero_add] at e3
  exact ⟨l.getD x default, pathOf lv x, e3, p1, p2⟩

theorem commitM_noCoin (cfg : ByteArray) (k a : ℕ) (rows : List (List UInt64 × ByteArray)) :
    (commitM cfg k a rows).NoCoin := by
  show ((leavesM (strsFrom cfg k a 0 rows)).bind fun l =>
    (levelsM (vertexQ cfg) a l).bind fun lv => OComp.pure (rootOf lv)).NoCoin
  exact OComp.NoCoin.bind (leavesM_noCoin _) fun l =>
    OComp.NoCoin.bind (noCoin_levelsM cfg a l) fun _ => trivial

/-- **At every g the committer runs in its own log to its own value.** -/
theorem commit_own (cfg : ByteArray) (k a : ℕ) (rows : List (List UInt64 × ByteArray))
    (g : Fam (rom 256)) :
    RunsIn ((commitM cfg k a rows).withTrace.det g).2 (commitM cfg k a rows)
      ((commitM cfg k a rows).det g) :=
  runsIn_ownLog g (commitM_noCoin cfg k a rows)

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (nb : ℕ)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (K : ℕ) (back : StrCode (AllPts 256 K L2))

/-- **The word under the committer's root, off the committer's own log, has at a position the
symbol of that row.** hM: what the encoding reads off that log is outside the event `EM`: a premise
on g. -/
theorem word_of_commit (W : QueryLayout 256 L2) (hW : W.OKG) (backW : StrCode (AllPts 256 W.K L2))
    (k : ℕ) (hn : nb = 8 * k) (rows : List (List UInt64 × ByteArray))
    (hr : rows.length = 2 ^ W.depth) (g : Fam (rom 256))
    (hM : ¬ EM (singleTr (implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF
      bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K backW)
      ((commitM cfg k W.depth rows).withTrace.det g).2))
    (p : Fin L2.wordLength) (hy : TypedOracleCompiler.Run.storedOK W.depth k (p.val, (rows.getD p.val default).1))
    (h0 : (rows.getD p.val default).2.size = k) (x : L2.Symbol)
    (hb : bd (W.embE x) =
      TypedOracleCompiler.Run.storedStr W.depth k (p.val, (rows.getD p.val default).1)) :
    extEnc W (singleTr (implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF
      bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K backW)
      ((commitM cfg k W.depth rows).withTrace.det g).2) ((commitM cfg k W.depth rows).det g) p =
      x := by
  obtain ⟨u, path, hl, hd, hc⟩ := commit_log cfg k W.depth rows (commit_own cfg k W.depth rows g)
    hr p.val (lt_of_lt_of_le p.isLt hW.fits)
  exact word_at_path D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL
    hpL cA tr hinj hlen htr W hW backW _ hM k hn W.depth (p.val, (rows.getD p.val default).1) hy
    (rows.getD p.val default).2 h0 x hb p rfl u _ path hd hl hc

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.vertexQ_is
#print axioms OnBytes.K.Arm.leafQ_is
#print axioms OnBytes.K.Arm.commit_log
#print axioms OnBytes.K.Arm.commit_own
#print axioms OnBytes.K.Arm.word_of_commit

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/K/Arm/TreeCommit.lean: a written committer to one stored table's tree: a term over the one
oracle that is given the table's rows with their salts and hashes the tree as the format's rules
say; and what its log holds: for every position the string `leafStr` of that row, which is the
format's string of that leaf where the row's salt has k bytes, and the format's strings of the
vertices from that leaf's answer up to the root that the term returns. So two of the three premises
on the log in `word_at_path` (OnBytes/K/Arm/TreeWord.lean) hold of this term's own log, at every
function.

What it is not. NOT THE HONEST COMMITTER of VerifiableInference/ (lean/GLOSSARY.md: argument
system), nor the scheme's: no law ties this term to them. It draws no salt and tosses no coin; it
encodes nothing; it makes no key and no commitment ID: rows, salts and the number k are its
arguments. A WRITTEN TERM: that any program which ships, in any language, hashes a table so is not
claimed, nor that the format's own builder and walk (Fmt/Rules7.lean) lay left and right as
`ClimbsStr` does. THE ROWS ARE LETTERS: nothing is asked of their widths, their words or their
salts, nor of the length of cfg. THAT EVERY ROW's SALT HAS k BYTES IS ASKED NOWHERE but at the one
position in `word_of_commit` (h0): at a row whose salt has another length the string asked has k in
its label and its fill, and is not the format's. The rows beyond the word's length, up to 2 ^ depth,
are letters too: what fills them in the format is not said. THE THIRD PREMISE ON THE LOG STAYS A
PREMISE, BY NAME (hM): that what the encoding reads off the log is outside the event `EM`
(OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean). It is an event of the function that answers; at a letter g
it is no theorem. NO g IS SHOWN TO MEET hM: by Lean alone `word_of_commit` could be idle; no price
of the event and no count of the log's entries is stated. ASKED BESIDE hM in `word_of_commit`: hW
(the wire's laws), hn (nb = 8 k), hr (2 ^ depth rows), and at the position hy (`storedOK`), h0, hb
(a symbol whose body is the row's string), with the letters and laws of `word_at_path`'s encoding.
That hb, hn and the depth hold at any written wire, plan or file is not claimed; no member of these
letters is written or evaluated here. One position is spoken of at a time, and one table's tree:
that the whole word decodes, and that a key file's root is this term's value, are not claimed.
Nothing on any log but this term's. Nothing on soundness. For proofs only; the executable
`verify-on-bytes` does not import this file.

How it is made. The leaves are asked in their order, each at the string `leafStr`; the answers are
paired level by level by the library's own tree (`levelsM`, `rootOf`, Compile/MerkleM.lean) at the
vertex's query `vertexQ` (OnBytes/K/Arm/TreeLog.lean). So, by the term's text, all leaves are asked
first, then the vertices level by level upward: no vertex is asked before the two queries whose
answers it holds. A vertex's query is the one query of the format's routine at the hash that asks
the oracle (`vertexQ_is`); so is a leaf's where the row's salt has k bytes: `leafQ_is` speaks at the
length of the row's own salt (by `vertexW_asks`, `leafW_asks`, OnBytes/K/Arm/TreeStrings.lean).

Main names.
 `leafStr`, `strsFrom`, `leavesM`, `commitM`   the string of a stored leaf; the strings of a list of
                rows; the leaves' queries; the written committer.
 `vertexQ_is`, `leafQ_is`   the two ties to `Fmt.vertexW`, `Fmt.leafW` at `Fmt.HM askB`.
 `commit_log`   in every trace in which the committer runs to cm, at 2 ^ a rows: at every position
                the leaf's entry and a `ClimbsStr` of length a from its answer to cm.
 `commit_own`   at every g the committer runs in its own log to its own value.
 `word_of_commit`   `word_at_path` at that log and that value: its hl, hc, hd are paid; hM and six
                more premises stay.

Open. What is left of the event at this term, by a reading of the two texts and by no law: a log
lists the first query first, and a vertex's two halves are answers of earlier entries; so, where
every row's string is read as a leaf's (every row within the format's bounds, every salt of k
bytes), the event would be two different entries of the log with one answer. If that is so, hM could
be had from "no collision in the term's own log", and priced. Namesakes in other namespaces, joined
to these by no law: `OnBytes.Maker.Page.leafStr` (OnBytes/Maker/Page/CollidesStr.lean [not in this library]), which spells
a leaf's call as bytes at a shape; `OnBytes.Maker.Page.leavesM`, a code of leaves.

Terms: lean/GLOSSARY.md.
-/
