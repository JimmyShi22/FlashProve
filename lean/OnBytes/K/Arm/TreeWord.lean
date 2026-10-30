-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`OnBytes/K/Arm/TreeWord.lean`: from hash queries to committed data. If a list of queries holds one
column of a stored table and its path in the hash tree, hashed as the file format says, then the
library reads that column at that position under the tree's root.

States. `word_at_path`: `extEnc W (singleTr m σ) cm p = x`. Here σ is any list of hash queries with
answers; m is the encoding of TreeStrings.lean, which spells typed queries as strings; `singleTr`
reads σ back as typed queries; `extEnc` reads the data under the root cm. `ClimbsStr` says that σ
holds, level by level, the format's query for each node from a value up to a root.
`extLeaf_at_path`: the same for the typed query at the bottom of the path. `mem_singleTr`: an entry
of σ at the string of a typed query whose answer is one block is read back as that typed query.
Under. Ten hypotheses, beside the seven that the encoding m itself takes as arguments (hcfg, hp0,
hp1, hpL, hinj, hlen, htr). hM: the library's hash event `EM` (the answer of a new tree query occurs
at an earlier entry) does not happen in what is read off σ. hl, hc: σ holds the queries. W :
`QueryLayout`; hW : `W.OKG`, its well-formedness conditions. hn, hy, h0, hb, hp, hd: salt length, ranges,
how x is spelled, position, depth.
Does not show.
  1. That any list of queries holds these entries: this file defines no committer.
  2. That the format's own tree walk puts left and right as `ClimbsStr` does: read, not proved.
  3. That all the data decodes: one position is spoken of; at a position for which σ holds no
     entries the data is a fixed default value.
  4. Anything at a list of queries in which the event `EM` happens.
  5. That hb, hn and the depth hold at any concrete `QueryLayout`, plan of a file (`Fmt/`) or file.
  6. Anything on soundness.
  7. Anything about a program: the file is for proofs only, and no program imports it.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Arm.TreeStrings
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import Rom.ExitDown

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

/-- An entry of a log of strings, at the string of a typed query whose answer is one block, stands
as a typed entry in what `singleTr` reads off the log. -/
theorem mem_singleTr {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (σ : Trace (rom lam)) (o : S.ι)
    (q : S.Dom o) (j : Fin (m.blocks o)) (d : Fin lam → Bool) (hb : m.blocks o = 1)
    (h : (⟨(), m.code o q j, d⟩ : QA (rom lam)) ∈ σ) :
    (⟨o, q, (m.rng o).symm fun _ => d⟩ : QA S) ∈ singleTr m σ := by
  unfold singleTr
  refine List.mem_filterMap.2 ⟨_, h, ?_⟩
  show (if m.blocks (m.dec (m.code o q j)).1 = 1 then
    some (⟨(m.dec (m.code o q j)).1, (m.dec (m.code o q j)).2.1,
      (m.rng (m.dec (m.code o q j)).1).symm fun _ => d⟩ : QA S) else none) = _
  rw [m.dec_code o q j]
  exact if_pos hb

/-- **A log of strings holds the format's strings of the vertices up a path**: from the value c at
the place j, past the siblings of the list, to the value r. -/
def ClimbsStr (σ : Trace (rom 256)) (cfg : ByteArray) :
    List (Dig 256) → ℕ → Dig 256 → Dig 256 → Prop
  | [], _, c, r => c = r
  | s :: ss, j, c, r => ∃ u : Dig 256,
      (⟨(), bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg
        (if j % 2 = 0 then digToBytes c ++ digToBytes s else digToBytes s ++ digToBytes c)), u⟩ :
        QA (rom 256)) ∈ σ ∧ ClimbsStr σ cfg ss (j / 2) u r

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

/-- The encoding, for short. -/
local notation "mE" =>
  implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL
    sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back

/-- A vertex's string in the log is a typed vertex entry. -/
theorem node_mem (σ : Trace (rom 256)) (a b u : Dig 256)
    (h : (⟨(), bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (digToBytes a ++ digToBytes b)), u⟩ :
      QA (rom 256)) ∈ σ) :
    (⟨OracleName.node, (List.ofFn a, List.ofFn b), u⟩ : QA (typedOracleFamily 256 K L2)) ∈ singleTr mE σ := by
  have e := implL2_vertex D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    isPL hpL cA tr hinj hlen htr K back (List.ofFn a) (List.ofFn b) List.length_ofFn
    List.length_ofFn ⟨0, Nat.one_pos⟩
  exact mem_singleTr mE σ OracleName.node (List.ofFn a, List.ofFn b) ⟨0, Nat.one_pos⟩ u rfl (e ▸ h)

/-- A stored leaf's string in the log is a typed leaf entry. -/
theorem leaf_mem (σ : Trace (rom 256)) (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64)
    (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray) (h0 : s0.size = k) (b : L2.Bd)
    (hb : bd b = TypedOracleCompiler.Run.storedStr a k y) (u : Dig 256)
    (h : (⟨(), bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (k / 8))
      (2 ^ a + y.1) cfg (_root_.Fmt.colBytes y.2 ++
        _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length k) ++ s0)), u⟩ : QA (rom 256)) ∈ σ) :
    (⟨OracleName.leaf, ⟨b, bytesToBits cfg ++ bytesToBits s0⟩, u⟩ : QA (typedOracleFamily 256 K L2)) ∈
      singleTr mE σ := by
  have e := implL2_stored_leaf D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
    rest isPL hpL cA tr hinj hlen htr K back k hn a y hy s0 h0 b hb ⟨0, Nat.one_pos⟩
  exact mem_singleTr mE σ OracleName.leaf ⟨b, bytesToBits cfg ++ bytesToBits s0⟩ ⟨0, Nat.one_pos⟩ u rfl
    (e ▸ h)

/-- The typed climb runs within what is read off such a log. -/
theorem runsIn_climb (σ : Trace (rom 256)) :
    ∀ (path : List (Dig 256)) (j : ℕ) (c r : Dig 256), ClimbsStr σ cfg path j c r →
      RunsIn (singleTr mE σ)
        (climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) path j c) r
  | [], _, c, r, h => runsIn_pure_iff.2 h
  | x :: xs, j, c, r, h => by
    obtain ⟨u, hm, hr⟩ := h
    by_cases hb : j % 2 = 0
    · have e : climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) (x :: xs) j c =
          (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2) c x).bind fun u =>
            climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) xs (j / 2) u := by
        simp only [climbM, if_pos hb]; rfl
      rw [if_pos hb] at hm
      rw [e, runsIn_bind_iff]
      exact ⟨u, runsIn_ask_iff.2 (node_mem D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL
        sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back σ c x u hm),
        runsIn_climb σ xs (j / 2) u r hr⟩
    · have e : climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) (x :: xs) j c =
          (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2) x c).bind fun u =>
            climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) xs (j / 2) u := by
        simp only [climbM, if_neg hb]; rfl
      rw [if_neg hb] at hm
      rw [e, runsIn_bind_iff]
      exact ⟨u, runsIn_ask_iff.2 (node_mem D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL
        sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back σ x c u hm),
        runsIn_climb σ xs (j / 2) u r hr⟩

/-- **Outside the event `EM`, what the log determines at the leaf's place under the root is the
typed leaf query.** -/
theorem extLeaf_at_path (σ : Trace (rom 256)) (hM : ¬ EM (singleTr mE σ)) (k : ℕ) (hn : nb = 8 * k)
    (a : ℕ) (y : ℕ × List UInt64) (hy : TypedOracleCompiler.Run.storedOK a k y) (s0 : ByteArray)
    (h0 : s0.size = k) (b : L2.Bd) (hb : bd b = TypedOracleCompiler.Run.storedStr a k y) (u cm : Dig 256)
    (path : List (Dig 256)) (hj : y.1 < 2 ^ path.length)
    (hl : (⟨(), bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (k / 8))
      (2 ^ a + y.1) cfg (_root_.Fmt.colBytes y.2 ++
        _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length k) ++ s0)), u⟩ : QA (rom 256)) ∈ σ)
    (hc : ClimbsStr σ cfg path y.1 u cm) :
    extLeaf (singleTr mE σ) path.length cm y.1 =
      some ⟨b, bytesToBits cfg ++ bytesToBits s0⟩ := by
  refine extLeaf_of_check (K := K)
    ⟨⟨b, bytesToBits cfg ++ bytesToBits s0⟩, y.1, path, cm, path.length⟩ hM ?_ ?_
  · simp only [TypedOracleCompiler.Compile.Batch.Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨trivial, hj⟩
  · show RunsIn _ ((askTypedOracle (K := K) (L := L2) OracleName.leaf ⟨b, bytesToBits cfg ++ bytesToBits s0⟩).bind
      fun d =>
        (climbM (TypedOracleCompiler.Compile.Batch.hashTreeNode (K := K) (L := L2)) path y.1 d).bind fun r =>
        OComp.pure (decide (r = cm))) true
    rw [runsIn_bind_iff]
    refine ⟨u, runsIn_ask_iff.2 (leaf_mem D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL
      sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K back σ k hn a y hy s0 h0 b hb u hl), ?_⟩
    rw [runsIn_bind_iff]
    exact ⟨cm, runsIn_climb D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
      rest isPL hpL cA tr hinj hlen htr K back σ path y.1 u cm hc,
      runsIn_pure_iff.2 (decide_eq_true rfl)⟩

/-- **The word at a path.** Off a log of strings that holds the format's string of a stored leaf and
the format's strings of the vertices up a path from the leaf's answer to cm, outside the event `EM`
of what the encoding reads off the log: the word under cm has at the leaf's position the leaf's
symbol. -/
theorem word_at_path (W : QueryLayout 256 L2) (hW : W.OKG) (backW : StrCode (AllPts 256 W.K L2))
    (σ : Trace (rom 256))
    (hM : ¬ EM (singleTr (implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF
      bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K backW) σ))
    (k : ℕ) (hn : nb = 8 * k) (a : ℕ) (y : ℕ × List UInt64) (hy : TypedOracleCompiler.Run.storedOK a k y)
    (s0 : ByteArray) (h0 : s0.size = k) (x : L2.Symbol)
    (hb : bd (W.embE x) = TypedOracleCompiler.Run.storedStr a k y) (p : Fin L2.wordLength) (hp : p.val = y.1)
    (u cm : Dig 256) (path : List (Dig 256)) (hd : path.length = W.depth)
    (hl : (⟨(), bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (k / 8))
      (2 ^ a + y.1) cfg (_root_.Fmt.colBytes y.2 ++
        _root_.Fmt.zeroBytes (_root_.Fmt.fillLen y.2.length k) ++ s0)), u⟩ : QA (rom 256)) ∈ σ)
    (hc : ClimbsStr σ cfg path y.1 u cm) :
    extEnc W (singleTr (implL2 D d₁ cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb cfg) L2 pbF
      bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K backW) σ) cm p =
      x := by
  refine extEnc_apply hW (sl := bytesToBits cfg ++ bytesToBits s0) ?_
  rw [← hd, hp]
  refine extLeaf_at_path D d₁ cfg hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    isPL hpL cA tr hinj hlen htr W.K backW σ hM k hn a y hy s0 h0 (W.embE x) hb u cm path ?_ hl hc
  rw [hd, ← hp]
  exact lt_of_lt_of_le p.isLt hW.fits

end OnBytes.K.Arm

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/K/Arm/TreeWord.lean: THE WORD AT A PATH: off a log of strings that holds the format's string
of one leaf of a stored table's tree and the format's strings of the vertices on the way from that
leaf to a root, and outside the library's hash event `EM` of what is read off that log, the word
under the root, read through the entry file's arm's encoding, has at the leaf's position the leaf's
symbol. Definitions, statements and proofs.

Why. The promise on a key file's arm speaks of the word under the key's root, read off the
committer's log through that encoding (`wordOf := extEnc .. (singleTr m tr) cm`, Johnson/Top/Pub/).
OnBytes/K/Arm/TreeStrings.lean shows that the encoding's strings at a vertex and at a stored leaf
are the format's. Here that is carried to the word, position by position.

m stands for the encoding of TreeStrings.lean.

Main names.
  `mem_singleTr`: general in the encoding: an entry of the log at the string of a typed query whose
    answer is one block is a typed entry of what `singleTr` reads.
  `ClimbsStr σ cfg path j c r`: the log σ holds, level by level, an entry at the format's string of
    the vertex over the value so far and the path's next sibling (the value on the left where the
    place is even), with the next value as its answer; from c at the place j to r.
  `node_mem`, `leaf_mem`: such an entry, and one at a stored leaf's string, as typed entries.
  `runsIn_climb`: the library's climb (`climbM hashTreeNode`) runs within what is read off such a log.
  `extLeaf_at_path`: outside `EM`, what the log determines at the place under the root is the typed
    leaf query.
  `word_at_path`: THE STATEMENT: `extEnc W (singleTr m σ) cm p = x`.
By `extLeaf_of_check` (OnBytes/TypedOracleCompiler/Compile/Batch/Hash.lean) and `extEnc_apply`
(OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean).
What is asked, by name: hW : the wire's laws; hM : not `EM` of what is read off the log
(OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean: "the answer of a new Merkle query occurs at an earlier entry
of the trace"); hn, hy, h0 as in TreeStrings.lean; hb : bd reads the wire's body of the symbol x as
the string of the stored symbol y; hp : the position is y's; hd : the path has the wire's depth; hl,
hc : the entries.

What is not claimed. THAT ANY LOG HOLDS THESE ENTRIES: this file writes no committer; that any log
holds such entries is not shown here. That the format's own walk lays left
and right as `ClimbsStr` does (the place's lowest bit first): a reading of Fmt/Rules7.lean, no law
here. That the whole word decodes: one position is spoken of; a position of which the log holds
nothing has the wire's filling. hM is a premise on the log: at a log with such an event nothing is
said. That hb, hn and the depth hold at any written wire, plan or file. Nothing on soundness. For
proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
