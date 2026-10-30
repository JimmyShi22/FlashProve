-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Toy1TieTree.lean.
Run/Toy1TieTree.lean: the compiled verifier's walk through a Merkle opening, at typed oracle
functions, agrees with the format page's reader of an opening.

This is the trees' half of the comparison between the compiled verifier at typed oracle functions
and the file reader of the format page (FORMAT.md, which comes with the programs, the C++
implementation that comes with this Lean code). On what the page's reader returns for an opening,
the verifier's walk says yes exactly if the reader's root is the root that was sent. This holds
UNDER A HYPOTHESIS ON HOW A LEAF'S SYMBOL IS SPELLED, AND FOR TREES MADE IN A RUN (not for stored
trees). The file holds definitions, statements as theorems, and proofs. It is generic in the ambient
interface L, in the spellings D (PageD, Run/CodingFn.lean), in the depth, and in the oracle O :
ByteArray → ByteArray with answers of 32 bytes. The links to a toy's own data are in
Run/Toy1TieChecks.lean.

Sources. The leaf's label (Fmt.leafPlace) was written against the format page (FORMAT.md, R2.1);
this file has not been held against the page as it ships, and may differ from it.


1. What the file contains (definitions).
   forestV K g a rt b      The verifier's own walk, as a formula.
   checksOf sy run rt Ob   The checks that a parser's opening Ob (OpenB, Run/ParseBS.lean) calls
                           for: position by position the symbol's body, the typed salt (the run's
                           value, then the file's salt), and the whole path that Octopus.fill makes.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   Bits against bytes. getD_bitsL, bytesToDig_eq; dig_bytes (32 bytes, as a digest, as bytes, are
   the same bytes); bytes_dig (a digest, as bytes, as a digest); bytesToDig_inj (on strings of 32
   bytes).
   The typed queries against the page's hash calls, at the family famOf O D K that O induces.
     famOf_node, hNode_famOf      A node query is the page's vertex at the hash HO O with the start
                                  D.cfg, read as a digest. As a function of two digests the node
                                  oracle is digFn (vP O D).
     famOf_leaf, famOf_leaf_page A leaf query whose typed salt is (the run's value, then the file's
     salt), at a symbol that D spells as (Fmt.leafPlace of the tree's number, the column's words and
     the salt's words; 2^a + x; the column with its fill), is the page's leaf at HO O under the
     number 164, read as a digest.
   The library's walk on typed digests and on bytes (hP is any function whose values have 32 bytes;
   digFn hP is the function on digests that it induces).
     step_dig, size_stepF, oct_dig, size_octF     On values and given digests of 32 bytes each, with
                                                  as many values as numbers and enough given
                                                  digests: Octopus.octF (digFn hP) on the digests is
                                                  Octopus.octF hP on the bytes, read as digests.
     forest_iff       If the opened leaves come to one vertex: "every value left is the root" on
                      digests says the same as "the walk on bytes ends in the root".
   The verifier's own walk. det_leavesV, det_runForest: forestV is runForest
   (Compile/Batch/Verifier.lean) of the forest with the one tree (depth a, root rt, checks b), on
   the digests that the verifier reads off the paths, run at the family g.
   Put together.
     forestV_checksOf     If the run's value and the root have 32 bytes each, Ob passes the parser's
                          own test and has a position, and D spells the symbol of (x, column) as
                          (Fmt.leafPlace of the tree's number, the column's words and the salt's
                          words; 2^a + x; the column with its fill) FOR x BELOW 2^a AND COLUMNS OF W
                          ELEMENTS: then forestV at famOf O D K on checksOf = "the library's walk on
                          bytes, at the page's vertex and on the page's leaves, ends in the root".
                          Auxiliary: leafV_eq, ok_spec, ok_list, incr_pairwise, zip4_three,
                          zip4_ends.
     reader_ok            What Fmt.readOpeningW (at Id, any hash) returns passes the parser's own
                          test, and its list is not empty. Auxiliary: rdMany_all, rdBytes_size,
                          listOK_incr.
     forestV_reader       UNDER THE SAME HYPOTHESIS ON D'S SPELLING, for a tree that is made in a
                          run (not a stored one), and a run's value and a sent root of 32 bytes
                          each: if Fmt.readOpeningW at HO O, with the start D.cfg of the vertices,
                          returns o, then forestV (famOf O D K) a (the sent root, as a digest)
                          (checksOf .. on o's columns, salts and given digests) = decide (o.root =
                          the sent root).

4. What is proved elsewhere, what is missing, and what is not claimed.
   Elsewhere (Run/Toy1TieChecks.lean): that the checks which the verifier forms from a parser's
   openings (checksComp over all 2^a numbers, at the openings OpenB.at) are checksOf; and that a
   small toy of our own (Run/ToyQ.lean) spells a leaf as the hypothesis on D wants.
   MISSING: where the reader refuses (too few bytes, a word that is no element) there is no o, and
   nothing is said. Both readers refuse there by their own tests.
   Nothing on the chain's queries. NO STATEMENT ON SOUNDNESS FOLLOWS, and none on privacy.

Terms: lean/GLOSSARY.md.

-/
import Run.Toy1TieTree
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.CodingFn
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
import OnBytes.TypedOracleCompiler.Compile.Batch.SeedNode
import Run.CodingBitsLaws
import OnBytes.TypedOracleCompiler.Run.CodingPage160
import Run.WalkTieProofs
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Rom.Cache
import Compile.Batch.SeedCache
import OnBytes.TypedOracleCompiler.Run.ParseBS
import Compile.OctopusRom

namespace TypedOracleCompiler.Run.TieTree
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch Octopus _root_.Run.WalkTie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.TieTree
export _root_.Run.TieTree (getD_bitsOfByte zero_bit getD_bitsL bytesToDig_eq dig_bytes bytes_dig
    bytesToDig_inj digFn step_dig size_stepF oct_dig size_octF forest_iff leafV_eq ok_spec
    incr_pairwise ok_list zip4_three zip4_ends rdMany_all rdBytes_size listOK_incr reader_ok)

/-! ### Bits against bytes: a digest -/

/-! ### The typed node query and the typed leaf query against the page's calls -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- A NODE QUERY IS THE PAGE'S VERTEX. -/
theorem famOf_node (q : Bits × Bits) :
    famOf O D K .node q =
      bytesToDig
        (_root_.Fmt.vertexW (m := Id) (_root_.Fmt.HO O) D.cfg
          (bitsToBytes q.1) (bitsToBytes q.2)) := rfl

/-- a leaf query, as the coding reads it -/
theorem famOf_leaf (s : L.Bd) (z : ℕ × ℕ × ByteArray) (hz : D.leaf s = some z) (salt : Bits) :
    famOf O D K .leaf ⟨s, salt⟩ =
      bytesToDig
        (_root_.Fmt.HO O 164 z.1 z.2.1 (bitsToBytes (salt.take 256))
          (z.2.2 ++ bitsToBytes (salt.drop 256))) := by
  show ansOf O (leafCall D ⟨s, salt⟩) = _
  rw [leafCall_self D s z hz salt]
  rfl

/-- A LEAF QUERY IS THE PAGE'S LEAF, if the typed salt is the run's value and then the file's salt,
and the spelling of the symbol is: the tree's number with the numbers of the column's and the salt's
words above it (Fmt.leafPlace), 2^a + x, the column with its fill. -/
theorem famOf_leaf_page (s : L.Bd) (run fsalt : ByteArray) (hr : run.size = 32)
    (tree a x : ℕ) (col : List UInt64)
    (hs : D.leaf s =
      some (_root_.Fmt.leafPlace tree col.length (fsalt.size / 8),
        2 ^ a + x,
        _root_.Fmt.colBytes col ++
          _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length fsalt.size))) :
    famOf O D K .leaf ⟨s, bytesToBits run ++ bytesToBits fsalt⟩ =
      bytesToDig (_root_.Fmt.leafW (m := Id) (_root_.Fmt.HO O) 164 tree a x run col fsalt) := by
  have hl : (bytesToBits run).length = 256 := by rw [length_bytesToBits, hr]
  rw [famOf_leaf O D K s _ hs, List.take_left' hl, List.drop_left' hl,
    bitsToBytes_bytesToBits, bitsToBytes_bytesToBits]
  rfl

end

/-! ### The library's walk on digests and on 32 bytes -/

section
variable (hP : ByteArray → ByteArray → ByteArray) (h32 : ∀ l r, (hP l r).size = 32)

include h32 in

include h32 in

include h32 in

include h32 in

end

/-! ### The typed family that an oracle induces, and the page's reader -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- the page's vertex at the oracle O -/
def vP (l r : ByteArray) : ByteArray := _root_.Fmt.HO O 166 0 0 D.cfg (l ++ r)

theorem size_vP (hO : ∀ s, (O s).size = 32) (l r : ByteArray) : (vP O D l r).size = 32 := hO _

/-- THE NODE ORACLE AS A FUNCTION OF TWO DIGESTS. -/
theorem hNode_famOf : Compile.Batch.Seed.hNode (famOf O D K) = digFn (vP O D) := by
  funext a b
  unfold Compile.Batch.Seed.hNode digFn vP digToBytes
  rw [famOf_node]
  dsimp only [_root_.Fmt.vertexW]

/-- The forest's part of the verifier's run at a family g of typed oracle functions: one tree of
depth a with the root rt; b: the checks. -/
def forestV (g : Fam (typedOracleFamily 256 K L)) (a : ℕ) (rt : Dig 256) (b : List (Check 256 L)) : Bool :=
  ((upN a (b.map fun c => 0 * 2 ^ a + c.j)).zip
      (Octopus.octF (Compile.Batch.Seed.hNode g) a
        (b.map fun c => 0 * 2 ^ a + c.j) (b.map fun c => g OracleName.leaf c.inp)
        ((reads a (b.map fun c => (0 * 2 ^ a + c.j, c.path))).take
          (need a (b.map fun c => 0 * 2 ^ a + c.j))))).all
    fun m => decide (m.2 = rt)

theorem det_leavesV (g : Fam (typedOracleFamily 256 K L)) :
    ∀ es : List (ℕ × Check 256 L), (leavesV (K := K) es).det g = es.map fun e => g OracleName.leaf e.2.inp
  | [] => rfl
  | e :: es => by
    show ((askTypedOracle (L := L) (K := K) OracleName.leaf e.2.inp).bind fun d =>
        (leavesV es).bind fun r => OComp.pure (d :: r)).det g = _
    rw [OComp.det_bind, OComp.det_bind, det_leavesV g es]
    rfl

/-- forestV IS THE VERIFIER'S OWN WALK THROUGH ONE FOREST (Compile/Batch/Verifier.lean: runForest,
on the digests that it reads off the paths), run at g. -/
theorem det_runForest (g : Fam (typedOracleFamily 256 K L)) (a : ℕ) (rt : Dig 256) (b : List (Check 256 L)) :
    (runForest (K := K) (⟨a, fun _ => rt, b.map fun c => (0, c)⟩ : Forest 256 L)
        ((Forest.reads (⟨a, fun _ => rt, b.map fun c => (0, c)⟩ : Forest 256 L)).take
          (Forest.need (⟨a, fun _ => rt, b.map fun c => (0, c)⟩ : Forest 256 L)))).det g =
      forestV K g a rt b := by
  unfold runForest
  show ((leavesV (K := K) (b.map fun c => (0, c))).bind fun v =>
      (octC Compile.Batch.hashTreeNode a _ v _).bind fun out => OComp.pure _).det g = _
  rw [OComp.det_bind, OComp.det_bind, det_leavesV,
    (Compile.Batch.Seed.evalO g).octC (hN := Compile.Batch.Seed.hNode g) (fun _ _ => rfl)]
  simp only [forestV, Forest.idx, Forest.reads, Forest.need, List.map_map, Function.comp_def]
  rfl

/-- the checks that a parser's opening calls for: position by position, the symbol's body, the typed
salt (the run's value, then the file's salt), the whole path -/
def checksOf (sy : ℕ → List UInt64 → L.Bd) (run : ByteArray)
    (rt : Dig 256) (Ob : OpenB) : List (Check 256 L) :=
  (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).map fun e =>
    ⟨⟨sy e.1 e.2.1, leafSalt run e.2.2.1⟩, e.1, e.2.2.2, rt, Ob.a⟩

end

/-! ### Put together: the verifier's walk on a parser's opening, and the walk on bytes -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- THE VERIFIER'S WALK ON THE CHECKS THAT A PARSER'S OPENING CALLS FOR SAYS YES EXACTLY IF THE
LIBRARY'S WALK ON BYTES, AT THE PAGE'S VERTEX AND ON THE PAGE'S LEAVES, ENDS IN THE ROOT. O answers
with 32 bytes; sy: how a position and a column become a symbol; D spells that symbol as the page
wants. -/
theorem forestV_checksOf (hO : ∀ s, (O s).size = 32) (sy : ℕ → List UInt64 → L.Bd)
    (run root : ByteArray) (hr : run.size = 32) (hroot : root.size = 32) (Ob : OpenB)
    (sb W tree : ℕ) (hok : Ob.ok sb W = true) (hne : Ob.idx ≠ [])
    (hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = W →
      D.leaf (sy x col) =
        some (_root_.Fmt.leafPlace tree W (sb / 8),
          2 ^ Ob.a + x,
          _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen W sb))) :
    forestV K (famOf O D K) Ob.a (bytesToDig root) (checksOf sy run (bytesToDig root) Ob) =
      decide ((Octopus.octF (vP O D) Ob.a Ob.idx
          (leafV (_root_.Fmt.HO O) ⟨Ob.a, W, false, tree⟩ run Ob.idx (Ob.cols.zip Ob.salts))
          Ob.given).headD default = root) := by
  obtain ⟨hc, hs, hsz, hg, hg32⟩ := ok_spec Ob sb W hok
  obtain ⟨hp, hb, hcw⟩ := ok_list Ob sb W hok
  have hpl : Ob.paths.length = Ob.idx.length := length_fill _ _ _
  have hA : (checksOf sy run (bytesToDig root) Ob).map (fun c => 0 * 2 ^ Ob.a + c.j) = Ob.idx := by
    unfold checksOf
    rw [List.map_map]
    have : ((fun c : Check 256 L => 0 * 2 ^ Ob.a + c.j) ∘
          fun e : ℕ × List UInt64 × ByteArray × List (Dig 256) =>
            (⟨⟨sy e.1 e.2.1, leafSalt run e.2.2.1⟩,
              e.1, e.2.2.2, bytesToDig root, Ob.a⟩ : Check 256 L)) = Prod.fst := by
      funext e
      simp
    rw [this]
    exact List.map_fst_zip (by simp only [List.length_zip]; omega)
  have hC : (checksOf sy run (bytesToDig root) Ob).map (fun c => (0 * 2 ^ Ob.a + c.j, c.path)) =
      Ob.idx.zip Ob.paths := by
    unfold checksOf
    rw [List.map_map, ← zip4_ends Ob.idx Ob.cols Ob.salts Ob.paths (by omega) (by omega)]
    refine List.map_congr_left fun e _ => ?_
    simp
  have hB : (checksOf sy run (bytesToDig root) Ob).map (fun c => famOf O D K OracleName.leaf c.inp) =
      (leafV (_root_.Fmt.HO O) ⟨Ob.a, W, false, tree⟩ run Ob.idx (Ob.cols.zip Ob.salts)).map
        bytesToDig := by
    unfold checksOf
    rw [leafV_eq, ← zip4_three Ob.idx Ob.cols Ob.salts Ob.paths (by omega), List.map_map,
      List.map_map, List.map_map]
    refine List.map_congr_left fun e he => ?_
    have hes : e.2.2.1 ∈ Ob.salts := (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip he).2).2).1
    have hec : e.2.1 ∈ Ob.cols := (List.of_mem_zip (List.of_mem_zip he).2).1
    have hex : e.1 ∈ Ob.idx := (List.of_mem_zip he).1
    exact famOf_leaf_page O D K (sy e.1 e.2.1) run e.2.2.1 hr tree Ob.a e.1 e.2.1
      (by rw [hsz _ hes, hcw _ hec]; exact hleaf _ _ (hb _ hex) (hcw _ hec))
  have hD : (reads Ob.a (Ob.idx.zip Ob.paths)).take (need Ob.a Ob.idx) =
      Ob.given.map bytesToDig := by
    unfold OpenB.paths
    rw [reads_fill (Dig 256) Ob.a Ob.idx (Ob.given.map bytesToDig) (by rw [List.length_map, hg]),
      List.take_take, Nat.min_self, List.take_of_length_le (by rw [List.length_map, hg])]
  unfold forestV
  rw [hA, hC, hD, hNode_famOf]
  erw [hB]
  refine forest_iff (vP O D) (size_vP O D hO) Ob.a Ob.idx _ Ob.given root
    (length_leafV _ _ _ _ _ (by rw [List.length_zip]; omega)) (le_of_eq hg.symm) ?_ hg32
    (upN_one Ob.a Ob.idx hne hp hb) hroot
  intro x hx
  rw [leafV_eq] at hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact hO _

end

/-! ### What the page's reader returns passes the parser's test on an opening; the verifier's walk
against the reader's root -/

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- ON WHAT THE PAGE'S READER RETURNS FOR AN OPENING, THE COMPILED VERIFIER'S WALK AT THE TYPED
ORACLES THAT O INDUCES SAYS YES EXACTLY IF THE READER'S ROOT IS THE ROOT SENT: for a tree made in a
run; O answers with 32 bytes; the run's value and the root sent have 32 bytes; D spells the symbol
of (x, column), x below 2^a, W elements, as (the tree's number, 2^a + x, the column with its fill).
-/
theorem forestV_reader (hO : ∀ s, (O s).size = 32) (sy : ℕ → List UInt64 → L.Bd)
    (run root : ByteArray) (hr : run.size = 32) (hroot : root.size = 32) (f : _root_.Fmt.Fld)
    (sb a W tree : ℕ) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.OpenOut)
    (e : _root_.Fmt.readOpeningW
        (m := Id) (_root_.Fmt.HO O) D.cfg f sb ⟨a, W, false, tree⟩ run xs b i = some o)
    (hleaf : ∀ x col, x < 2 ^ a → col.length = W →
      D.leaf (sy x col) =
        some (_root_.Fmt.leafPlace tree W (sb / 8),
          2 ^ a + x,
          _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen W sb))) :
    forestV K (famOf O D K) a (bytesToDig root)
        (checksOf sy run (bytesToDig root) ⟨a, xs, o.cols, o.salts, o.given⟩) =
      decide (o.root = root) := by
  obtain ⟨hok, hne⟩ := reader_ok _ _ _ _ _ _ _ _ _ _ e
  rw [forestV_checksOf O D K hO sy run root hr hroot ⟨a, xs, o.cols, o.salts, o.given⟩
        sb W tree hok hne hleaf,
    (reader_id _ _ _ _ _ _ _ _ _ _ e).2.2.2]
  rfl

end

end TypedOracleCompiler.Run.TieTree
