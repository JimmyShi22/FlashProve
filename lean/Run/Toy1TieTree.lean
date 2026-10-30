-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Toy1TieTree.lean: under the hypotheses below, the compiled verifier's walk through a Merkle
opening, at typed oracle functions, agrees with the format page's reader of an opening.

This is the trees' half of the comparison between the compiled verifier at typed oracle functions
and the file reader of the format page (docs/format/FORMAT.md, which comes with the programs, the
C++
implementation that comes with this Lean code; this file has not been held against the page as it
ships, and may differ from it). On what the page's reader returns for an opening,
the verifier's walk says yes exactly if the reader's root is the root that was sent. This holds
under a hypothesis on how a leaf's symbol is spelled, and for trees made in a run (not for stored
trees). The run's value and the sent root must have 32 bytes each; all hypotheses: part 3,
`forestV_reader`. The file holds definitions, statements as theorems, and proofs. It is generic in
the ambient interface L, in the spellings D (`PageD`, Run/CodingFn.lean), in the depth, and in the
oracle O : ByteArray → ByteArray with answers of 32 bytes. The ambient interface is the interface
(`BatchProtocol`, Iop/Batch.lean) that gives the compiled verifier's queries their types.

The compiled verifier (`verifyOneProtocol`, Compile/Batch/Verifier.lean) tests opened leaves forest by
forest. A check (`Check`, in that file) is the data of one test of an opened leaf: the leaf's
input, the leaf's number, a path, the root, and the tree's depth. `runForest` asks the leaf oracle
for the leaves' digests and then walks up by the pruned walk of Hash/Octopus.lean, asking the node
oracle. Typed oracle functions are a family g with one function for each kind of query;
`famOf O D K` (Run/CodingFn.lean) is the family that O induces through the spellings D. A spelling
says what is hashed for typed data; its field `leaf` gives, for a symbol, what stands in the tree's
place of the leaf's label (see `Fmt.leafPlace`), the number that the hash call takes as its index,
and the first bytes of the leaf's hash call. The page's reader is `Fmt.readOpeningW`
(Fmt/Rules7.lean).

1. What the file contains (definitions).
   `forestV K g a rt b`: the verifier's own walk, as a formula.
   `checksOf sy run rt Ob`: the checks that a parser's opening Ob (`OpenB`, Run/ParseBS.lean) calls
     for: position by position the symbol's body, the typed salt (the run's value, then the file's
     salt), and the whole path that `Octopus.fill` makes.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   Bits against bytes. `getD_bitsL`, `bytesToDig_eq`; `dig_bytes`; `bytes_dig`; `bytesToDig_inj`
     (on strings of 32 bytes).
   The typed queries against the page's hash calls, at the family famOf O D K that O induces.
     `famOf_node`, `hNode_famOf`: a node query is the page's vertex at the hash HO O with the start
       D.cfg, read as a digest.
     `famOf_leaf`, `famOf_leaf_page`: under three conditions a leaf query is the page's leaf at
       HO O under the number 164, read as a digest. The first asks that the run's value has 32
       bytes. The second asks that the query's typed salt is (the run's value, then the file's
       salt). The third asks that D spells the query's symbol as these three parts: Fmt.leafPlace
       of the tree's number, the number of the column's words and the number of the salt's words;
       2^a + x; the column with its fill.
   The library's walk on typed digests and on bytes (hP is any function whose values have 32
     bytes).
     `step_dig`, `size_stepF`, `oct_dig`, `size_octF`: on values and given digests of 32 bytes
       each, with as many values as numbers and enough given digests: Octopus.octF (digFn hP) on
       the digests is Octopus.octF hP on the bytes, read as digests.
     `forest_iff`: under the same hypotheses, for a root of 32 bytes, if the opened leaves come to
       one vertex: "every value left is the root" on digests says the same as "the walk on bytes
       ends in the root".
   The verifier's own walk. `det_leavesV`, `det_runForest` (the forest with the one tree: depth a,
     root rt, checks b).
   Put together.
     `forestV_checksOf`: under four conditions `forestV` at famOf O D K on `checksOf` = "the
       library's walk on bytes, at the page's vertex and on the page's leaves, ends in the root".
       The first asks that O answers with 32 bytes. The second asks that the run's value and the
       root have 32 bytes each. The third asks that Ob passes the parser's own test and has a
       position. The fourth asks that, for x below 2^a and columns of W elements, D spells the
       symbol of (x, column) as these three parts: Fmt.leafPlace of the tree's number, the number of
       the column's words and the number of the salt's words; 2^a + x; the column with its fill.
     `reader_ok`: what `Fmt.readOpeningW` (at Id, any hash) returns passes the parser's own test,
       and its list is not empty.
     `forestV_reader`: under the same hypothesis on D's spelling, for a tree that is made in a run
       (not a stored one), an O that answers with 32 bytes, and a run's value and a sent root of 32
       bytes each: if `Fmt.readOpeningW` at HO O, with the start D.cfg of the vertices and the
       run's value as the start of the leaves, returns o, then forestV (famOf O D K) a (the sent
       root, as a digest) (checksOf .. on o's columns, salts and given digests) = decide (o.root =
       the sent root).

4. What is proved elsewhere, what is missing, and what is not claimed.
   Elsewhere (Run/Toy1TieChecks.lean): that the checks which the verifier forms from a parser's
     openings (`checksComp` over all 2^a numbers, at the openings `OpenB.at`) are `checksOf`
     (`checksComp_at`, under its hypotheses); and that a small toy of this library's own
     (Run/ToyQ.lean) spells a leaf as the hypothesis on D wants (`toy_leaf`).
   Elsewhere too, for the generic construction (Run/PlanQTypes.lean, Run/PlanQS.lean): the compiled
     verifier behind the lenient reader is compared with the format's own strict verifier
     (`Fmt.verifyW`, Fmt/M1View.lean); `pi_formula`, `pi_chain`, `pi_half`, `pi_core`, each under
     its hypotheses, are stated in Run/PageIs.lean, whose head names the files of the proofs.
     `forestV_checksOf` is used there (Run/PageIsForest.lean).
   Missing in this file: where the page's reader refuses (too few bytes, a word that is no element)
     there is no o, and nothing is said. The page's reader and the lenient reader
     (Run/ParseLax.lean) refuse there by their own tests.
   Nothing in this file on the chain's queries. No statement on soundness follows, and none on
     privacy.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Sources. The leaf's label (Fmt.leafPlace) was written against the format page (FORMAT.md, R2.1);
this file has not been held against the page as it ships, and may differ from it.


Terms: lean/GLOSSARY.md.
-/
import Run.CodingFn
import Run.CodingBitsLaws
import Run.CodingPage160
import Run.WalkTieProofs
import Compile.Batch.Verifier
import Rom.Cache
import Compile.Batch.SeedCache
import Run.ParseBS
import Compile.OctopusRom

namespace Run.TieTree
open Iop Rom Compile Compile.Batch Octopus Run.WalkTie

/-! ### Bits against bytes: a digest -/

theorem getD_bitsOfByte (x : UInt8) (r : ℕ) (h : r < 8) :
    (bitsOfByte x).getD r false = ((x >>> UInt8.ofNat r) &&& 1 == 1) := by
  unfold bitsOfByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem zero_bit (r : ℕ) (h : r < 8) : (((0 : UInt8) >>> UInt8.ofNat r) &&& 1 == 1) = false := by
  interval_cases r <;> decide

theorem getD_bitsL :
    ∀ (l : List UInt8) (i : ℕ),
      (bitsL l).getD i false = (((l.getD (i / 8) 0) >>> UInt8.ofNat (i % 8)) &&& 1 == 1)
  | [], i => by
    rw [show bitsL [] = [] from rfl, List.getD_nil,
      List.getD_nil, zero_bit _ (Nat.mod_lt _ (by decide))]
  | x :: l, i => by
    show (bitsOfByte x ++ bitsL l).getD i false = _
    by_cases h : i < 8
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [length_bitsOfByte]; exact h),
        ← List.getD_eq_getElem?_getD, getD_bitsOfByte x i h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · have h8 : 8 ≤ i := Nat.le_of_not_lt h
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [length_bitsOfByte]; exact h8),
        ← List.getD_eq_getElem?_getD, length_bitsOfByte, getD_bitsL l (i - 8)]
      have e1 : i / 8 = (i - 8) / 8 + 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2, List.getD_cons_succ]

theorem bytesToDig_eq (b : ByteArray) : bytesToDig b = digOf (bytesToBits b) := by
  funext i
  show _root_.Fmt.bitAt b i.val = (bitsL b.data.toList).getD i.val false
  rw [getD_bitsL]
  unfold _root_.Fmt.bitAt
  rw [_root_.Fmt.byteAt_eq]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- 32 bytes, as a digest, as bytes -/
theorem dig_bytes (b : ByteArray) (h : b.size = 32) : digToBytes (bytesToDig b) = b := by
  rw [bytesToDig_eq]; exact digToBytes_digOf b h

/-- a digest, as bytes, as a digest -/
theorem bytes_dig (d : Dig 256) : bytesToDig (digToBytes d) = d := by
  rw [bytesToDig_eq, bits_digToBytes, digOf_ofFn]

theorem bytesToDig_inj {a b : ByteArray} (ha : a.size = 32)
    (hb : b.size = 32) (h : bytesToDig a = bytesToDig b) : a = b := by
  rw [← dig_bytes a ha, ← dig_bytes b hb, h]

/-! ### The typed node query and the typed leaf query against the page's calls -/

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- A node query is the page's vertex. -/
theorem famOf_node (q : Bits × Bits) :
    famOf O D K .node q =
      bytesToDig
        (_root_.Fmt.vertexW (m := Id) (_root_.Fmt.HO O) D.cfg
          (bitsToBytes q.1) (bitsToBytes q.2)) := rfl

/-- a leaf query, as the coding reads it -/
theorem famOf_leaf (s : SymAny (shapeOf L tg)) (salt : Bits) :
    famOf O D K .leaf ⟨some (.inr ⟨tg, s⟩), salt⟩ =
      bytesToDig
        (_root_.Fmt.HO O 164 (D.leaf s).1 (D.leaf s).2.1 (bitsToBytes (salt.take 256))
          ((D.leaf s).2.2 ++ bitsToBytes (salt.drop 256))) := by
  have e : leafCall D ⟨some (.inr ⟨tg, s⟩), salt⟩ =
      some ⟨0, 164, (D.leaf s).1, (D.leaf s).2.1, bitsToBytes (salt.take 256),
          (D.leaf s).2.2 ++ bitsToBytes (salt.drop 256)⟩ := by
    show (castTag (F := fun t => SymAny (shapeOf L t)) tg tg s).map _ = _
    rw [castTag_self]
    rfl
  show ansOf O (leafCall D ⟨some (.inr ⟨tg, s⟩), salt⟩) = _
  rw [e]
  rfl

/-- A leaf query is the page's leaf, if the run's value has 32 bytes (`hr`), the typed salt is the
run's value and then the file's salt, and the spelling of the symbol is (`hs`): the tree's number
with the numbers of the column's and the salt's words above it (`Fmt.leafPlace`), 2^a + x, the
column with its fill. -/
theorem famOf_leaf_page (s : SymAny (shapeOf L tg)) (run fsalt : ByteArray) (hr : run.size = 32)
    (tree a x : ℕ) (col : List UInt64)
    (hs : D.leaf s =
      (_root_.Fmt.leafPlace tree col.length (fsalt.size / 8),
        2 ^ a + x,
        _root_.Fmt.colBytes col ++
          _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length fsalt.size))) :
    famOf O D K .leaf ⟨some (.inr ⟨tg, s⟩), bytesToBits run ++ bytesToBits fsalt⟩ =
      bytesToDig (_root_.Fmt.leafW (m := Id) (_root_.Fmt.HO O) 164 tree a x run col fsalt) := by
  have hl : (bytesToBits run).length = 256 := by rw [length_bytesToBits, hr]
  rw [famOf_leaf, hs, List.take_left' hl, List.drop_left' hl,
    bitsToBytes_bytesToBits, bitsToBytes_bytesToBits]
  rfl

end

/-! ### The library's walk on digests and on 32 bytes -/

section
variable (hP : ByteArray → ByteArray → ByteArray) (h32 : ∀ l r, (hP l r).size = 32)

/-- the vertex function on typed digests that hP induces -/
def digFn (a b : Dig 256) : Dig 256 := bytesToDig (hP (digToBytes a) (digToBytes b))

theorem step_dig :
    ∀ (js : List ℕ) (v s : List ByteArray), v.length = js.length → need1 js ≤ s.length →
      (∀ x ∈ v, x.size = 32) → (∀ x ∈ s, x.size = 32) →
      stepF (digFn hP) js (v.map bytesToDig) (s.map bytesToDig) = (stepF hP js v s).map bytesToDig
  | [], _, _, _, _, _, _ => rfl
  | [i], [a], x :: g, _, _, hv, hs => by
    have ha := hv a (by simp)
    have hx := hs x (by simp)
    show [lone (M := Id) (digFn hP) i (bytesToDig a) (bytesToDig x)] =
      [bytesToDig (lone (M := Id) hP i a x)]
    unfold lone digFn
    split <;> (rw [dig_bytes a ha, dig_bytes x hx]; rfl)
  | i :: j :: l, a :: b :: v, s, hl, hn, hv, hs => by
    have ha := hv a (by simp)
    have hb := hv b (by simp)
    have hl' : v.length = l.length := by simpa using hl
    by_cases h : sib i j
    · have hn' : need1 l ≤ s.length := by
        have e : need1 (i :: j :: l) = need1 l := by rw [need1, if_pos h]
        exact e ▸ hn
      have ih := step_dig l v s hl' hn' (fun x hx => hv x (by simp [hx])) hs
      simp only [stepF, stepC, if_pos h, List.map_cons] at ih ⊢
      show digFn hP (bytesToDig a) (bytesToDig b) ::
          stepC (M := Id) (digFn hP) l (v.map bytesToDig) (s.map bytesToDig) =
        bytesToDig (hP a b) :: (stepC (M := Id) hP l v s).map bytesToDig
      refine congrArg₂ List.cons ?_ ih
      unfold digFn
      rw [dig_bytes a ha, dig_bytes b hb]
    · have hn1 : need1 (i :: j :: l) = 1 + need1 (j :: l) := by rw [need1, if_neg h]
      obtain ⟨x, g, rfl⟩ : ∃ x g, s = x :: g := by
        cases s with
        | nil => simp [hn1] at hn
        | cons x g => exact ⟨x, g, rfl⟩
      have hx := hs x (by simp)
      have hn' : need1 (j :: l) ≤ g.length := by
        rw [hn1] at hn
        simp only [List.length_cons] at hn
        omega
      have ih := step_dig (j :: l) (b :: v) g (by simpa using hl') hn'
        (fun y hy => hv y (by simp only [List.mem_cons] at hy ⊢; tauto))
        (fun y hy => hs y (by simp [hy]))
      simp only [stepF, List.map_cons] at ih ⊢
      rw [stepC, stepC, if_neg h, if_neg h]
      show lone (M := Id) (digFn hP) i (bytesToDig a) (bytesToDig x) ::
          stepC (M := Id) (digFn hP) (j :: l)
            (bytesToDig b :: v.map bytesToDig) (g.map bytesToDig) =
        bytesToDig (lone (M := Id) hP i a x) ::
          (stepC (M := Id) hP (j :: l) (b :: v) g).map bytesToDig
      refine congrArg₂ List.cons ?_ ih
      unfold lone digFn
      split <;> rw [dig_bytes a ha, dig_bytes x hx]

include h32 in
theorem size_stepF : ∀ (js : List ℕ) (v s : List ByteArray), ∀ x ∈ stepF hP js v s, x.size = 32
  | [], _, _, x, hx => by cases hx
  | [i], v, s, x, hx => by
    have e : stepF hP [i] v s = [loneF hP i (v.headD default) (s.headD default)] := rfl
    rw [e, List.mem_singleton] at hx
    subst hx
    unfold loneF
    split <;> exact h32 _ _
  | i :: j :: l, v, s, x, hx => by
    by_cases h : sib i j
    · have e : stepF hP (i :: j :: l) v s =
          hP (v.headD default) (v.tail.headD default) :: stepF hP l v.tail.tail s := by
        simp only [stepF]
        rw [stepC, if_pos h]
        rfl
      rw [e, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h32 _ _
      · exact size_stepF l _ _ x hx
    · have e : stepF hP (i :: j :: l) v s =
          loneF hP i (v.headD default) (s.headD default) :: stepF hP (j :: l) v.tail s.tail := by
        simp only [stepF]
        rw [stepC, if_neg h]
        rfl
      rw [e, List.mem_cons] at hx
      rcases hx with rfl | hx
      · unfold loneF
        split <;> exact h32 _ _
      · exact size_stepF (j :: l) _ _ x hx

include h32 in
/-- d levels: under the hypotheses of its statement, the library's walk on typed digests is its
walk on 32 bytes. -/
theorem oct_dig :
    ∀ (d : ℕ) (js : List ℕ) (v s : List ByteArray), v.length = js.length → need d js ≤ s.length →
      (∀ x ∈ v, x.size = 32) → (∀ x ∈ s, x.size = 32) →
      Octopus.octF (digFn hP) d js (v.map bytesToDig) (s.map bytesToDig) =
        (Octopus.octF hP d js v s).map bytesToDig
  | 0, _, _, _, _, _, _, _ => rfl
  | d + 1, js, v, s, hl, hn, hv, hs => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hn
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hn
      omega
    show Octopus.octF (digFn hP) d (up js)
        (stepF (digFn hP) js (v.map bytesToDig) (s.map bytesToDig))
        ((s.map bytesToDig).drop (need1 js)) =
      (Octopus.octF hP d (up js) (stepF hP js v s) (s.drop (need1 js))).map bytesToDig
    rw [step_dig hP js v s hl h1 hv hs, ← List.map_drop]
    exact oct_dig d (up js) _ _ (length_stepF hP js v s) h2 (size_stepF hP h32 js v s)
      (fun x hx => hs x (List.mem_of_mem_drop hx))

include h32 in
theorem size_octF :
    ∀ (d : ℕ) (js : List ℕ) (v s : List ByteArray),
      (∀ x ∈ v, x.size = 32) → ∀ x ∈ Octopus.octF hP d js v s, x.size = 32
  | 0, _, _, _, hv, x, hx => hv x hx
  | d + 1, js, v, s, _, x, hx =>
    size_octF d (up js) (stepF hP js v s) (s.drop (need1 js)) (size_stepF hP h32 js v s) x hx

include h32 in
/-- Under the hypotheses of its statement, the forest's test on typed digests is "the walk on bytes
ends in the root", for one tree whose opened leaves come to one vertex (`hu`). -/
theorem forest_iff (d : ℕ) (js : List ℕ) (v s : List ByteArray) (root : ByteArray)
    (hl : v.length = js.length) (hn : need d js ≤ s.length) (hv : ∀ x ∈ v, x.size = 32)
    (hs : ∀ x ∈ s, x.size = 32) (hu : (upN d js).length = 1) (hr : root.size = 32) :
    (((upN d js).zip (Octopus.octF (digFn hP) d js (v.map bytesToDig) (s.map bytesToDig))).all
        fun m => decide (m.2 = bytesToDig root)) =
      decide ((Octopus.octF hP d js v s).headD default = root) := by
  rw [oct_dig hP h32 d js v s hl hn hv hs]
  have ho : (Octopus.octF hP d js v s).length = 1 := (length_octF hP d js v s hl).trans hu
  have hz := size_octF hP h32 d js v s hv
  revert ho hz
  generalize Octopus.octF hP d js v s = out
  intro ho hz
  obtain ⟨u, hu'⟩ := List.length_eq_one_iff.1 hu
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.1 ho
  rw [hu']
  have h1 : r.size = 32 := hz r (by simp)
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, List.headD_cons]
  by_cases e : r = root
  · simp [e]
  · have : bytesToDig r ≠ bytesToDig root := fun h => e (bytesToDig_inj h1 hr h)
    simp [e, this]

end

/-! ### The typed family that an oracle induces, and the verifier's own walk -/

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- the page's vertex at the oracle O -/
def vP (l r : ByteArray) : ByteArray := _root_.Fmt.HO O 166 0 0 D.cfg (l ++ r)

theorem size_vP (hO : ∀ s, (O s).size = 32) (l r : ByteArray) : (vP O D l r).size = 32 := hO _

/-- The node oracle as a function of two digests. -/
theorem hNode_famOf : Compile.Batch.Seed.hNode (famOf O D K) = digFn (vP O D) := by
  funext a b
  unfold Compile.Batch.Seed.hNode digFn vP digToBytes
  rw [famOf_node]
  dsimp only [_root_.Fmt.vertexW]

/-- The forest's part of the verifier's run at a family g of typed oracle functions: one tree of
depth a with the root rt; b: the checks. -/
def forestV (g : Fam (spec 256 K L)) (a : ℕ) (rt : Dig 256) (b : List (Check 256 L)) : Bool :=
  ((upN a (b.map fun c => 0 * 2 ^ a + c.j)).zip
      (Octopus.octF (Compile.Batch.Seed.hNode g) a
        (b.map fun c => 0 * 2 ^ a + c.j) (b.map fun c => g OracleName.leaf c.inp)
        ((reads a (b.map fun c => (0 * 2 ^ a + c.j, c.path))).take
          (need a (b.map fun c => 0 * 2 ^ a + c.j))))).all
    fun m => decide (m.2 = rt)

theorem det_leavesV (g : Fam (spec 256 K L)) :
    ∀ es : List (ℕ × Check 256 L), (leavesV (K := K) es).det g = es.map fun e => g OracleName.leaf e.2.inp
  | [] => rfl
  | e :: es => by
    show ((askTypedOracle (L := L) (K := K) OracleName.leaf e.2.inp).bind fun d =>
        (leavesV es).bind fun r => OComp.pure (d :: r)).det g = _
    rw [OComp.det_bind, OComp.det_bind, det_leavesV g es]
    rfl

/-- `forestV` is the verifier's own walk through one forest (Compile/Batch/Verifier.lean:
`runForest`, on the digests that it reads off the paths), run at g. -/
theorem det_runForest (g : Fam (spec 256 K L)) (a : ℕ) (rt : Dig 256) (b : List (Check 256 L)) :
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

/-- the checks that a parser's opening calls for: position by position, the symbol's body, the
typed salt (the run's value, then the file's salt), the whole path -/
def checksOf (sy : ℕ → List UInt64 → SymAny (shapeOf L tg)) (run : ByteArray)
    (rt : Dig 256) (Ob : OpenB) : List (Check 256 L) :=
  (Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))).map fun e =>
    ⟨⟨some (.inr ⟨tg, sy e.1 e.2.1⟩), leafSalt run e.2.2.1⟩, e.1, e.2.2.2, rt, Ob.a⟩

end

theorem leafV_eq (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
    (sh : _root_.Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)), leafV h sh start xs cs =
      (xs.zip cs).map fun e =>
        h (_root_.Fmt.leafNo sh.stored) (_root_.Fmt.leafPlace sh.tree e.2.1.length (e.2.2.size / 8))
          (2 ^ sh.a + e.1) start (_root_.Fmt.leafBytes e.2.1 e.2.2)
  | [], _ => by simp [leafV]
  | _ :: _, [] => by simp [leafV]
  | x :: xs, c :: cs => by simp [leafV, leafV_eq h sh start xs cs]

/-- what the parser's test on an opening says -/
theorem ok_spec (Ob : OpenB) (sb W : ℕ) (h : Ob.ok sb W = true) :
    Ob.cols.length = Ob.idx.length ∧
    Ob.salts.length = Ob.idx.length ∧
    (∀ s ∈ Ob.salts, s.size = sb) ∧
    Ob.given.length = need Ob.a Ob.idx ∧
    (∀ d ∈ Ob.given, d.size = 32) := by
  unfold OpenB.ok at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h3, h4, h6, h7, h8⟩

/-! ### Put together: the verifier's walk on a parser's opening, and the walk on bytes -/

theorem incr_pairwise : ∀ l : List ℕ, incr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | i :: j :: l, h => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := incr_pairwise (j :: l) h.2
    refine List.pairwise_cons.2 ⟨?_, hp⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · exact lt_trans h.1 ((List.pairwise_cons.1 hp).1 z hz)

theorem ok_list (Ob : OpenB) (sb W : ℕ) (h : Ob.ok sb W = true) :
    Ob.idx.Pairwise (· < ·) ∧ (∀ x ∈ Ob.idx, x < 2 ^ Ob.a) ∧ ∀ c ∈ Ob.cols, c.length = W := by
  unfold OpenB.ok at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, -⟩, -⟩, -⟩ := h
  exact ⟨incr_pairwise _ h1, h2, h5⟩

theorem zip4_three {α β γ δ : Type} (a : List α) (b : List β) (c : List γ)
    (d : List δ) (h : c.length ≤ d.length) :
    (a.zip (b.zip (c.zip d))).map (fun e => (e.1, e.2.1, e.2.2.1)) = a.zip (b.zip c) := by
  conv_rhs => rw [← List.map_fst_zip (l₁ := c) (l₂ := d) h, List.zip_map_right, List.zip_map_right]
  exact List.map_congr_left fun _ _ => rfl

theorem zip4_ends {α β γ δ : Type} (a : List α) (b : List β) (c : List γ) (d : List δ)
    (h1 : d.length ≤ c.length) (h2 : d.length ≤ b.length) :
    (a.zip (b.zip (c.zip d))).map (fun e => (e.1, e.2.2.2)) = a.zip d := by
  have e1 : (c.zip d).map Prod.snd = d := List.map_snd_zip h1
  have e2 : (b.zip (c.zip d)).map Prod.snd = c.zip d :=
    List.map_snd_zip (by rw [List.length_zip]; omega)
  conv_rhs => rw [← e1, ← e2, List.map_map, List.zip_map_right]
  rfl

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- Under the hypotheses of its statement (in words: the head, `forestV_checksOf`), the verifier's
walk on the checks that a parser's opening calls for says yes exactly if the library's walk on
bytes, at the page's vertex and on the page's leaves, ends in the root. O answers with 32 bytes;
sy: how a position and a column become a symbol; D spells that symbol as the page wants. -/
theorem forestV_checksOf (hO : ∀ s, (O s).size = 32) (sy : ℕ → List UInt64 → SymAny (shapeOf L tg))
    (run root : ByteArray) (hr : run.size = 32) (hroot : root.size = 32) (Ob : OpenB)
    (sb W tree : ℕ) (hok : Ob.ok sb W = true) (hne : Ob.idx ≠ [])
    (hleaf : ∀ x col, x < 2 ^ Ob.a → col.length = W →
      D.leaf (sy x col) =
        (_root_.Fmt.leafPlace tree W (sb / 8),
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
            (⟨⟨some (.inr ⟨tg, sy e.1 e.2.1⟩), leafSalt run e.2.2.1⟩,
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

/-! ### The verifier's walk against the reader's root -/

theorem rdMany_all {α : Type} (r : _root_.Fmt.Rd α) (P : α → Prop)
    (hP : ∀ b i x j, r b i = some (x, j) → P x) :
    ∀ (n : ℕ) (b : ByteArray) (i : ℕ) (l : List α) (k : ℕ),
      _root_.Fmt.rdMany r n b i = some (l, k) → ∀ x ∈ l, P x
  | 0, _, _, l, k, h, x, hx => by
    simp only [_root_.Fmt.rdMany, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hx
    cases hx
  | n + 1, b, i, l, k, h, x, hx => by
    simp only [_root_.Fmt.rdMany] at h
    split at h
    · rename_i y j e1
      split at h
      · rename_i l' k' e2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1] at hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hP _ _ _ _ e1
        · exact rdMany_all r P hP n b j l' k' e2 x hx
      · cases h
    · cases h

theorem rdBytes_size (n : ℕ) (b : ByteArray) (i : ℕ) (x : ByteArray) (j : ℕ)
    (h : _root_.Fmt.rdBytes n b i = some (x, j)) : x.size = n := by
  unfold _root_.Fmt.rdBytes _root_.Fmt.slice at h
  split at h
  · rename_i hle
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ByteArray.size_extract]
    omega
  · cases h

theorem listOK_incr (a : ℕ) : ∀ xs : List ℕ, _root_.Fmt.listOK a xs = true → incr xs = true
  | [_], _ => rfl
  | x :: y :: tl, h => by
    simp only [_root_.Fmt.listOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1, listOK_incr a (y :: tl) h.2⟩

/-- What the page's reader returns passes the parser's own test, whatever the hash. -/
theorem reader_ok (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)
    (f : _root_.Fmt.Fld) (sb : ℕ) (sh : _root_.Fmt.Shape) (start : ByteArray) (xs : List ℕ)
    (b : ByteArray) (i : ℕ) (o : _root_.Fmt.OpenOut)
    (e : _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    (⟨sh.a, xs, o.cols, o.salts, o.given⟩ : OpenB).ok sb sh.W = true ∧ xs ≠ [] := by
  obtain ⟨r1, r2, r3, -⟩ := reader_id h cfg f sb sh start xs b i o e
  unfold _root_.Fmt.readOpeningW at e
  split at e
  · rename_i hok
    have hl : _root_.Fmt.listOK sh.a xs = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).1
    obtain ⟨hne, -, hb⟩ := listOK_spec sh.a xs hl
    split at e
    · cases e
    · rename_i cs given next ep
      have hparts : (∀ c ∈ cs, c.1.length = sh.W ∧ c.2.size = sb) ∧ ∀ d ∈ given, d.size = 32 := by
        unfold _root_.Fmt.rdOpening _root_.Fmt.rdPair at ep
        split at ep
        · rename_i cs' j e1
          split at ep
          · rename_i g' k e2
            simp only [Option.some.injEq, Prod.mk.injEq] at ep
            obtain ⟨⟨rfl, rfl⟩, -⟩ := ep
            refine ⟨rdMany_all _ (fun c => c.1.length = sh.W ∧ c.2.size = sb) ?_ _ _ _ _ _ e1,
              rdMany_all _ (fun d => d.size = 32)
                (fun b i x j hx => rdBytes_size 32 b i x j hx) _ _ _ _ _ e2⟩
            intro b' i' x j' hx
            unfold _root_.Fmt.rdPair at hx
            split at hx
            · rename_i col j1 e3
              split at hx
              · rename_i st j2 e4
                simp only [Option.some.injEq, Prod.mk.injEq] at hx
                rw [← hx.1]
                exact ⟨rdMany_length _ _ _ _ _ _ e3, rdBytes_size _ _ _ _ _ e4⟩
              · cases hx
            · cases hx
          · cases ep
        · cases ep
      have e' : (_root_.Fmt.walkW (m := Id) (fun _ _ l r => h 166 0 0 cfg (l ++ r))
              _root_.Fmt.takeGiven sh.a
              (_root_.Fmt.leavesW (m := Id) h sh start xs cs) (given, []) []).map
            (fun r =>
              (⟨cs.map (·.1), cs.map (·.2), given, r.1,
                r.2.2 ++ r.2.1.2, next⟩ : _root_.Fmt.OpenOut)) = some o := e
      obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 e'
      subst hp
      refine ⟨?_, hne⟩
      unfold OpenB.ok
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨⟨⟨listOK_incr _ _ hl, hb⟩, r1⟩, r2⟩, ?_⟩, ?_⟩, r3⟩, hparts.2⟩
      · intro c hc
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
        exact (hparts.1 y hy).1
      · intro s hs
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
        exact (hparts.1 y hy).2
  · cases e

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) {tg : Tag} (D : PageD L tg) (K : ℕ)

/-- On what the page's reader returns for an opening (`e`: at the hash HO O, the vertices' start
D.cfg, the leaves' start the run's value), the compiled verifier's walk at the typed oracles that O
induces says yes exactly if the reader's root is the root sent: for a tree made in a run; O answers
with 32 bytes; the run's value and the root sent have 32 bytes; D spells the symbol of (x, column),
x below 2^a, W elements, as (`Fmt.leafPlace` of the tree's number, the number of the column's words
and the number of the salt's words; 2^a + x; the column with its fill). -/
theorem forestV_reader (hO : ∀ s, (O s).size = 32) (sy : ℕ → List UInt64 → SymAny (shapeOf L tg))
    (run root : ByteArray) (hr : run.size = 32) (hroot : root.size = 32) (f : _root_.Fmt.Fld)
    (sb a W tree : ℕ) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.OpenOut)
    (e : _root_.Fmt.readOpeningW
        (m := Id) (_root_.Fmt.HO O) D.cfg f sb ⟨a, W, false, tree⟩ run xs b i = some o)
    (hleaf : ∀ x col, x < 2 ^ a → col.length = W →
      D.leaf (sy x col) =
        (_root_.Fmt.leafPlace tree W (sb / 8),
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

end Run.TieTree
