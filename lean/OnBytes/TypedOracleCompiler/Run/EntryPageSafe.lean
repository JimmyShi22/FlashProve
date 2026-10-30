-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryPageSafe.lean: THE WRITING SIDE OF THE PAGE OF AN ENTRY's JUDGE, FOR THE
EVALUATOR: the string of a leaf query, a vertex query and a chain query under either tag, by
functions whose only data are the description, the pins, `back` and the query; the interface stands
in their types alone; each is tied to `EntryPage.implE`'s code by an equation at EVERY query; and
the family over the oracle made from Lean's BLAKE2b that they give.

WHY. OnBytes/TypedOracleCompiler/Run/EntryPageRun.lean makes the page a term that Lean's compiler takes. It does not
come home: at a made-up description of three rounds the first evaluation of a partial code ended
"out of memory" within seconds (measured). Compiled Lean is strict, and an interface
(`BatchProtocolWithLeafBody`) holds shapes, so rounds, and a round carries the list of all its verifier's messages. Every
general definition of the page takes the interface as a value, stated or unstated, and this compiler
builds the value at the call, though no body looks at it (so the trials read: the first partial code
that has the interface among its arguments died, the library's code of vertices, which has none,
came home). The library knows the trap (Run/CodingFnThin.lean's head). Here the texts of the writing
side are said once more AT the entry's interface, with the description, the way `early` and the
seeds' entry as the only data: by the text no definition on the path of a run takes a value of the
type `BatchProtocolWithLeafBody`, `InteractiveOracleProof`, `Shape` or `Round`, or catches one; `back` is an argument, and whoever gives it
owes the same. The reading side (the inverse) is not said again: a run does not read strings back.
The sibling is a second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `leafS`: a leaf query's string, where the code of leaves writes; `leafS_eq`;
 - `selL`, `restS`, `tupS`, `toTupS`, `linkS`: a chain query under the link's tag, with a block;
   `linkS_eq`: it is what `EntryPageRun.fbLinkT` writes, at the computable tests;
 - `selS`, `p1c`, `rcS1`, `tupT`, `toTupT`, `seedS`: a chain query under the seeds' tag; `seedS_eq`;
 - `codeLeaf`, `codeNode`, `codeLink`, `codeSeed`: the string of EVERY such query: the partial
   code's string where it writes, else the byte 2 and `back`'s string; `codeLeaf_eq`, `codeNode_eq`,
   `codeLink_eq`, `codeSeed_eq`: each is `implE`'s code;
 - `toBytesT`, `hashS`: the realised oracle at a string of bits, as bytes, by the library's looping
   way from bits to bytes; `hashS_eq`;
 - `famSafe`: the family: at these four kinds of query the blocks' strings are hashed first, as
   bytes, then decoded; at every other oracle the plain family of EntryPageRun.lean, which, by the
   text of the run's forms, a run of the judge does not ask: no theorem says so; `famSafe_eq`: IT IS
   `readBlocks (implE …) Run.oBits`, at every oracle and query.

Main definitions: `leafS`, `linkS`, `seedS`, `codeLeaf`, `codeNode`, `codeLink`, `codeSeed`,
`famSafe`.
Main theorems: `linkS_eq`, `seedS_eq`, `codeLeaf_eq`, `codeNode_eq`, `codeLink_eq`, `codeSeed_eq`,
`famSafe_eq`.

Not claimed. THAT IT COMES HOME is a fact of a run, not a theorem. How often a
hash is computed. At the other oracles `famSafe` is the plain family, which does not come home: if a
run asked one, it would end without a verdict, not with a false one. BEHIND THE BYTE 2 `back` MAY
WRITE A NUMBER IN UNARY (a stored leaf's position, a nonce): a query that the partial codes do not
write may be long to spell, or end the evaluator's stack. Strings are lists of bits; a message's
code is nested once for each item, so a round of many thousand items may end the evaluator's stack.
Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryPageRun
import OnBytes.TypedOracleCompiler.Run.KeyLeaves
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
import Run.OracleBits
import Run.CodingBitsT

set_option autoImplicit false

namespace TypedOracleCompiler.Run.EntryPageSafe
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.EntryPageRun
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.Chain162G TypedOracleCompiler.Run.KeyRanges TypedOracleCompiler.Strings
open TypedOracleCompiler.Run.EntryFirst (YE first0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## Leaves -/

/-- A leaf query's string, of body and typed salt. cfg: the start that a stored leaf must have;
n: the bits of a file's salt. -/
def leafS (cfg : ByteArray) (n : ℕ) (body : List Bool) (salt : Bits) : Option (List Bool) :=
  if (if storedLike body then bitsToBytes (salt.take 256) == cfg else true) = true then
    (pSalted pre33 n (pBody ok2)).put (body, salt)
  else none

/-- It is what the code of leaves writes. -/
theorem leafS_eq {I X : Type} (L : _root_.Iop.BatchProtocol I X) (cfg : ByteArray) (n : ℕ)
    (q : LeafIn (strung L)) : leafS cfg n q.body q.salt = (KeyLeaves.leafCode L n cfg).put q := rfl

variable {Sd : Type} [DecidableEq Sd] (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry) (dd : Sd)
  (P : PinsE D early e) (K : ℕ)

/-! ## The link's chain -/

/-- Of the link's first query: (pd, roots and answers, salt). -/
def selL (q : FbIn 256 (Le D early e) .link) :
    Option (Dig 256 × Option (Dig 256 × YE) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [r₀, r₁] (some x) salt, [] =>
      if (Tests.run D early e dd).tL q.plain = true ∧ (Tests.run D early e dd).tD x.2 = true then
        some (P.pd, some (r₀, (x.1.1, (r₁, x.1.2))), salt) else none
  | _, _, _ => none

/-- The code of what stands behind label and index. -/
def restS (l j : ℕ) :
    PCode ((List (Dig 256) × PlainPart (shE D early e) (annOf (Le D early e) .link)) × ℕ) :=
  match backE D.ds.length P.l l j with
  | some i =>
      (rcE D early e i).ins (pKwc (kindE D i) (workE D i)) 64 64 (pKwc_len _ _) (rcE_ge D early e i)
  | none => PCode.empty _

/-- The code of the tuple. -/
def tupS : PCode (TupG (Le D early e) .link) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        pLab.cons 64 pLab_len fun l =>
          pWord.cons 64 pWord_len fun j => restS D early e P l j)

/-- A later round's query with a block, as a tuple. -/
def toTupS (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) :
    Option (TupG (Le D early e) .link) :=
  match selF2 q.head with
  | some ρ =>
      if onE D.ds.length q.round = true then
        some (decide ((blockTo (ordE D q.round) K j).val % 2 = 1), ρ, P.l, q.round,
          ((q.rt, q.plain), (blockTo (ordE D q.round) K j).val / 2))
      else none
  | none => none

/-- A chain query under the link's tag, with a block: its string, where the page's partial code
writes. -/
def linkS (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) : Option (List Bool) :=
  if q.round = 0 then
    if j = Fin.last K then (selL D early e dd P q).bind (first0E P.l).put else none
  else (toTupS D early e P K q j).bind (tupS D early e P).put

/-- It is what the page's code of chain queries under the link's tag writes. -/
theorem linkS_eq (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) :
    linkS D early e dd P K q j = (fbLinkT (Tests.run D early e dd) P K).put (q, j) := by
  unfold linkS
  by_cases h0 : q.round = 0
  · rw [if_pos h0]
    refine Eq.trans ?_ (split_true _ _ _ _ (q, j) (decide_eq_true h0)).symm
    show _ = (selT K (q, j)).bind (e0T (Tests.run D early e dd) P).put
    unfold selT
    by_cases hj : j = Fin.last K
    · rw [if_pos hj, if_pos hj]
      rfl
    · rw [if_neg hj, if_neg hj]
      rfl
  · rw [if_neg h0]
    refine Eq.trans ?_ (split_false _ _ _ _ (q, j) (decide_eq_false h0)).symm
    rfl

/-! ## The seeds' chain -/

/-- Of the seeds' chain's first query: (the zero digest, the root, no salt). -/
def selS (q : FbIn 256 (Le D early e) .test) : Option (Dig 256 × Option (Dig 256) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [cm] none [], [] =>
      if (Tests.run D early e dd).t0 q.plain = true then some (FirstName.zeroPd, some cm, [])
      else none
  | _, _, _ => none

/-- The drawing round's fixed plain part, as a plain term. -/
def p1c : PlainPart (shapeOf (Le D early e) .test) (annOf (Le D early e) .test) := .inr (.inl (.inr ()))

/-- The code of a round's roots and plain part on the seeds' chain: `SeedRound.rcS`'s text. -/
def rcS1 (i : ℕ) :
    PCode (List (Dig 256) × PlainPart (shapeOf (Le D early e) .test) (annOf (Le D early e) .test)) where
  put := fun y =>
    if i = 1 ∧ y.1.isEmpty = true ∧ (Tests.run D early e dd).t1 y.2 = true then
      some SeedRound.word0 else none
  parse := fun s => if i = 1 ∧ s = SeedRound.word0 then some ([], p1c D early e) else none
  parse_put := (SeedRound.rcS (Le D early e) .test (p1S (L := Le D early e) .test D.C e _ id)
    (Tests.run D early e dd).t1 (Tests.run D early e dd).h1 i).parse_put
  put_parse := (SeedRound.rcS (Le D early e) .test (p1S (L := Le D early e) .test D.C e _ id)
    (Tests.run D early e dd).t1 (Tests.run D early e dd).h1 i).put_parse

/-- The code of the tuple, on the seeds' chain. -/
def tupT : PCode (Tup (Le D early e) .test) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        PCode.pre (bytesToBits (_root_.Fmt.u64n (162 + 65536 * _root_.Fmt.recordLabel)))
          (pWord.cons 64 pWord_len fun i =>
            (rcS1 D early e dd i).ins (pKwc _root_.Fmt.Kind.seeds.num 0) 64 64 (pKwc_len _ _)
              (SeedRound.rcS_len (Le D early e) .test (p1S (L := Le D early e) .test D.C e _ id)
                (Tests.run D early e dd).t1 (Tests.run D early e dd).h1 i)))

/-- A later round's query with a block, as a tuple, on the seeds' chain. -/
def toTupT (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) :
    Option (Tup (Le D early e) .test) :=
  match q.round, q.head with
  | i + 1, .f2 none ρ =>
      some (decide ((blockTo (decide ((0 : ℕ) ≠ 0)) K j).val % 2 = 1), ρ, i + 1,
        ((q.rt, q.plain), (blockTo (decide ((0 : ℕ) ≠ 0)) K j).val / 2))
  | _, _ => none

/-- A chain query under the seeds' tag, with a block: its string, where the page's partial code
writes. -/
def seedS (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) : Option (List Bool) :=
  if q.round = 0 then
    if j = Fin.last K then
      (selS D early e dd q).bind (FirstName.first0N P.rest _root_.Fmt.recordLabel).put
    else none
  else (toTupT D early e K q j).bind (tupT D early e dd).put

theorem selS_eq (q : FbIn 256 (Le D early e) .test) :
    selS D early e dd q =
      FirstName.selN (Le D early e) .test (Tests.run D early e dd).t0 FirstName.zeroPd q := by
  obtain ⟨round, head, rt, plain⟩ := q
  cases round <;> cases head <;> (try rfl)
  all_goals
    rename_i cms x salt
    rcases cms with _ | ⟨cm, _ | ⟨c2, l⟩⟩ <;> cases x <;> cases salt <;> cases rt <;> rfl

theorem rcS1_eq (i : ℕ) :
    rcS1 D early e dd i = SeedRound.rcS (Le D early e) .test
      (p1S (L := Le D early e) .test D.C e _ id) (Tests.run D early e dd).t1
      (Tests.run D early e dd).h1 i := rfl

theorem tupT_eq :
    tupT D early e dd = pTup (SeedRound.chainDS (Le D early e) .test
      (p1S (L := Le D early e) .test D.C e _ id) (Tests.run D early e dd).t1
      (Tests.run D early e dd).h1) := rfl

theorem toTupT_eq (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) :
    toTupT D early e K q j = toTup (SeedRound.chainDS (Le D early e) .test
      (p1S (L := Le D early e) .test D.C e _ id) (Tests.run D early e dd).t1
      (Tests.run D early e dd).h1) K (q, j) := by
  obtain ⟨round, head, rt, plain⟩ := q
  cases round <;> cases head <;> (try rfl)
  all_goals
    rename_i xl ρ
    cases xl <;> rfl

/-- It is what the page's code of chain queries under the seeds' tag writes. -/
theorem seedS_eq (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) :
    seedS D early e dd P K q j = (fbSeedsT (Tests.run D early e dd) P K).put (q, j) := by
  unfold seedS
  by_cases h0 : q.round = 0
  · rw [if_pos h0]
    refine Eq.trans ?_ (split_true _ _ _ _ (q, j) (decide_eq_true h0)).symm
    show _ = (selT K (q, j)).bind (u0T (Tests.run D early e dd) P).put
    unfold selT
    by_cases hj : j = Fin.last K
    · rw [if_pos hj, if_pos hj, selS_eq]
      rfl
    · rw [if_neg hj, if_neg hj]
      rfl
  · rw [if_neg h0]
    refine Eq.trans ?_ (split_false _ _ _ _ (q, j) (decide_eq_false h0)).symm
    rw [toTupT_eq D early e dd, tupT_eq]
    rfl

/-! ## The string of every query -/

/-- The total code at a real point: what `real` writes, where it writes; elsewhere the byte 2 and
the string under `back`. -/
theorem totalG_get {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : Page L K) (a : RealPts 256 K L) :
    (totalG C).put (.inl a) = (C.real.put a).getD (bitsOfByte 2 ++ C.back.put (.inl a)) := by
  cases h : C.real.put a with
  | some s => exact totalG_real C a s h
  | none => exact totalG_none C a h

variable (n : ℕ) (back : StrCode (AllPts 256 K (Le D early e)))

/-- The page's code of leaves. -/
abbrev Vn : Leaves (Le D early e) := KeyLeaves.leavesAt (Le D early e).toBatchProtocol n P.cfg

/-- The string of every leaf query. -/
def codeLeaf (q : LeafIn (Le D early e)) : List Bool :=
  (leafS P.cfg n q.body q.salt).getD (bitsOfByte 2 ++ back.put (.inl (.inl q)))

/-- The string of every vertex query. -/
def codeNode (q : Bits × Bits) : List Bool :=
  ((pNode P.cfg).put q).getD (bitsOfByte 2 ++ back.put (.inl (.inr (.inl q))))

/-- The string of every chain query under the link's tag, at every block. -/
def codeLink (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) : List Bool :=
  (linkS D early e dd P K q j).getD
    (bitsOfByte 2 ++ back.put (.inl (.inr (.inr (.inr (.inr (.inl ⟨.link, q, j⟩)))))))

/-- The string of every chain query under the seeds' tag, at every block. -/
def codeSeed (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) : List Bool :=
  (seedS D early e dd P K q j).getD
    (bitsOfByte 2 ++ back.put (.inl (.inr (.inr (.inr (.inr (.inl ⟨.test, q, j⟩)))))))

/-- The page's data at the computable tests are `EntryPage.pageE`'s. -/
theorem pg_eq : pageT (Tests.run D early e dd) P K (Vn D early e P n) back =
    pageE P dd K (Vn D early e P n) back := pageT_eq _ _ _ _ _

theorem codeLeaf_eq (q : LeafIn (Le D early e)) (j : Fin 1) :
    codeLeaf D early e P K n back q = (implE P dd K (Vn D early e P n) back).code .leaf q j := by
  show _ = (totalG (pageE P dd K (Vn D early e P n) back)).put (.inl (.inl q))
  rw [← pg_eq, totalG_get]
  rfl

theorem codeNode_eq (q : Bits × Bits) (j : Fin 1) :
    codeNode D early e P K back q = (implE P dd K (Vn D early e P n) back).code .node q j := by
  show _ = (totalG (pageE P dd K (Vn D early e P n) back)).put (.inl (.inr (.inl q)))
  rw [← pg_eq, totalG_get]
  rfl

theorem codeLink_eq (q : FbIn 256 (Le D early e) .link) (j : Fin (K + 1)) :
    codeLink D early e dd P K back q j =
      (implE P dd K (Vn D early e P n) back).code (.fb .link) q j := by
  show _ = (totalG (pageE P dd K (Vn D early e P n) back)).put
    (.inl (.inr (.inr (.inr (.inr (.inl ⟨.link, q, j⟩))))))
  rw [← pg_eq, totalG_get]
  unfold codeLink
  rw [linkS_eq]
  rfl

theorem codeSeed_eq (q : FbIn 256 (Le D early e) .test) (j : Fin (K + 1)) :
    codeSeed D early e dd P K back q j =
      (implE P dd K (Vn D early e P n) back).code (.fb .test) q j := by
  show _ = (totalG (pageE P dd K (Vn D early e P n) back)).put
    (.inl (.inr (.inr (.inr (.inr (.inl ⟨.test, q, j⟩))))))
  rw [← pg_eq, totalG_get]
  unfold codeSeed
  rw [seedS_eq]
  rfl

/-! ## The family -/

/-- `Run.toBytes`, with the library's looping twin of `bitsToBytes` (Run/CodingBitsT.lean): one
frame of the evaluator's stack a byte is too many for a long query. -/
def toBytesT (s : List Bool) : ByteArray :=
  if plainB s then bitsToBytesT s
  else ⟨#[4, UInt8.ofNat (s.length % 8)]⟩ ++ bitsToBytesT (fillUp s)

/-- It is `Run.toBytes`. -/
theorem toBytesT_eq (s : List Bool) : toBytesT s = toBytes s := by
  unfold toBytesT toBytes
  rw [bitsToBytesT_eq, bitsToBytesT_eq]

/-- The realised oracle at a string of bits, as bytes. -/
def hashS (s : List Bool) : ByteArray := _root_.Fmt.oracle (toBytesT s)

/-- As a digest it is the one oracle on bits. -/
theorem hashS_eq (s : List Bool) : digS (hashS s) = oBits () s := by
  unfold hashS
  rw [toBytesT_eq]
  exact digS_eq _

/-- Whether the evaluable part of the family answers at an oracle. -/
def asked : TypedOracleCompiler.Compile.Batch.OracleName → Bool
  | .leaf => true
  | .node => true
  | .fb .link => true
  | .fb .test => true
  | _ => false

/-- The answer to a typed query as data: one byte string for each block. -/
def ansS : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 (Le D early e) o → Array ByteArray
  | .leaf, q => #[hashS (codeLeaf D early e P K n back q)]
  | .node, q => #[hashS (codeNode D early e P K back q)]
  | .fb .link, q => Array.ofFn (n := K + 1) fun j => hashS (codeLink D early e dd P K back q j)
  | .fb .test, q => Array.ofFn (n := K + 1) fun j => hashS (codeSeed D early e dd P K back q j)
  | _, _ => #[]

/-- The byte strings as a typed answer. -/
def decS (o : TypedOracleCompiler.Compile.Batch.OracleName) (a : Array ByteArray) : rngOf 256 K o :=
  (rngEquiv 256 K o).symm fun j => digS (a.getD j.val ByteArray.empty)

/-- THE PAGE's FAMILY AT THE ORACLE MADE FROM LEAN's BLAKE2b, FOR THE EVALUATOR. -/
def famSafe : Fam (typedOracleFamily 256 K (Le D early e)) := fun o q =>
  if asked o = true then decS K o (ansS D early e dd P K n back o q)
  else famRun dd P K (Vn D early e P n) back oBits o q

/-- IT IS THE FAMILY THAT IS READ OUT OF THE REALISED ORACLE THROUGH `EntryPage.implE`, AT EVERY
ORACLE AND QUERY. -/
theorem famSafe_eq :
    famSafe D early e dd P K n back = readBlocks (implE P dd K (Vn D early e P n) back) oBits := by
  funext o q
  unfold famSafe
  have one : ∀ (s : List Bool) (j : Fin 1),
      digS ((#[hashS s] : Array ByteArray).getD j.val ByteArray.empty) = oBits () s := by
    intro s j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact hashS_eq _
  have many : ∀ (f : Fin (K + 1) → List Bool) (j : Fin (K + 1)),
      digS ((Array.ofFn (n := K + 1) fun i => hashS (f i)).getD j.val ByteArray.empty) =
        oBits () (f j) := by
    intro f j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
    exact hashS_eq _
  have rest : ∀ o' q', asked o' = false →
      (if asked o' = true then decS K o' (ansS D early e dd P K n back o' q')
        else famRun dd P K (Vn D early e P n) back oBits o' q') =
        readBlocks (implE P dd K (Vn D early e P n) back) oBits o' q' := fun o' q' h =>
    (if_neg (by rw [h]; exact Bool.false_ne_true)).trans
      (congrFun (congrFun (famRun_eq _ _ _ _ _ _) _) _)
  cases o with
  | leaf =>
    refine (if_pos (rfl : asked .leaf = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .leaf).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (oBits ()) (codeLeaf_eq D early e dd P K n back q j))
  | node =>
    refine (if_pos (rfl : asked .node = true)).trans ?_
    refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K .node).symm (funext fun j => ?_)
    exact (one _ j).trans (congrArg (oBits ()) (codeNode_eq D early e dd P K n back q j))
  | fb t =>
    cases t with
    | link =>
      refine (if_pos (rfl : asked (.fb .link) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .link)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (oBits ()) (codeLink_eq D early e dd P K n back q j))
    | test =>
      refine (if_pos (rfl : asked (.fb .test) = true)).trans ?_
      refine congrArg (TypedOracleCompiler.Compile.Batch.rngEquiv 256 K (.fb .test)).symm
        (funext fun j => ?_)
      exact (many _ j).trans (congrArg (oBits ()) (codeSeed_eq D early e dd P K n back q j))
    | onl => exact rest (.fb .onl) q rfl
  | rleaf => exact rest .rleaf q rfl
  | rnode => exact rest .rnode q rfl
  | g t => exact rest (.g t) q rfl
  | ann => exact rest .ann q rfl
  | other => exact rest .other q rfl
  | fbw t k => exact rest (.fbw t k) q rfl

end TypedOracleCompiler.Run.EntryPageSafe
