-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsList.lean: the body of a leaf is a string of bits, at the sibling's generic
protocol with A LIST OF TREES A ROUND.

OnBytes/TypedOracleCompiler/Strings.lean has this instance of the sibling's body at the LIBRARY's generic protocol,
whose rounds have one tree. OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean and PlanQS.lean make a generic protocol
from rounds' data with a list of trees a round, each tree with its own depth and width, and its
wiring. This file says the instance again over that maker.

A symbol at a position is written as its leaf's own string: what the library's code of ONE tree's
leaves (`Run.PQ.leaf1`) writes at that position's own tree: the label with the index, the column,
the fill (`ownT` in a round, `ownStr` in a list of rounds, `embT` on the shape with the round in
front). A body is read at a position by that same tree's code (`rdT`, `rdLeaf`, `prjT`). What is
written is read back if no tree is deeper than 63 (`prjT_embT`); the body is the bits of the
format's label with the position's own tree's numbers, and of column and fill (`embT_fit`). A lawful
wiring of the protocol whose external part is the empty one gives a lawful wire of the sibling with
these bodies (`ofT`, `ofT_okg`); the maker's own wiring is such a one under the maker's three
hypotheses (`ofMaker_okg`), also at a list with a round of two trees.

Main definitions: `ownT`, `rdT`, `leafT`, `ownStr`, `rdLeaf`, `leafSL`, `embT`, `prjT`, `ofT`, `wT`.
Main theorems: `rdT_ownT`, `ownT_some`, `ownT_fit`, `prjT_embT`, `embT_fit`, `ofT_okg`,
`ofMaker_okg`, `leaf_query`.

Not claimed. What OnBytes/TypedOracleCompiler/Strings.lean's head says is not claimed is not claimed here either,
but for two things: a round may have several trees, and a lawful wire is made, under the maker's
hypotheses on the verifier's messages (uniform blocks give uniform messages; what is drawn fits the
entry; work of at most 64 bits), which this file shows at no list (the sibling's Run/PlanPull.lean
meets them with verifier's messages as hash blocks, from bounds on the entries, and at one closed
list with a round of two trees; with sampled values the first is false wherever a field element is
drawn). The interface has no external string. The code of leaf queries is that file's
(`Strings.pLeafS`): it does not look at the shape; no test on bodies is shown to be passed here. No
condition is put on the trees' numbers. That the chains of a key file are such a list is not shown.
The laws of a wire take any number of trees a round, but the sibling's verifier refuses a component
with more than `maxRt` (two) trees. This instance is tied to that of OnBytes/TypedOracleCompiler/Strings.lean by
nothing: no guard stands over it as a whole; of its pieces for a round and a list of rounds
OnBytes/TypedOracleCompiler/StringsRead.lean and StringsBounds.lean show that a symbol's body passes a test on
bodies. (Two files of tests by program try them; they are not in this library.) Its shape is not
that of the protocol in three stretches (OnBytes/TypedOracleCompiler/Slice/Plain3.lean): there
OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean uses this file's pieces for a round and for a list of rounds.
`okg_cast` carries the laws and the external part alone. In this file `RD`, `uL`, `SOf`, `LtS`,
`wqS` are the SIBLING's (TypedOracleCompiler.Run.PQ); `leaf1` is the library's.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Strings
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws

set_option autoImplicit false

namespace TypedOracleCompiler.StringsList
open _root_.Compile Rom
open _root_.Iop (OPos OSym BatchInteractiveOracleProof)
open _root_.Run (PCode bytesToBits Twin.up)
open _root_.Run.PQ (CK View leaf1 leaf1_fit leaf1_some)
open TypedOracleCompiler.Run.PQ (RD PosT SymT uL SOf LtS wqS wqS_okg psof_up ChalUnif DrawnFits)

/- salt: the length of a file's salt, in bytes -/
variable (salt : ℕ)

/-! ## One round -/

/-- A leaf's own string, in a round: what the code of its own tree writes for place and column. -/
def ownT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → SymT ts p → Option (List Bool)
  | s :: _, .inl x, col => (leaf1 (some s) salt).put (x, col)
  | _ :: ts, .inr p, col => ownT ts p col

/-- A string read at a position of a round by the code of that position's own tree: the column, if
the place is the position's. -/
def rdT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → List Bool → Option (SymT ts p)
  | s :: _, .inl x, b =>
    ((leaf1 (some s) salt).parse b).bind fun z => if z.1 = x then some z.2 else none
  | _ :: ts, .inr p, b => rdT ts p b

/-- The two numbers of a leaf's label and its bytes: the word with its own tree's number, width and
the salt's words; 2 ^ depth + place; column and fill. -/
def leafT : (ts : List _root_.Fmt.Shape) → (p : PosT ts) → SymT ts p → Nat × Nat × ByteArray
  | s :: _, .inl x, col =>
    (_root_.Fmt.leafPlace s.tree s.W (salt / 8), 2 ^ s.a + x.val,
      _root_.Fmt.colBytes (List.ofFn col) ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen s.W salt))
  | _ :: ts, .inr p, col => leafT ts p col

/-- An own string, read at its own position, gives its column. -/
theorem rdT_ownT : ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts) (a : SymT ts p) (m : List Bool),
    ownT salt ts p a = some m → rdT salt ts p m = some a
  | s :: _, .inl x, a, m, h => by
      have h1 : (leaf1 (some s) salt).parse m = some (x, a) :=
        (leaf1 (some s) salt).parse_put _ m h
      show ((leaf1 (some s) salt).parse m).bind
        (fun z => if z.1 = x then some z.2 else none) = some a
      rw [h1]
      exact if_pos rfl
  | _ :: ts, .inr p, a, m, h => rdT_ownT ts p a m h

/-- Every leaf of a round has an own string if none of its trees is deeper than 63. -/
theorem ownT_some : ∀ (ts : List _root_.Fmt.Shape), (∀ s ∈ ts, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
    ∀ (p : PosT ts) (a : SymT ts p), (ownT salt ts p a).isSome = true
  | s :: _, h, .inl x, a => leaf1_some (some s) salt (h s (List.mem_cons_self ..)) (x, a)
  | _ :: ts, h, .inr p, a => ownT_some ts (fun s hs => h s (List.mem_cons_of_mem _ hs)) p a

/-- An own string is the bits of the format's label, with its own tree's numbers, and of column and
fill. -/
theorem ownT_fit : ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts) (a : SymT ts p) (m : List Bool),
    ownT salt ts p a = some m →
      m = bytesToBits (_root_.Fmt.label 164 (leafT salt ts p a).1 (leafT salt ts p a).2.1) ++
          bytesToBits (leafT salt ts p a).2.2
  | s :: _, .inl x, a, m, h => leaf1_fit (some s) salt x a m h
  | _ :: ts, .inr p, a, m, h => ownT_fit ts p a m h

/-! ## A list of rounds -/

variable (C : CK)

/-- A leaf's own string, in a list of rounds. -/
def ownStr : (ds : List RD) → SymAny (uL C ds) → Option (List Bool)
  | [], y => y.1.elim
  | d :: _, ⟨.inl p, col⟩ => ownT salt d.trees p col
  | _ :: ds, ⟨.inr q, col⟩ => ownStr ds ⟨q, col⟩

/-- A string read at a position of a list of rounds. -/
def rdLeaf : (ds : List RD) → (p : OPos (uL C ds)) → List Bool → Option (OSym (uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl p, b => rdT salt d.trees p b
  | _ :: ds, .inr q, b => rdLeaf ds q b

/-- The two numbers of a leaf's label and its bytes, in a list of rounds. -/
def leafSL : (ds : List RD) → SymAny (uL C ds) → Nat × Nat × ByteArray
  | [], y => y.1.elim
  | d :: _, ⟨.inl p, col⟩ => leafT salt d.trees p col
  | _ :: ds, ⟨.inr q, col⟩ => leafSL ds ⟨q, col⟩

/-- An own string, read at its own position, gives its column. -/
theorem rdLeaf_own : ∀ (ds : List RD) (p : OPos (uL C ds)) (a : OSym (uL C ds) p)
    (m : List Bool), ownStr salt C ds ⟨p, a⟩ = some m → rdLeaf salt C ds p m = some a
  | [], p, _, _, _ => p.elim
  | d :: _, .inl p, a, m, h => rdT_ownT salt d.trees p a m h
  | _ :: ds, .inr q, a, m, h => rdLeaf_own ds q a m h

/-- Every leaf has an own string if no tree is deeper than 63. -/
theorem ownStr_some : ∀ (ds : List RD), (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
    ∀ y : SymAny (uL C ds), (ownStr salt C ds y).isSome = true
  | [], _, y => y.1.elim
  | d :: _, h, ⟨.inl p, col⟩ => ownT_some salt d.trees (h d (List.mem_cons_self ..)) p col
  | _ :: ds, h, ⟨.inr q, col⟩ =>
    ownStr_some ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) ⟨q, col⟩

/-- An own string is the bits of the format's label, with its own tree's numbers, and of column and
fill. -/
theorem ownStr_fit : ∀ (ds : List RD) (y : SymAny (uL C ds)) (m : List Bool),
    ownStr salt C ds y = some m →
      m = bytesToBits (_root_.Fmt.label 164 (leafSL salt C ds y).1 (leafSL salt C ds y).2.1) ++
          bytesToBits (leafSL salt C ds y).2.2
  | [], y, _, _ => y.1.elim
  | d :: _, ⟨.inl p, col⟩, m, h => ownT_fit salt d.trees p col m h
  | _ :: ds, ⟨.inr q, col⟩, m, h => ownStr_fit ds ⟨q, col⟩ m h

/-! ## The shape with the round in front; the wire -/

variable (ds : List RD) (dec : View → Bool)

/-- A symbol with position of the shape with the round in front, as one of the shape behind it. -/
def lower : SymAny (Twin.up (SOf C ds)) → SymAny (uL C ds)
  | ⟨.inl p, _⟩ => p.elim
  | ⟨.inr q, a⟩ => ⟨q, a⟩

/-- A symbol at a position, as a body: its leaf's own string; the empty string where its own tree's
code writes nothing (a tree deeper than 63). -/
def embT (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p) : List Bool :=
  (ownStr salt C ds (lower C ds ⟨p, a⟩)).getD []

/-- A body read at a position: by the code of that position's own tree. -/
def prjT : (p : OPos (Twin.up (SOf C ds))) → List Bool → Option (OSym (Twin.up (SOf C ds)) p)
  | .inl p, _ => p.elim
  | .inr q, b => rdLeaf salt C ds q b

/-- What is written is read back, if no tree is deeper than 63. No condition on the trees'
numbers, or on how many trees a round has. -/
theorem prjT_embT (hd : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    ∀ (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p),
      prjT salt C ds p (embT salt C ds p a) = some a
  | .inl p, _ => p.elim
  | .inr q, a => by
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ownStr_some salt C ds hd ⟨q, a⟩)
      show rdLeaf salt C ds q ((ownStr salt C ds ⟨q, a⟩).getD []) = some a
      rw [hm]
      exact rdLeaf_own salt C ds q a m hm

/-- The body is the bits of the format's label, with the position's own tree's numbers, and of
column and fill, if no tree is deeper than 63. -/
theorem embT_fit (hd : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p) :
    embT salt C ds p a =
      bytesToBits (_root_.Fmt.label 164 (leafSL salt C ds (lower C ds ⟨p, a⟩)).1
          (leafSL salt C ds (lower C ds ⟨p, a⟩)).2.1) ++
        bytesToBits (leafSL salt C ds (lower C ds ⟨p, a⟩)).2.2 := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (ownStr_some salt C ds hd (lower C ds ⟨p, a⟩))
  unfold embT
  rw [hm]
  exact ownStr_fit salt C ds _ m hm

/-- A wiring of the protocol, as a wire of the sibling at the interface whose Test is the protocol,
with bodies that are strings. Link and Batch have no round. -/
def ofT {K : ℕ} (T : Iop.ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline)) :
    Iop.QueryLayout 256 (Strings.strung (LtS C ds dec)) where
  K := K
  T := T
  Lk := ⟨(), _root_.Run.PQ.weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), _root_.Run.PQ.we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := fun _ => ([] : List Bool)
  prjE := fun _ => some ()
  embT := embT salt C ds
  prjT := prjT salt C ds
  embL := fun p _ => p.elim
  prjL := fun p _ => p.elim
  embB := fun p _ => p.elim
  prjB := fun p _ => p.elim

/-- A lawful wiring of the protocol gives a lawful wire of the sibling with these bodies, if its
external part is the empty one and no tree is deeper than 63. -/
theorem ofT_okg {K : ℕ} {T : Iop.ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline)}
    (hT : T.OKG) (he : T.ext = _root_.Run.PQ.we0)
    (hd : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    (ofT salt C ds dec T).OKG where
  T := hT
  Lk := { sh := trivial
          ext := ⟨List.nodup_nil, fun p => p.elim (·.elim0) (·.elim0),
            fun _ p => p.elim (·.elim0) (·.elim0)⟩
          opens := fun _ _ _ => le_refl 0
          depth := trivial }
  B := { sh := trivial
         ext := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩
         opens := fun _ _ _ => le_refl 0
         depth := trivial }
  fits := Nat.zero_le _
  slots := rfl
  extDepth := ⟨by show T.ext.depth = 0; rw [he]; rfl, rfl, rfl⟩
  depthT := Nat.zero_le _
  depthL := le_refl 0
  depthB := le_refl 0
  extT := fun p => p.elim0
  extB := fun p => p.elim0
  extL := ⟨fun p => p.elim0, fun p => p.elim0⟩
  prjE_emb := fun _ => rfl
  prjT_emb := prjT_embT salt C ds hd
  prjL_emb := fun p _ => p.elim
  prjB_emb := fun p _ => p.elim

/-- The maker's own wiring, carried along the equation "the protocol is the Test of its interface".
-/
def wT (K : ℕ) (chal : ∀ e k, (Fin K → _root_.Iop.Dig 256) → C.Ch e k) :
    Iop.ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline) :=
  psof_up C ds dec ▸ wqS C K chal ds dec

/-- Laws and external part go along an equation of protocols. -/
theorem okg_cast {K : ℕ} {Q Q' : BatchInteractiveOracleProof Unit _root_.Run.PQ.E0} (e : Q = Q')
    (w : Iop.ProtocolQueryLayout 256 K Q) (h : w.OKG) : (e ▸ w).OKG ∧ (e ▸ w).ext = w.ext := by
  subst e
  exact ⟨h, rfl⟩

/-- The maker's own wiring gives a lawful wire of the sibling with bodies that are strings,
under the maker's three hypotheses, if no tree is deeper than 63: at any list of rounds' data, each
round with any list of trees (of which the sibling's verifier takes at most `maxRt`). -/
theorem ofMaker_okg (K : ℕ) (chal : ∀ e k, (Fin K → _root_.Iop.Dig 256) → C.Ch e k)
    (hc : ChalUnif C K chal ds) (hf : DrawnFits C ds) (hw : ∀ d ∈ ds, d.entry.work ≤ 64)
    (hd : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    (ofT salt C ds dec (wT C ds dec K chal)).OKG :=
  ofT_okg salt C ds dec
    (okg_cast (psof_up C ds dec) _ (wqS_okg C K chal ds dec hc hf hw)).1
    (okg_cast (psof_up C ds dec) _ (wqS_okg C K chal ds dec hc hf hw)).2 hd

/-- A leaf query on a symbol is written by the code of OnBytes/TypedOracleCompiler/Strings.lean, with the bits of
`Fmt.oStr` at the number 164 and the numbers of the position's own tree. start: 32 bytes; fsalt: a
file's salt of the length `salt`; the typed salt is the bits of the one and then of the other.
Asked: no tree is deeper than 63; the body passes the code's test. -/
theorem leaf_query (ok : List Bool → Bool)
    (hd : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (p : OPos (Twin.up (SOf C ds))) (a : OSym (Twin.up (SOf C ds)) p)
    (hok : ok (embT salt C ds p a) = true)
    (start fsalt : ByteArray) (hs : start.size = 32) (hf : fsalt.size = salt) :
    (Strings.pLeafS (LtS C ds dec) (8 * salt) ok).put
        ⟨embT salt C ds p a, bytesToBits start ++ bytesToBits fsalt⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 164 (leafSL salt C ds (lower C ds ⟨p, a⟩)).1
        (leafSL salt C ds (lower C ds ⟨p, a⟩)).2.1 start
        ((leafSL salt C ds (lower C ds ⟨p, a⟩)).2.2 ++ fsalt))) := by
  have hl : (bytesToBits start ++ bytesToBits fsalt).length = 256 + 8 * salt := by
    rw [List.length_append, _root_.Run.length_bytesToBits, _root_.Run.length_bytesToBits, hs, hf]
  have h256 : (bytesToBits start).length = 256 := by rw [_root_.Run.length_bytesToBits, hs]
  show (if (bytesToBits start ++ bytesToBits fsalt).length = 256 + 8 * salt then
      (if ok (embT salt C ds p a) then some (embT salt C ds p a) else none).map fun m =>
        _root_.Run.pre33 ++ ((bytesToBits start ++ bytesToBits fsalt).take 256 ++
          (m ++ (bytesToBits start ++ bytesToBits fsalt).drop 256)) else none) = _
  rw [if_pos hl, if_pos hok, embT_fit salt C ds hd p a, List.take_left' h256,
    List.drop_left' h256, _root_.Run.oStr32_bits 164 _ _ start _ (by decide) hs,
    _root_.Run.bytesToBits_append]
  simp only [Option.map_some, List.append_assoc]

end TypedOracleCompiler.StringsList
