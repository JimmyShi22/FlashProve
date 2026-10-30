-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsOp.lean: THE PARSER's OPENINGS ON THE POSITIONS OF A LIST OF ROUNDS, AND: FOR
THE k-TH TREE OF A ROUND THE VERIFIER's CHECKS ARE THOSE THAT THE PARSER's OPENING CALLS FOR. After
the library's Run/PageIsOp.lean (opL, syOf, comp_tree). HERE IS PROOF WRITTEN, NOT TEXT SAID AGAIN.
  AS TEXT    opL
  WRITTEN ANEW   syOf (how a leaf's number and a column become a body: through the position of that
                 leaf IN TREE k; a body dflt stands where there is
             none: the library falls back on leaf 0), comp_tree (of the k-th tree; the library's is
             at a round written out with ONE tree, positions and columns by unfolding)
  NEW        noT_at, leafT_at: number, and column with its spelling, at the position of leaf x of
             tree k

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsTab
import OnBytes.TypedOracleCompiler.Run.Toy1TieChecksK
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
import OnBytes.TypedOracleCompiler.Slice.Plain3Pins
import Run.PageIsOp

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (colFn ofFn_colFn)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- the function "opens" of the parser's argument string, on the positions of a list of rounds, from
a table -/
def opL (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray)
    (ds : List RD) (p : OPos (uL C ds)) :
    Option (Opening 256 (OSym (uL C ds) p)) :=
  match tbl.lookup (placeSL C ds p).1 with
  | none => none
  | some x => x.2.at (symSL C ds p) run (placeSL C ds p).2

/-! ### At the position of leaf x of tree k -/

theorem noT_at : ∀ (ts : List _root_.Fmt.Shape) (k x : ℕ) (sh : _root_.Fmt.Shape) (p : PosT ts),
    ts[k]? = some sh → posAtT ts k x = some p → noT ts p = (sh.tree, x)
  | [], _, _, _, _, h, _ => by simp at h
  | s :: _, 0, x, sh, p, h, hp => by
      obtain rfl : s = sh := by simpa using h
      have h0 : (if h : x < 2 ^ s.a then some (.inl ⟨x, h⟩) else none) = some p := hp
      by_cases hx : x < 2 ^ s.a
      · rw [dif_pos hx] at h0
        cases Option.some.inj h0
        rfl
      · rw [dif_neg hx] at h0
        cases h0
  | _ :: ts, k + 1, x, sh, p, h, hp => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1
          (show (posAtT ts k x).map Sum.inr = some p from hp)
      exact noT_at ts k x sh q (by simpa using h) hq

/-- a column of the tree's width is a symbol there, and its spelling is the format's -/
theorem leafT_at (salt : ℕ) :
    ∀ (ts : List _root_.Fmt.Shape) (k x : ℕ) (sh : _root_.Fmt.Shape) (p : PosT ts)
        (col : List UInt64),
      ts[k]? = some sh → posAtT ts k x = some p → col.length = sh.W →
      ∃ y, symT ts p col = some y ∧
        leafT salt ts p y =
          (_root_.Fmt.leafPlace sh.tree sh.W (salt / 8), 2 ^ sh.a + x,
            _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen sh.W salt))
  | [], _, _, _, _, _, h, _, _ => by simp at h
  | s :: _, 0, x, sh, p, col, h, hp, hw => by
      obtain rfl : s = sh := by simpa using h
      have h0 : (if h : x < 2 ^ s.a then some (.inl ⟨x, h⟩) else none) = some p := hp
      by_cases hx : x < 2 ^ s.a
      · rw [dif_pos hx] at h0
        cases Option.some.inj h0
        refine ⟨fun i => col[i.val]'(by rw [hw]; exact i.isLt), dif_pos hw, ?_⟩
        have e2 : (fun i : Fin s.W => col[i.val]'(by rw [hw]; exact i.isLt)) = colFn s.W col :=
          funext fun i => by
            simp [colFn, List.getElem?_eq_getElem (show i.val < col.length by rw [hw]; exact i.isLt)]
        show (_root_.Fmt.leafPlace s.tree s.W (salt / 8), 2 ^ s.a + x,
            _root_.Fmt.colBytes (List.ofFn fun i : Fin s.W => col[i.val]'(by rw [hw]; exact i.isLt)) ++ _) = _
        rw [e2, ofFn_colFn s.W col hw]
      · rw [dif_neg hx] at h0
        cases h0
  | _ :: ts, k + 1, x, sh, p, col, h, hp, hw => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1
          (show (posAtT ts k x).map Sum.inr = some p from hp)
      exact leafT_at salt ts k x sh q col (by simpa using h) hq hw

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- how a leaf's number and a column become a body: through the position of that leaf in tree k of
the round -/
def syOf (d : RD) (emb : (p : PosT d.trees) → SymT d.trees p → L.Bd) (dflt : L.Bd) (k x : ℕ)
    (col : List UInt64) : L.Bd :=
  match posAtT d.trees k x with
  | some p =>
    match symT d.trees p col with
    | some y => emb p y
    | none => dflt
  | none => dflt

/-- the k-th tree of a round: the verifier's checks are those that the parser's opening calls for -/
theorem comp_tree (d : RD) (ds : List RD) (k : ℕ) (sh : _root_.Fmt.Shape)
    (hk : d.trees[k]? = some sh)
    (tbl : List (ℕ × ℕ × OpenB))
    (run : ByteArray) (sb : ℕ) (Ob : OpenB) (hl : tbl.lookup sh.tree = some (sh.W, Ob))
    (ha : Ob.a = sh.a) (hok : Ob.ok sb sh.W = true)
    (emb : (p : PosT d.trees) → SymT d.trees p → L.Bd) (dflt : L.Bd)
    (isRead : OPos (uL C (d :: ds)) → Bool)
    (hread : ∀ x p, posAtT d.trees k x = some p → isRead (.inl p) = decide (x ∈ Ob.idx))
    (rt : Dig 256) :
    compP (fun _ => L) (roundS C d) ((wireS C K chal d).posAtJ k) sh.a emb rt
        (fun p => isRead (.inl p)) (fun p => opL C tbl run (d :: ds) (.inl p))
        (List.range (2 ^ sh.a)) =
      some (TieTree.checksOf (syOf d emb dflt k) run rt Ob) := by
  rw [compP_eq, ← ha]
  refine TieTree.checksComp_atK (L := L) (r := (roundS C d).up) ((wireS C K chal d).posAtJ k) emb rt
    (fun p => isRead (.inl p)) (fun p => opL C tbl run (d :: ds) (.inl p))
    (fun p l => symT d.trees p l) (syOf d emb dflt k) run Ob sb sh.W hok fun j hj => ?_
  rw [ha] at hj
  obtain ⟨p, hp, -⟩ := TypedOracleCompiler.Slice.posAtT_some d.trees k j sh hk hj
  refine ⟨p, hp, hread j p hp, ?_, fun col hc => ?_⟩
  · unfold opL
    show (match tbl.lookup (noT d.trees p).1 with
      | none => none
      | some x => x.2.at (symT d.trees p) run (noT d.trees p).2) = _
    rw [noT_at d.trees k j sh p hk hp, hl]
  · have hw : col.length = sh.W := (TieTree.ok_list Ob sb sh.W hok).2.2 col hc
    obtain ⟨y, hy, -⟩ := leafT_at 0 d.trees k j sh p col hk hp hw
    refine ⟨y, hy, ?_⟩
    unfold syOf
    rw [hp]
    dsimp only
    rw [hy]

end

end TypedOracleCompiler.Run.PQ
