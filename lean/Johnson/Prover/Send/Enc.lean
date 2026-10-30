--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Send/Enc.lean: THE SHARED "SENDING" (the kind K1), THE PROVER's SIDE: THE WRITTEN
COLUMN: the description's own cut of a leaf, at the written column of Core.lean, reads the code
words' symbols of the rows that the caller handed: at every position, for every message of the
place. Statements and proofs.

General in the place P : K1.Par and in the rows V. The letters: lay := the place's layout
(Own.treesMade P.codes P.sent); of message number k: its tree lay.tree k, its part lay.part k, its
tree's shape T.

  flatL_at, flatC_at, length_flatC, foldl_extract, foldl_all   tools on lists and arrays
  symG_ofF         a row over F, laid into E, has symG's symbol: so there is ONE form of a symbol
  lay_some, deg_of_plan, mine_eq, mem_inTree, col_eq, seat_of   the layout is there; main rows are
                   over one of the two fields; the messages that col takes into a tree are the
                   landed inTree (Johnson/Desc/K12/Coin/LaySymbols.lean)
  length_mainSyms, length_maskSyms, widths_main, widths_mask, length_mains, length_masks
                   a message's words in a column are as many as its tree lists of it
  col_main_at, col_mask_at   where a message's words stand in the column: behind the two skips
  mainSyms_three, mainSyms_one, maskSyms_three, read_three   a message's symbols, word by word
  length_col       the column's width is the tree's
  send_enc         Blk.columnOf (OnBytes/Iop/Ground.lean) at the two skips that Own.symbolsAt
                   (Johnson/Desc/Own/Symbols.lean) counts, at the written column: as many main and
                   mask symbols as the message has rows, and each READS (readE) as symG of the row
                   and its tail; mask rows at the position modulo the mask code's length
  rows_held        these rows are the held words' rows, by K1's index
  lt_col           every word of the column is below the prime
  seat_behind      the book behind the sending seats message k at (the old trees + its tree, its
                   part), and that tree has the shape T: so send_enc's skips are the book's

By: layTrees_symbols, layTrees_part, layTrees_treeSize, inTree_get
(Johnson/Desc/K12/Coin/LaySymbols.lean); Own.treesMade_eq (Johnson/Desc/Own/TreesAgree.lean);
Book.recvP_seat (Johnson/Desc/Book/BookFitsGround.lean); Book.layTrees_fits (Book/BookFits.lean);
Book.getElem?_of_getD (Book/LayOmega.lean); lt_ofF (Johnson/Prover/Link/BasePart.lean).

Limits. Own.symbolsAt's three look-ups and its search for a drawn position in a tree's own list are
not treated: they read what is drawn and opened later. No tree, no root, no salt, no hash: the
compiler's. The position is any number. Nothing on how a tail or a mask row's entries are chosen;
nothing on soundness, or on what any entry shows or does not show.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Says
import Johnson.Desc.K12.Coin.LaySymbols
import Johnson.Desc.Book.BookFitsGround
import Johnson.Desc.Book.LayOmega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open OnBytes.LayTreesLaws (inTree mainW maskW inTree_get)
open _root_.Desc.Plain (DState)
open Johnson.Prover.Link (symG symG_congr lt_ofF words3)

/-! ## Lists -/

/-- Entry j of the p-th list stands behind the lists in front of it. -/
theorem flatL_at {ι α : Type} (f : ι → List α) : ∀ (ks : List ι) (p : ℕ) (k : ι) (j : ℕ),
    ks[p]? = some k → j < (f k).length →
    (ks.flatMap f)[((ks.take p).map fun a => (f a).length).sum + j]? = (f k)[j]?
  | [], _, _, _, h, _ => by simp at h
  | a :: ks, 0, k, j, h, hj => by
    obtain rfl : a = k := by simpa using h
    rw [List.flatMap_cons]
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
    exact List.getElem?_append_left hj
  | a :: ks, p + 1, k, j, h, hj => by
    have ih := flatL_at f ks p k j (by simpa using h) hj
    rw [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact ih

/-- Lists of one length c in a row: entry t of the r-th. -/
theorem flatC_at {α : Type} (f : ℕ → List α) (c : ℕ) (hc : ∀ r, (f r).length = c) (n r t : ℕ)
    (hr : r < n) (ht : t < c) : ((List.range n).flatMap f)[c * r + t]? = (f r)[t]? := by
  have h := flat_at f n r t hr (by rw [hc]; exact ht)
  simp only [hc] at h
  rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm] at h
  exact h

theorem length_flatC {α : Type} (f : ℕ → List α) (c : ℕ) (hc : ∀ r, (f r).length = c) (n : ℕ) :
    ((List.range n).flatMap f).length = n * c := by
  rw [List.length_flatMap]
  simp only [hc]
  rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]

theorem foldl_extract (A : Array ℕ) (p : ℕ) :
    (A.extract 0 p).foldl (· + ·) 0 = (A.toList.take p).sum := by
  rw [← Array.foldl_toList, List.sum_eq_foldl]
  simp

theorem foldl_all (A : Array ℕ) : A.foldl (· + ·) 0 = A.toList.sum := by
  rw [← Array.foldl_toList, List.sum_eq_foldl]

/-! ## One form of a symbol -/

/-- **A row over F, laid into E, has symG's symbol.** -/
theorem symG_ofF (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GF) :
    algebraMap GF GE (symF C x m r) =
      symG C x (fun j => algebraMap GF GE (m j)) (fun q => algebraMap GF GE (r q)) := by
  unfold symF symG
  rw [map_add, map_sum, map_sum]
  simp only [map_mul]

/-! ## The layout -/

/-- At a place that passes the tests on the plan the layout is there. -/
theorem lay_some (P : K1.Par) (hP : K1.planOkOwn P = true) :
    ∃ Ly, layTrees P.codes P.sent = some Ly ∧ (Own.treesMade P.codes P.sent).getD {} = Ly := by
  simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hP
  have h := hP.1.1.2
  rw [Own.treesCan_eq] at h
  obtain ⟨Ly, hL⟩ := Option.isSome_iff_exists.1 h
  exact ⟨Ly, hL, by rw [Own.treesMade_eq, hL]; rfl⟩

/-- A message's main rows are over one of the two fields. -/
theorem deg_of_plan (P : K1.Par) (hP : K1.planOkOwn P = true) (k : ℕ) (hk : k < P.sent.size) :
    (shapeAt P k).mainDeg = 1 ∨ (shapeAt P k).mainDeg = 3 := by
  simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hP
  have h := Array.all_eq_true_iff_forall_mem.1 hP.1.1.1 P.sent[k] (Array.getElem_mem hk)
  rw [← Own.sentShapeFits_agrees] at h
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  have e : shapeAt P k = P.sent[k].shape := by
    unfold shapeAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    rfl
  rw [e]
  exact h.2

/-- The messages that col takes into a tree. -/
theorem mine_eq (cs : Codes) (sent : Array OracleNotice) (Ly : TreeLay)
    (h : layTrees cs sent = some Ly) (τ : ℕ) :
    ((List.range sent.size).filter fun k => Ly.tree[k]? == some τ) =
      inTree Ly.tree τ sent.size := by
  unfold inTree
  refine List.filter_congr fun k hk => ?_
  have hk' : k < Ly.tree.size := by
    rw [layTrees_treeSize cs sent Ly h]
    exact List.mem_range.1 hk
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']
  simp

theorem mem_inTree {tree : Array ℕ} {τ n a : ℕ} (h : a ∈ inTree tree τ n) : a < n :=
  List.mem_range.1 (List.mem_filter.1 h).1

/-! ## A message's words in a column -/

theorem length_mainSyms (P : K1.Par) (V : ℕ → Rows) (k x : ℕ)
    (hd : (shapeAt P k).mainDeg = 1 ∨ (shapeAt P k).mainDeg = 3) :
    (mainSyms P V k x).length = mainW P.sent k := by
  unfold mainSyms
  show ((List.range (shapeAt P k).mainRows).flatMap _).length =
    (shapeAt P k).mainRows * (shapeAt P k).mainDeg
  refine length_flatC _ _ (fun r => ?_) _
  rcases hd with h | h <;> rw [h] <;> rfl

theorem length_maskSyms (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) :
    (maskSyms P V k x).length = maskW P.sent k := by
  unfold maskSyms
  exact length_flatC _ 3 (fun r => rfl) _

/-! ## Where a message's words stand in the column -/

/-- The column, over the landed list of a tree's messages. -/
theorem col_eq (P : K1.Par) (V : ℕ → Rows) (Ly : TreeLay) (hL : layTrees P.codes P.sent = some Ly)
    (τ x : ℕ) :
    col P V τ x = ((inTree Ly.tree τ P.sent.size).flatMap fun k => mainSyms P V k x) ++
      (inTree Ly.tree τ P.sent.size).flatMap fun k => maskSyms P V k x := by
  have e : (Own.treesMade P.codes P.sent).getD {} = Ly := by
    rw [Own.treesMade_eq, hL]
    rfl
  unfold col
  simp only [e, mine_eq P.codes P.sent Ly hL τ]

/-- What the layout says of message number k. -/
theorem seat_of (P : K1.Par) (Ly : TreeLay) (hL : layTrees P.codes P.sent = some Ly) (k : ℕ)
    (hk : k < P.sent.size) :
    (Ly.shapes.getD (Ly.tree.getD k 0) {}).mainSymbols.toList =
        (inTree Ly.tree (Ly.tree.getD k 0) P.sent.size).map (mainW P.sent) ∧
      (Ly.shapes.getD (Ly.tree.getD k 0) {}).maskSymbols.toList =
        (inTree Ly.tree (Ly.tree.getD k 0) P.sent.size).map (maskW P.sent) ∧
      (inTree Ly.tree (Ly.tree.getD k 0) P.sent.size)[Ly.part.getD k 0]? = some k := by
  have hτ : Ly.tree.getD k 0 < Ly.shapes.size := (Book.layTrees_fits hL k hk).1
  obtain ⟨a, b⟩ := layTrees_symbols P.codes P.sent Ly hL _ _ (Book.getElem?_of_getD _ _ {} hτ)
  refine ⟨a, b, ?_⟩
  have hp : Ly.part.getD k 0 = (inTree Ly.tree (Ly.tree.getD k 0) k).length := by
    have h := layTrees_part P.codes P.sent Ly hL k hk
    have hs : k < Ly.part.size := (Array.getElem?_eq_some_iff.1 h).1
    rw [Book.getElem?_of_getD _ _ 0 hs] at h
    exact Option.some.inj h
  rw [hp]
  exact inTree_get Ly.tree _ k rfl P.sent.size hk

theorem widths_main (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (x : ℕ)
    (l : List ℕ) (hl : ∀ a ∈ l, a < P.sent.size) :
    (l.map fun a => (mainSyms P V a x).length) = l.map (mainW P.sent) :=
  List.map_congr_left fun a ha => length_mainSyms P V a x (deg_of_plan P hP a (hl a ha))

theorem widths_mask (P : K1.Par) (V : ℕ → Rows) (x : ℕ) (l : List ℕ) :
    (l.map fun a => (maskSyms P V a x).length) = l.map (maskW P.sent) :=
  List.map_congr_left fun a _ => length_maskSyms P V a x

/-- The main symbols of all messages of a tree fill the tree's main width. -/
theorem length_mains (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (Ly : TreeLay)
    (τ x : ℕ) (T : TreeShape)
    (hT : T.mainSymbols.toList = (inTree Ly.tree τ P.sent.size).map (mainW P.sent)) :
    ((inTree Ly.tree τ P.sent.size).flatMap fun k => mainSyms P V k x).length = T.mainWidth := by
  rw [List.length_flatMap, widths_main P V hP x _ (fun a ha => mem_inTree ha), ← hT]
  exact (foldl_all _).symm

theorem length_masks (P : K1.Par) (V : ℕ → Rows) (Ly : TreeLay) (τ x : ℕ) (T : TreeShape)
    (hT : T.maskSymbols.toList = (inTree Ly.tree τ P.sent.size).map (maskW P.sent)) :
    ((inTree Ly.tree τ P.sent.size).flatMap fun k => maskSyms P V k x).length = T.maskWidth := by
  rw [List.length_flatMap, widths_mask P V x, ← hT]
  exact (foldl_all _).symm

/-- **Word j of message k's main symbols** stands behind skipMain. -/
theorem col_main_at (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (Ly : TreeLay)
    (hL : layTrees P.codes P.sent = some Ly) (k x j : ℕ) (hk : k < P.sent.size)
    (hj : j < (mainSyms P V k x).length) :
    (col P V (Ly.tree.getD k 0) x)[skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {})
      (Ly.part.getD k 0) + j]? = (mainSyms P V k x)[j]? := by
  obtain ⟨a, _, c⟩ := seat_of P Ly hL k hk
  have key := flatL_at (fun a => mainSyms P V a x) _ _ k j c hj
  rw [widths_main P V hP x _ (fun a ha => mem_inTree (List.mem_of_mem_take ha)), List.map_take,
    ← a, ← foldl_extract] at key
  have hlt := key
  rw [List.getElem?_eq_getElem hj] at hlt
  unfold skipMain
  rw [col_eq P V Ly hL, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hlt).1]
  exact key

/-- **Word j of message k's mask symbols** stands behind skipMask. -/
theorem col_mask_at (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (Ly : TreeLay)
    (hL : layTrees P.codes P.sent = some Ly) (k x j : ℕ) (hk : k < P.sent.size)
    (hj : j < (maskSyms P V k x).length) :
    (col P V (Ly.tree.getD k 0) x)[skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {})
      (Ly.part.getD k 0) + j]? = (maskSyms P V k x)[j]? := by
  obtain ⟨a, b, c⟩ := seat_of P Ly hL k hk
  have key := flatL_at (fun a => maskSyms P V a x) _ _ k j c hj
  rw [widths_mask P V x, List.map_take, ← b, ← foldl_extract] at key
  unfold skipMask
  rw [col_eq P V Ly hL, ← length_mains P V hP Ly _ x _ a, Nat.add_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact key

/-- **The column's width is the tree's.** -/
theorem length_col (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (τ x : ℕ)
    (hτ : τ < ((Own.treesMade P.codes P.sent).getD {}).shapes.size) :
    (col P V τ x).length =
      (((Own.treesMade P.codes P.sent).getD {}).shapes.getD τ {}).mainWidth +
        (((Own.treesMade P.codes P.sent).getD {}).shapes.getD τ {}).maskWidth := by
  obtain ⟨Ly, hL, e⟩ := lay_some P hP
  rw [e] at hτ ⊢
  obtain ⟨a, b⟩ := layTrees_symbols P.codes P.sent Ly hL _ _ (Book.getElem?_of_getD _ _ {} hτ)
  rw [col_eq P V Ly hL, List.length_append, length_mains P V hP Ly τ x _ a,
    length_masks P V Ly τ x _ b]

/-! ## A message's symbols, word by word -/

theorem mainSyms_three (P : K1.Par) (V : ℕ → Rows) (k x r t : ℕ)
    (h : (shapeAt P k).mainDeg = 3) (hr : r < (shapeAt P k).mainRows) (ht : t < 3) :
    (mainSyms P V k x)[3 * r + t]? =
      (words3 (ofE (symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainE r) ((V k).mainTlE r))))[t]? := by
  have e := flatC_at (fun r => if (shapeAt P k).mainDeg == 3 then
      words3 (ofE (symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainE r) ((V k).mainTlE r)))
    else [ofF (symF (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainF r) ((V k).mainTlF r))]) 3 (fun r => by rw [h]; rfl) _ r t hr ht
  simp only [h, beq_self_eq_true, if_true] at e
  rw [← e]
  unfold mainSyms
  simp only [h, beq_self_eq_true, if_true]

theorem mainSyms_one (P : K1.Par) (V : ℕ → Rows) (k x r : ℕ)
    (h : (shapeAt P k).mainDeg = 1) (hr : r < (shapeAt P k).mainRows) :
    (mainSyms P V k x)[r]? =
      some (ofF (symF (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainF r) ((V k).mainTlF r))) := by
  have e := flatC_at (fun r => if (shapeAt P k).mainDeg == 3 then
      words3 (ofE (symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainE r) ((V k).mainTlE r)))
    else [ofF (symF (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainF r) ((V k).mainTlF r))]) 1 (fun r => by rw [h]; rfl) _ r 0 hr Nat.one_pos
  have h13 : ((1 : ℕ) == 3) = false := rfl
  simp only [h, h13, Bool.false_eq_true, if_false, Nat.one_mul, Nat.add_zero,
    List.getElem?_cons_zero] at e
  rw [← e]
  unfold mainSyms
  simp only [h, h13, Bool.false_eq_true, if_false]

theorem maskSyms_three (P : K1.Par) (V : ℕ → Rows) (k x r t : ℕ)
    (hr : r < (shapeAt P k).maskRows) (ht : t < 3) :
    (maskSyms P V k x)[3 * r + t]? =
      (words3 (ofE (symG (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default))
        (x % 2 ^ (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)).a)
        ((V k).mask r) ((V k).maskTl r))))[t]? :=
  flatC_at _ 3 (fun _ => rfl) _ r t hr ht

/-- Three words of a list that spell a written element read as the element. -/
theorem read_three (c : List UInt64) (s : ℕ) (y : GE)
    (h : ∀ t, t < 3 → c[s + t]? = (words3 (ofE y))[t]?) :
    readE (E.mk3 (c.toArray.getD s 0) (c.toArray.getD (s + 1) 0) (c.toArray.getD (s + 2) 0)) =
      y := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  rw [Nat.add_zero] at h0
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, h0, h1, h2]
  show toE (ofE y) = y
  exact toE_ofE y

/-! ## The law -/

/-- **THE DESCRIPTION's OWN CUT OF A LEAF, AT THE WRITTEN COLUMN, READS THE CODE WORDS'
SYMBOLS.** -/
theorem send_enc (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (k : ℕ)
    (X : OnBytes.Oracle) (x : ℕ) (hk : k < P.sent.size) (hX : X.shape = shapeAt P k) :
    let lay := (Own.treesMade P.codes P.sent).getD {}
    let T := lay.shapes.getD (lay.tree.getD k 0) {}
    let c := Blk.columnOf X (skipMain T (lay.part.getD k 0)) (skipMask T (lay.part.getD k 0))
      (col P V (lay.tree.getD k 0) x).toArray
    let C := codeOf (P.codes.base.getD (shapeAt P k).code default)
    let Z := codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)
    c.main.size = (shapeAt P k).mainRows ∧ c.mask.size = (shapeAt P k).maskRows ∧
    (∀ r, r < (shapeAt P k).mainRows → readE (c.main.getD r zeroE) =
      symG C x ((V k).main ((shapeAt P k).mainDeg == 3) r)
        ((V k).mainTl ((shapeAt P k).mainDeg == 3) r)) ∧
    ∀ r, r < (shapeAt P k).maskRows → readE (c.mask.getD r zeroE) =
      symG Z (x % 2 ^ Z.a) ((V k).mask r) ((V k).maskTl r) := by
  obtain ⟨Ly, hL, e⟩ := lay_some P hP
  simp only [e]
  refine ⟨by simp [Blk.columnOf, hX], by simp [Blk.columnOf, hX], fun r hr => ?_, fun r hr => ?_⟩
  · have hr' : r < X.shape.mainRows := by rw [hX]; exact hr
    have em : (Blk.columnOf X (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0))
        (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0))
        (col P V (Ly.tree.getD k 0) x).toArray).main.getD r zeroE =
        if X.shape.mainDeg == 1 then
          OnBytes.ofF ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + r) 0)
        else E.mk3
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r) 0)
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r + 1) 0)
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r + 2)
            0) := by
      simp [Blk.columnOf, Array.getD_eq_getD_getElem?, hr']
    rw [em, hX]
    have hlen := length_mainSyms P V k x (deg_of_plan P hP k hk)
    have hW : mainW P.sent k = (shapeAt P k).mainRows * (shapeAt P k).mainDeg := rfl
    rcases deg_of_plan P hP k hk with h | h
    · have h11 : ((1 : ℕ) == 1) = true := rfl
      have h13 : ((1 : ℕ) == 3) = false := rfl
      rw [h, h11, if_pos rfl, h13, readE_ofF, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        col_main_at P V hP Ly hL k x r hk (by rw [hlen, hW, h]; omega), mainSyms_one P V k x r h hr]
      show algebraMap GF GE (toF (ofF _)) = _
      rw [toF_ofF, symG_ofF]
      exact symG_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    · have h31 : ((3 : ℕ) == 1) = false := rfl
      have h33 : ((3 : ℕ) == 3) = true := rfl
      rw [h, h31, if_neg (by simp), h33]
      rw [read_three _ _ (symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        ((V k).mainE r) ((V k).mainTlE r)) fun t ht => by
          rw [Nat.add_assoc, col_main_at P V hP Ly hL k x (3 * r + t) hk
            (by rw [hlen, hW, h]; omega)]
          exact mainSyms_three P V k x r t h hr ht]
      exact symG_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  · have hr' : r < X.shape.maskRows := by rw [hX]; exact hr
    have em : (Blk.columnOf X (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0))
        (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0))
        (col P V (Ly.tree.getD k 0) x).toArray).mask.getD r zeroE =
        E.mk3
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r) 0)
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r + 1) 0)
          ((col P V (Ly.tree.getD k 0) x).toArray.getD
            (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r + 2)
            0) := by
      simp [Blk.columnOf, Array.getD_eq_getD_getElem?, hr']
    have hW : maskW P.sent k = (shapeAt P k).maskRows * 3 := rfl
    rw [em]
    exact read_three _ _ _ fun t ht => by
      rw [Nat.add_assoc, col_mask_at P V hP Ly hL k x (3 * r + t) hk
        (by rw [length_maskSyms, hW]; omega)]
      exact maskSyms_three P V k x r t hr ht

/-- **These rows are the held words' rows**, by K1's index. -/
theorem rows_held (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) (k : ℕ)
    (hk : k < P.sent.size) :
    (∀ r j, r < (shapeAt P k).mainRows → (V k).main ((shapeAt P k).mainDeg == 3) r j =
      held w first P V (first + k) .main (r + j * 2 ^ K1.clog (shapeAt P k).mainRows)) ∧
    ∀ r j, r < (shapeAt P k).maskRows → (V k).mask r j =
      held w first P V (first + k) .mask (r + j * 2 ^ K1.clog (shapeAt P k).maskRows) :=
  ⟨fun r j hr => by rw [held_new w first P V k hk, word_main _ _ r j hr],
    fun r j hr => by rw [held_new w first P V k hk, word_mask _ _ r j hr]⟩

/-- **Every word of the column is below the prime.** -/
theorem lt_col (P : K1.Par) (V : ℕ → Rows) (τ x : ℕ) : ∀ u ∈ col P V τ x, u < fieldPrimeWord := by
  have h3 : ∀ (y : GE), ∀ u ∈ words3 (ofE y), u < fieldPrimeWord := by
    intro y u hu
    simp only [words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h | h | h <;> rw [h] <;> exact lt_ofF _
  intro u hu
  unfold col at hu
  rcases List.mem_append.1 hu with h | h
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    unfold mainSyms at hk
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hk
    split at hr
    · exact h3 _ u hr
    · rw [List.mem_singleton.1 hr]
      exact lt_ofF _
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    unfold maskSyms at hk
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hk
    exact h3 _ u hr

/-- **Where the book behind the sending seats message k.** -/
theorem seat_behind {L : Type} (P : K1.Par) (d : DState L) (seeds : List (List E × E))
    (ys : List E) (F : SendFront P d) (k : ℕ) (hk : k < P.sent.size) :
    let lay := (Own.treesMade P.codes P.sent).getD {}
    (K1.behind P d seeds ys).book.place[d.st.oracles.size + k]? =
      some (d.book.trees.size + lay.tree.getD k 0, lay.part.getD k 0) ∧
    ∃ t : Tree, (K1.behind P d seeds ys).book.trees[d.book.trees.size + lay.tree.getD k 0]? =
        some t ∧ t.shape = lay.shapes.getD (lay.tree.getD k 0) {} := by
  obtain ⟨Ly, hL, e⟩ := lay_some P F.plan
  simp only [e]
  have hok : Ground.ok (Ground.recvL d.st d.book P.sent) = true := by
    have hp := F.plan
    simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hp
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    rw [F.codes]
    exact ⟨hp.1.1.1, hp.1.1.2, F.step⟩
  have h5 : Ground.recvP P.gp.firstTree d P.sent =
      some ((Array.range P.sent.size).map (· + d.st.oracles.size),
        K1.recvD P.gp.firstTree d P.sent Ly) :=
    (K1.recvP_iff _ _ _ _ _).2 ⟨hok, Ly, by rw [F.codes]; exact hL, rfl, rfl⟩
  obtain ⟨_, Ly', hL', hS⟩ := Book.recvP_seat P.gp.firstTree d _ P.sent _ h5
  obtain rfl : Ly' = Ly := by
    rw [F.codes, hL] at hL'
    exact (Option.some.inj hL').symm
  have hb : (K1.behind P d seeds ys).book = (K1.recvD P.gp.firstTree d P.sent Ly').book := by
    rw [(behind_rest P d seeds ys).2.2.2.2.2.2.2, hL]
    rfl
  rw [hb]
  obtain ⟨t, h1, h2, _⟩ := hS.made _ (hS.fits k hk).1
  exact ⟨hS.new k hk, t, h1, h2⟩

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.flatL_at
#print axioms Johnson.Prover.Send.flatC_at
#print axioms Johnson.Prover.Send.length_flatC
#print axioms Johnson.Prover.Send.foldl_extract
#print axioms Johnson.Prover.Send.foldl_all
#print axioms Johnson.Prover.Send.symG_ofF
#print axioms Johnson.Prover.Send.lay_some
#print axioms Johnson.Prover.Send.deg_of_plan
#print axioms Johnson.Prover.Send.mine_eq
#print axioms Johnson.Prover.Send.mem_inTree
#print axioms Johnson.Prover.Send.length_mainSyms
#print axioms Johnson.Prover.Send.length_maskSyms
#print axioms Johnson.Prover.Send.col_eq
#print axioms Johnson.Prover.Send.seat_of
#print axioms Johnson.Prover.Send.widths_main
#print axioms Johnson.Prover.Send.widths_mask
#print axioms Johnson.Prover.Send.length_mains
#print axioms Johnson.Prover.Send.length_masks
#print axioms Johnson.Prover.Send.col_main_at
#print axioms Johnson.Prover.Send.col_mask_at
#print axioms Johnson.Prover.Send.length_col
#print axioms Johnson.Prover.Send.mainSyms_three
#print axioms Johnson.Prover.Send.mainSyms_one
#print axioms Johnson.Prover.Send.maskSyms_three
#print axioms Johnson.Prover.Send.read_three
#print axioms Johnson.Prover.Send.send_enc
#print axioms Johnson.Prover.Send.rows_held
#print axioms Johnson.Prover.Send.lt_col
#print axioms Johnson.Prover.Send.seat_behind
