-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/FramesTie.lean: **THE TWO FRAMES' TIE AT THE STAGE**: a member's words at each
leaf, as the description's plain strings hold them, ARE the stretch of the written oracle's column
from the member's first word on. Definitions, statements and proofs.

Two texts read one tree. The row words_are_committed reads it off plain strings: `wordOf G y j t x`
(Johnson/Desc/Msg.lean): the description's oracle at the tree number j cuts tenant t's words out of
the column at leaf x (`Oracle.cut`). The proximity test's law reads it off a written oracle:
`W0 F no book y z` (Sheet.lean): the same column, by the book's place z, at the book's depth and
width; a member's words begin at `layOf m` (Johnson/Desc/K12/Law/TieYOf.lean: `skM` | `skZ` of the
record's tree shape). The equation between the two words (`wordsOf_eq_strOf`)
leaves two premises, hM and hZ. Here they are proved from plain facts.

  `SeatIs no book m j t o`: THE RECORD's SEAT IS THE DESCRIPTION's: six equations: the book's place
    of the member's tree has the file's number j; the book's tree there has the member's shape; the
    member's part is the tenant t; the shape's main | mask symbols, part by part, are the tenants'
    main | mask words; its depth is the oracle's log-length.
  `frames_main`, `frames_mask`: under `SeatIs`, "the tenants' words add up to the oracle's", "every
    leaf below the depth is shown" and "the frame lists the tree no deeper": at EVERY x and every k
    below the tenant's main | mask words: the two readings are one word.
  `hM_at`, `hZ_at`: these at the row's letters (l, seat, i), with `SeatFits` and `ShownAt`
    (Johnson/Desc/Sound/MsgSig.lean) for what they give: hM and hZ to the letter, at
    (d, o) := W0 F no book y m.t and L := layOf m.
  `ShapeIs`; `seatIs_of_made`: `SeatIs` of a member of the plain data D that the record fixes, from
    TWO FACTS ON THE BOOK D.book: the member's place is (a place whose tree has the file's number,
    the tenant); the tree there has the description's shape. (D.book: the record's book; where the
    first fold sends its own mask, that book with the mask's tree received.)
  `depth_at_desc`: "the frame lists the tree no deeper" at every description's data and list of all
    trees.
WHO PAYS WHAT IS LEFT. `SeatFits`: a test on the plan, a premise of the row's own statements.
`ShownAt`: stands in the row's promise (`CfAt`). The description's four (its data are made; the last
clause of its test on the plan; the first two chains tell of as many trees as they send): public.
THE TWO FACTS ON THE BOOK: of the record: earned where the tree is sent, kept by the blocks between:
NOT PAID HERE.
Limits. No soundness is claimed. No record is shown at which the two facts on the book hold. Nothing
is said of a leaf's words beyond the tenant's own.

-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.Law.TieYOf
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.Sound.OraclesAre
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.K12.Law.FirstOkLaw
import OnBytes.Maker.TypingViews

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (Seat1 skM skZ logAt widthAt)
open H2K.Pin (layOf)

/-! ## 1 Lists -/

theorem foldl_add_sum : ∀ (l : List ℕ) (z : ℕ), l.foldl (· + ·) z = z + l.sum
  | [], z => by simp
  | a :: l, z => by
    rw [List.foldl_cons, foldl_add_sum l, List.sum_cons, Nat.add_assoc]

theorem arr_sum (a : Array ℕ) : a.foldl (· + ·) 0 = a.toList.sum := by
  rw [← Array.foldl_toList, foldl_add_sum, Nat.zero_add]

theorem arr_take_sum (a : Array ℕ) (p : ℕ) :
    (a.extract 0 p).foldl (· + ·) 0 = (a.toList.take p).sum := by
  rw [arr_sum]
  simp

theorem getD_cut (c : List UInt64) (s n k : ℕ) (h : k < n) :
    ((c.drop s).take n).getD k 0 = c.getD (s + k) 0 := by
  simp [List.getD_eq_getElem?_getD, h, List.getElem?_drop]

/-! ## 2 The record's seat is the description's -/

/-- **The record's seat is the description's.** j, t: the tree's number through the file and the
tenant; o: what the description tells of that tree. -/
structure SeatIs (no : ℕ → ℕ) (book : TreeBook) (m : Seat1) (j t : ℕ) (o : Oracle) : Prop where
  tree : no m.t = j
  inBook : (book.trees[m.t]?).map (·.shape) = some m.tsh
  part : m.part = t
  main : m.tsh.mainSymbols.toList = o.tenants.map (·.main)
  mask : m.tsh.maskSymbols.toList = o.tenants.map (·.mask)
  log : m.tsh.logN = o.logLength

section
variable {no : ℕ → ℕ} {book : TreeBook} {m : Seat1} {j t : ℕ} {o : Oracle}

theorem SeatIs.logAt (h : SeatIs no book m j t o) : logAt book m.t = o.logLength := by
  have e := h.inBook
  unfold H2K.First.logAt
  cases hT : book.trees[m.t]? with
  | none => rw [hT] at e; cases e
  | some T =>
    rw [hT] at e
    have e' : T.shape = m.tsh := Option.some.inj e
    show T.shape.logN = _
    rw [e', h.log]

theorem SeatIs.widthAt (h : SeatIs no book m j t o)
    (hw : (o.tenants.map fun n => n.main + n.mask).sum = o.words) :
    widthAt book m.t = o.words := by
  have e := h.inBook
  unfold H2K.First.widthAt
  cases hT : book.trees[m.t]? with
  | none => rw [hT] at e; cases e
  | some T =>
    rw [hT] at e
    have e' : T.shape = m.tsh := Option.some.inj e
    show T.shape.mainWidth + T.shape.maskWidth = _
    rw [e', ← hw]
    unfold TreeShape.mainWidth TreeShape.maskWidth
    rw [arr_sum, arr_sum, h.main, h.mask, List.sum_map_add]

theorem SeatIs.oM (h : SeatIs no book m j t o) : (layOf m).oM = o.mainSkip t := by
  show skM m.tsh m.part = _
  unfold H2K.First.skM Oracle.mainSkip
  rw [arr_take_sum, h.main, h.part, List.map_take]

theorem SeatIs.oZ (h : SeatIs no book m j t o) : (layOf m).oZ = o.maskSkip t := by
  show skZ m.tsh m.part = _
  unfold H2K.First.skZ Oracle.maskSkip TreeShape.mainWidth
  rw [arr_sum, arr_take_sum, h.main, h.mask, h.part, List.map_take]

end

/-! ## 3 The two readings are one -/

/-- Beyond every listed depth of the tree the frame has no column. -/
theorem colAt_beyond (F : Frame) (y : F.E.Str) (j a x : ℕ)
    (hd : ∀ e ∈ F.all, e.no = j → e.a ≤ a) (hx : 2 ^ a ≤ x) : colAt F y j x = [] := by
  have hn : posL F.all j x = none := by
    unfold posL
    rw [List.findSome?_eq_none_iff]
    intro i _
    by_cases hj : (F.all.get i).no = j
    · rw [if_pos hj, dif_neg]
      have := hd _ (List.get_mem _ i) hj
      have h2 : 2 ^ (F.all.get i).a ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) this
      omega
    · rw [if_neg hj]
  unfold colAt
  rw [hn]
  rfl

/-- The written oracle's word, written out. -/
theorem wordAt_W0 (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y : F.E.Str) (z x q : ℕ) :
    Slice.wordAt (W0 F no book y z).1 (W0 F no book y z).2 x q =
      if x < 2 ^ logAt book z then
        if q < widthAt book z then (colAt F y (no z) x).getD q 0 else 0
      else 0 := by
  unfold Slice.wordAt
  show (if hx : x < 2 ^ logAt book z then
    if hj : q < widthAt book z then (colIn F y (no z) x).getD q 0 else 0 else 0) = _
  by_cases hx : x < 2 ^ logAt book z
  · rw [dif_pos hx, if_pos hx]
    by_cases hq : q < widthAt book z
    · rw [dif_pos hq, if_pos hq]
      rfl
    · rw [dif_neg hq, if_neg hq]
  · rw [dif_neg hx, if_neg hx]

section
variable {Xi : Type} (G : FileDescription Xi) (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y : F.E.Str)
  (m : Seat1) (j t : ℕ) (o : Oracle) (n : SymbolComponent)

/-- What the plain reading comes to at a leaf. -/
theorem frames_core (ho : G.oracleAt j = some o) (hn : o.tenants[t]? = some n)
    (hs : ∀ x, x < 2 ^ o.logLength → (wordOf G (strsOf F y) j t x).isSome = true)
    (hd : ∀ e ∈ F.all, e.no = j → e.a ≤ o.logLength) (x : ℕ) :
    (x < 2 ^ o.logLength ∧ (colAt F y j x).length = o.words ∧
      wordOf G (strsOf F y) j t x = some
        ⟨((colAt F y j x).drop (o.mainSkip t)).take n.main,
          ((colAt F y j x).drop (o.maskSkip t)).take n.mask⟩) ∨
    (2 ^ o.logLength ≤ x ∧ colAt F y j x = []) := by
  rcases Nat.lt_or_ge x (2 ^ o.logLength) with hx | hx
  · left
    have h1 := hs x hx
    have e : wordOf G (strsOf F y) j t x =
        if (colAt F y j x).length = o.words then some
          ⟨((colAt F y j x).drop (o.mainSkip t)).take n.main,
            ((colAt F y j x).drop (o.maskSkip t)).take n.mask⟩ else none := by
      unfold wordOf Oracle.cut
      rw [ho, Option.bind_some, hn, Option.bind_some]
      rfl
    rw [e] at h1 ⊢
    by_cases hl : (colAt F y j x).length = o.words
    · rw [if_pos hl]
      exact ⟨hx, hl, rfl⟩
    · rw [if_neg hl] at h1
      cases h1
  · exact .inr ⟨hx, colAt_beyond F y j _ x hd hx⟩

/-- **The main words.** -/
theorem frames_main (ho : G.oracleAt j = some o) (hn : o.tenants[t]? = some n)
    (hI : SeatIs no book m j t o)
    (hw : (o.tenants.map fun n => n.main + n.mask).sum = o.words)
    (hs : ∀ x, x < 2 ^ o.logLength → (wordOf G (strsOf F y) j t x).isSome = true)
    (hd : ∀ e ∈ F.all, e.no = j → e.a ≤ o.logLength) (x k : ℕ) (hk : k < n.main) :
    (((wordOf G (strsOf F y) j t x).map (·.main)).getD []).getD k 0 =
      Slice.wordAt (W0 F no book y m.t).1 (W0 F no book y m.t).2 x ((layOf m).oM + k) := by
  rw [wordAt_W0, hI.logAt, hI.widthAt hw, hI.tree, hI.oM]
  rcases frames_core G F y j t o n ho hn hs hd x with ⟨hx, hl, e⟩ | ⟨hx, e⟩
  · rw [e, if_pos hx]
    show (((colAt F y j x).drop (o.mainSkip t)).take n.main).getD k 0 = _
    rw [getD_cut _ _ _ _ hk]
    by_cases hq : o.mainSkip t + k < o.words
    · rw [if_pos hq]
    · rw [if_neg hq, List.getD_eq_default]
      omega
  · rw [if_neg (by omega)]
    have e0 : wordOf G (strsOf F y) j t x = o.cut t [] := by
      unfold wordOf
      rw [ho, Option.bind_some]
      show o.cut t (colAt F y j x) = _
      rw [e]
    rw [e0]
    unfold Oracle.cut
    rw [hn, Option.bind_some]
    split <;> simp

/-- **The mask words.** -/
theorem frames_mask (ho : G.oracleAt j = some o) (hn : o.tenants[t]? = some n)
    (hI : SeatIs no book m j t o)
    (hw : (o.tenants.map fun n => n.main + n.mask).sum = o.words)
    (hs : ∀ x, x < 2 ^ o.logLength → (wordOf G (strsOf F y) j t x).isSome = true)
    (hd : ∀ e ∈ F.all, e.no = j → e.a ≤ o.logLength) (x k : ℕ) (hk : k < n.mask) :
    (((wordOf G (strsOf F y) j t x).map (·.mask)).getD []).getD k 0 =
      Slice.wordAt (W0 F no book y m.t).1 (W0 F no book y m.t).2 x ((layOf m).oZ + k) := by
  rw [wordAt_W0, hI.logAt, hI.widthAt hw, hI.tree, hI.oZ]
  rcases frames_core G F y j t o n ho hn hs hd x with ⟨hx, hl, e⟩ | ⟨hx, e⟩
  · rw [e, if_pos hx]
    show (((colAt F y j x).drop (o.maskSkip t)).take n.mask).getD k 0 = _
    rw [getD_cut _ _ _ _ hk]
    by_cases hq : o.maskSkip t + k < o.words
    · rw [if_pos hq]
    · rw [if_neg hq, List.getD_eq_default]
      omega
  · rw [if_neg (by omega)]
    have e0 : wordOf G (strsOf F y) j t x = o.cut t [] := by
      unfold wordOf
      rw [ho, Option.bind_some]
      show o.cut t (colAt F y j x) = _
      rw [e]
    rw [e0]
    unfold Oracle.cut
    rw [hn, Option.bind_some]
    split <;> simp

end

/-! ## 4 At the row's letters -/

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (l : List (OnBytes.OracleShape × ℕ))
  (seat : Fin l.length → ℕ × ℕ) (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y : F.E.Str)
  (i : Fin l.length) (m : Seat1)

/-- **hM**, to the letter. -/
theorem hM_at (hF : SeatFits G cs l seat) (hS : ShownAt G cs l seat (strsOf F y) i)
    (hI : ∀ o, G.oracleAt (seat i).1 = some o → SeatIs no book m (seat i).1 (seat i).2 o)
    (hd : ∀ o, G.oracleAt (seat i).1 = some o →
      ∀ e ∈ F.all, e.no = (seat i).1 → e.a ≤ o.logLength) :
    ∀ x k, k < (l.get i).1.mainRows * (l.get i).1.mainDeg →
      (((wordOf G (strsOf F y) (seat i).1 (seat i).2 x).map (·.main)).getD []).getD k 0 =
        OnBytes.Slice.wordAt (W0 F no book y m.t).1 (W0 F no book y m.t).2 x
          ((layOf m).oM + k) := by
  obtain ⟨o, n, ho, hn, hlog, hmain, _, _, hw, _⟩ := hF i
  intro x k hk
  exact frames_main G F no book y m _ _ o n ho hn (hI o ho) hw (by rw [hlog]; exact hS)
    (hd o ho) x k (by rw [hmain]; exact hk)

/-- **hZ**, to the letter. -/
theorem hZ_at (hF : SeatFits G cs l seat) (hS : ShownAt G cs l seat (strsOf F y) i)
    (hI : ∀ o, G.oracleAt (seat i).1 = some o → SeatIs no book m (seat i).1 (seat i).2 o)
    (hd : ∀ o, G.oracleAt (seat i).1 = some o →
      ∀ e ∈ F.all, e.no = (seat i).1 → e.a ≤ o.logLength) :
    ∀ x k, k < (l.get i).1.maskRows * 3 →
      (((wordOf G (strsOf F y) (seat i).1 (seat i).2 x).map (·.mask)).getD []).getD k 0 =
        OnBytes.Slice.wordAt (W0 F no book y m.t).1 (W0 F no book y m.t).2 x
          ((layOf m).oZ + k) := by
  obtain ⟨o, n, ho, hn, hlog, _, hmask, _, hw, _⟩ := hF i
  intro x k hk
  exact frames_mask G F no book y m _ _ o n ho hn (hI o ho) hw (by rw [hlog]; exact hS)
    (hd o ho) x k (by rw [hmask]; exact hk)

end

/-! ## 5 What is left, cut down -/

/-- **The record's tree shape is what the description tells of the tree**: part by part the main |
mask symbols are the tenants' main | mask words; the depth is the log-length. -/
structure ShapeIs (tsh : TreeShape) (o : Oracle) : Prop where
  main : tsh.mainSymbols.toList = o.tenants.map (·.main)
  mask : tsh.maskSymbols.toList = o.tenants.map (·.mask)
  log : tsh.logN = o.logLength

/-- **`SeatIs` of a member that the record's own data hold**, from two facts on the book: the
member's place in the book is (a place whose tree has the file's number j, the tenant t); the tree
there has the description's shape. D: the plain data that the record fixes (`Fixes`, Sheet.lean);
hm: what `gpOf` has made (`made_of`, Johnson/Desc/K12/Law/FirstOkLaw.lean). -/
theorem seatIs_of_made {p : P12} {t12 : T12} {a : Fmt.M1.Stage} {L : GroupLayout}
    {D : H2K.First.Plain} (hm : H2K.First.Made p t12 a L D) (no : ℕ → ℕ)
    (q : Fin D.mems.length) (j t : ℕ) (o : Oracle)
    (hp : ∀ z u, D.book.place[(D.mems.get q).id]? = some (z, u) → no z = j ∧ u = t)
    (hsh : ∀ z u T, D.book.place[(D.mems.get q).id]? = some (z, u) →
      D.book.trees[z]? = some T → ShapeIs T.shape o) :
    SeatIs no D.book (D.mems.get q) j t o := by
  obtain ⟨_, _, hpl, T, hT, e1, _⟩ := hm.mem q
  obtain ⟨h1, h2⟩ := hp _ _ hpl
  have h3 := hsh _ _ T hpl hT
  rw [e1] at h3
  exact ⟨h1, by rw [hT]; exact congrArg some e1, h2, h3.main, h3.mask, h3.log⟩

/-- **"The frame lists the tree no deeper" at every description**: at the frame of the data D of a
description G over the list of all trees: by `oraclesAre` (Johnson/Desc/Sound/OraclesAre.lean). -/
theorem depth_at_desc {Xi : Type} (G : FileDescription Xi) (file : String) (D : WholeD)
    (h : G.data file = .ok D) (hs : G.sentFit = true)
    (c₁ : (oraclesOf G.first.blocksInOrder).length = D.t₁) (c₂ : (oraclesOf G.shared.blocksInOrder).length = D.t₂)
    (key : ℕ → ℕ) (ft j : ℕ) (o : Oracle) (ho : G.oracleAt j = some o) :
    ∀ e ∈ (frameAt D (allOf D) key ft).all, e.no = j → e.a ≤ o.logLength := by
  intro e he hj
  obtain ⟨sh, g1, g2, _⟩ := oraclesAre Xi G file D h hs c₁ c₂ j o ho
  obtain ⟨j', _, rfl⟩ := List.mem_map.1 (show e ∈ allOf D from he)
  have e' : j' = j := hj
  subst e'
  show (D.depth j').getD 0 ≤ _
  rw [WholeD.depth_shape, g1, g2]
  exact Nat.le_refl _

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.frames_main
#print axioms VerifiableInference.Desc.K12.Coin.frames_mask
#print axioms VerifiableInference.Desc.K12.Coin.hM_at
#print axioms VerifiableInference.Desc.K12.Coin.hZ_at
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_of_made
#print axioms VerifiableInference.Desc.K12.Coin.depth_at_desc
