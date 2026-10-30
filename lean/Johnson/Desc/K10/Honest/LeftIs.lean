-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/LeftIs.lean: what a fold leaves, in the code switch's terms, written in the library's terms.

What is proved. `leftAt S old w` (Johnson/Desc/K2/Honest/Carry/Left.lean) is what the fold that closed a group left, of
the words w, in the terms of the code switch's honest prover. old: the single rows that the fold returned (`SingleRows`,
OnBytes/Iop/Fold.lean). The law on the closing of a segment (`closeBase_holds`, Johnson/Desc/K10/Honest/Holds.lean) ends
in an equation in the library's terms: `vecS`, `foldMsg` of `msgOf` of `tablesOf`, and `keptVal`. This file shows that
`ClaimTrue` at `leftAt` is, beside its own first clause, an equation of that form, at the stage `stageAt`, the fresh
table `freshAt` and the point `pointAt`.

  **`left_is`**      row by row: `leftAt`'s main row and its two mask rows, at the places below the codes' message
                   lengths, are the three parts of `foldedAt`; each kept member's table, cut to its real rows, is the
                   kept part of `tablesOf`
  **`claimTrue_iff_tables`**   `ClaimTrue (sizesAt S old T) old (leftAt S old w)` holds exactly if its own first clause
                   holds and `∑ j, vecS … j * foldedAt … j + keptVal … = readE old.target`
  `LeftFits.facts`  what is used of `foldShapeOk`
  `mu_is`           the two tables that `foldEndAt` folds are `msgOf` of `tablesOf`
  `kept_seat`       `switchKept` and `keptNos` name the same seat (seat: see LeftTables.lean)
  `left_kept`       a kept member's table, cut to its real rows, is the kept part of `tablesOf`
  `kept_form`       one summand of `ClaimTrue` is one of `keptVal`
The other lemmas are small steps. The two theorems are proved under `LeftFits S G old` and `Padded S w`.

What is defined.
  `stageAt`, `freshAt`, `pointAt`   the stage, the fresh table and the point that `foldEndAt` uses at `leftAt`'s
                   arguments
  `foldedAt`        the three folded messages: the group's two tables are the library's (`tablesOf`), the fresh table is
                   `freshAt`
  `LeftFits`        the public premises, on the statement, the group and the single rows only: the layout's blocks are
                   aligned, inside and disjoint (`LayFacts`); no member occurs twice; the fold's shape fits
                   (`foldShapeOk`)
  `pairs`, `shapeAt`, `rowsAt`, `mainForm`, `maskForm`, `muAt`, `keptNos`   helpers, named so that lemmas can speak of
                   them: `shapeAt`, `muAt`, `keptNos`, and `mainForm`, `maskForm` ("mainOf", "maskOf", each at one
                   reader) are local definitions of `foldEndAt` at `leftAt`'s arguments; `rowsAt` is the argument "M"
                   that `leftAt` hands it; `pairs` is the list of (member, kept mark) from which `membersAt` and
                   `switchKept` are made

What is used of `foldShapeOk`: `LeftFits.facts`. Why the other premises are needed: see the head of LeftTables.lean. For
the words that a witness gives at S, `Padded` is `padded_wordsOn` (Johnson/Desc/Means/ItemsTab.lean); for arbitrary
words it is an assumption.

Limits. That `ClaimTrue` holds is not shown. `closeBase_holds` is not called. Its stage, fresh table and point are free,
with premises of their own (the stage's four numbers, `Pairs`, `Shows`); that `stageAt`, `freshAt` and `pointAt` meet
them is not shown here, and neither is `ClaimTrue`'s first clause (LeftClaim.lean shows three of the four numbers, that
`pointAt` is the point that the rounds show, and the first clause; the fourth number, `Pairs` at `freshAt` and `Shows`
are premises there). `freshAt` is `leftAt`'s own reading of the words at `old.fresh`, so the second mask row's equation
holds by unfolding. Nothing is asked of `old.fresh`, `old.masks` or the length of `old.gamma`. `leftAt` is `foldEndAt`
at the single rows' own layout; that `foldEnd`, which makes the layout anew, gives the same is not shown. Nothing is
said of tails, pads or symbols (`Left.mainTail`, `maskTail`, `Held.tail`). `Codes.lengthsOk` is not asked: both sides
sum over the places below the codes' own lengths; on a kept member's table both sum over 2 ^ (row bits + `logEll`)
indices (a kept member without a main row: both sums are 0). That `foldMsg` is the program's fold is not shown here. The
file names no state, no round and no witness. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K2.Honest.Carry.Left
import Johnson.Desc.K10.Honest.LeftTables
import Johnson.Desc.K10.Honest.Values
import Johnson.Desc.Own.FoldMean
import Johnson.Desc.Own.FoldAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open ProofFile.Honest.K10.Values (keptLen)

/-! ## 1 The terms and the premises -/

/-- The stage at which the single rows' fold is read: `foldEndAt`'s own "s". -/
def stageAt (S : Statement) (old : SingleRows) : Sg :=
  stageOf S.codes old.code old.maskCode old.layout

/-- The fresh mask's table, of the words: `foldEndAt`'s own "φ" at `leftAt`'s "fresh". -/
def freshAt (S : Statement) (old : SingleRows) (w : Words GE) : (stageAt S old).cFr.J → GE :=
  fun x => w old.fresh .mask
    (Sz.rowNo x.1 + x.2.val * 2 ^ ceilLog2 (S.oracles.getD old.fresh default).shape.maskRows)

/-- The fold's point, off the single rows' challenges: `foldEndAt`'s own "pt". -/
def pointAt (S : Statement) (old : SingleRows) :
    Fin ((stageAt S old).h + (stageAt S old).g) → GE :=
  fun i => (old.gamma.map readE).getD i.val zeroG

/-- The three folded messages: the group's two tables are the library's (`tablesOf`), the fresh table is `freshAt`. -/
def foldedAt (S : Statement) (old : SingleRows) (w : Words GE) : (stageAt S old).cMid.J → GE :=
  foldMsg (stageAt S old) (msgOf (stageAt S old) (tablesOf S old.layout w)) (freshAt S old w)
    (pointAt S old)

/-- The public premises: on the statement, the group and the single rows only. -/
structure LeftFits (S : Statement) (G : Group) (old : SingleRows) : Prop where
  lay : LayFacts S G old.layout
  once : old.layout.members.toList.Nodup
  shape : foldShapeOk S { code := old.code, maskCode := old.maskCode, layout := old.layout } = true

/-! ## 2 What the shape's test gives; a member's seat -/

variable {S : Statement} {G : Group} {old : SingleRows}

/-- What the test on the fold's shape gives: h ≤ k; the four lists have one length; the statement has every member, with
its main rows under the single rows' code. -/
theorem LeftFits.facts (H : LeftFits S G old) :
    old.layout.h ≤ old.layout.k ∧ old.layout.kept.size = old.layout.members.size ∧
      old.layout.mainFirst.size = old.layout.members.size ∧
      old.layout.maskFirst.size = old.layout.members.size ∧
      ∀ i < old.layout.members.size, ∃ x, S.oracles[old.layout.members.getD i noId]? = some x ∧
        (x.shape.mainRows = 0 ∨ x.shape.code = old.code) := by
  obtain ⟨_, _, _, _, _, h2, _, _, h5, h6, h7, h8, _⟩ :=
    (Own.foldShapeFits_iff S _).1 ((Own.foldShapeFits_agrees S _).symm.trans H.shape)
  refine ⟨h2, h5, h6, h7, fun i hi => ?_⟩
  obtain ⟨x, hx, hc, _⟩ := h8 i hi
  exact ⟨x, hx, hc⟩

/-- The stage has as many row variables as the layout. -/
theorem stage_rows (H : LeftFits S G old) :
    (stageAt S old).h + (stageAt S old).g = old.layout.k := by
  have := H.facts.1
  show old.layout.h + (old.layout.k - old.layout.h) = old.layout.k
  omega

/-- An array's entry as its list has it. -/
theorem toList_get {α : Type} (xs : Array α) (d : α) {i : Nat} (hi : i < xs.size) :
    xs.toList[i]? = some (xs.getD i d) := by
  rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

/-- The pairs (member, kept mark), in the members' order. -/
def pairs (old : SingleRows) : List (Nat × Bool) := (old.layout.members.zip old.layout.kept).toList

/-- There are as many pairs as members. -/
theorem pairs_length (hk : old.layout.kept.size = old.layout.members.size) :
    (pairs old).length = old.layout.members.size := by
  unfold pairs
  rw [Array.length_toList, Array.size_zip, hk, Nat.min_self]

/-- The pair at a seat. -/
theorem pairs_get (hk : old.layout.kept.size = old.layout.members.size) {i : Nat}
    (hi : i < old.layout.members.size) :
    (pairs old)[i]? = some (old.layout.members.getD i noId, old.layout.kept.getD i false) := by
  unfold pairs
  rw [Array.toList_zip]
  exact List.getElem?_zip_eq_some.2 ⟨toList_get _ noId hi, toList_get _ false (by omega)⟩

/-- `foldEndAt`'s own "shape", at `leftAt`'s members. -/
def shapeAt (S : Statement) (old : SingleRows) (i : Nat) : OracleShape :=
  (((membersAt S old)[i]?).map (·.shape)).getD {}

/-- At a seat, `shapeAt` is the member's shape at S, read over the extension field. -/
theorem shapeAt_seat (hk : old.layout.kept.size = old.layout.members.size) {i : Nat}
    (hi : i < old.layout.members.size) :
    shapeAt S old i =
      { (S.oracles.getD (old.layout.members.getD i noId) default).shape with mainDeg := 3 } := by
  unfold shapeAt membersAt
  rw [List.getElem?_map, show (old.layout.members.zip old.layout.kept).toList = pairs old from rfl,
    pairs_get hk hi]
  rfl

/-- The shape of a message that the statement has. -/
theorem there_shape {o : Nat} {x : OnBytes.Oracle} (hx : S.oracles[o]? = some x) :
    (S.oracles.getD o default).shape = x.shape := by
  rw [Array.getD_eq_getD_getElem?, hx]
  rfl

/-- Its number of row bits. -/
theorem there_bits {o : Nat} {x : OnBytes.Oracle} (hx : S.oracles[o]? = some x) (part : Part) :
    S.rowBits o part = ceilLog2 (x.shape.rows part) := by
  unfold Statement.rowBits
  rw [hx]

/-- Its number of real rows. -/
theorem there_real {o : Nat} {x : OnBytes.Oracle} (hx : S.oracles[o]? = some x) (part : Part) :
    realRows S o part = x.shape.rows part := by
  unfold realRows
  rw [hx]

/-- The code switch's zero is the field's. -/
theorem zeroG_is : zeroG = (0 : GE) := readE_zero

/-! ## 3 The two tables that `foldEndAt` folds -/

/-- `leftAt`'s own "M". -/
def rowsAt (S : Statement) (old : SingleRows) (w : Words GE) (i : Nat) : Johnson.Prover.Send.Rows :=
  rowsOfWords w (old.layout.members.getD i noId)
    (S.oracles.getD (old.layout.members.getD i noId) default).shape

/-- `foldEndAt`'s own "mainOf (fun R e => R.main e)". -/
def mainForm (S : Statement) (old : SingleRows) (w : Words GE) (ρ j : Nat) : GE :=
  match tableRow old.layout.mainFirst (fun i => (shapeAt S old i).mainRows) ρ with
  | some (i, b) => (rowsAt S old w i).main ((shapeAt S old i).mainDeg == 3) b j
  | none => zeroG

/-- `foldEndAt`'s own "maskOf (·.mask)". -/
def maskForm (S : Statement) (old : SingleRows) (w : Words GE) (ρ j : Nat) : GE :=
  match tableRow old.layout.maskFirst (fun i => (shapeAt S old i).maskRows) ρ with
  | some (i, b) => (rowsAt S old w i).mask b j
  | none => zeroG

/-- `foldEndAt`'s own "μ". -/
def muAt (S : Statement) (old : SingleRows) (w : Words GE) : (stageAt S old).cIn.J → GE :=
  Sum.elim (fun x => mainForm S old w (Sz.rowNo x.1) x.2.val)
    (fun x => maskForm S old w (Sz.rowNo x.1) x.2.val)

/-- `foldEndAt`'s main table is `tablesOf`'s. -/
theorem mainForm_is (H : LeftFits S G old) (w : Words GE) (hp : Padded S w) (ρ j : Nat)
    (hρ : ρ < 2 ^ old.layout.k) :
    mainForm S old w ρ j = (tablesOf S old.layout w).main (ρ + 2 ^ old.layout.k * j) := by
  obtain ⟨_, hk, hm, _, hx⟩ := H.facts
  rw [← main_is H.lay H.once hm w hp ρ j hρ]
  unfold mainForm
  have hrows : ∀ i, i < old.layout.mainFirst.size →
      (shapeAt S old i).mainRows = realRows S (old.layout.members.getD i noId) .main := by
    intro i hi
    obtain ⟨x, e, _⟩ := hx i (by omega)
    rw [shapeAt_seat hk (by omega), there_shape e, there_real e]
    rfl
  rw [tableRow_congr old.layout.mainFirst _ _ ρ hrows]
  cases h : tableRow old.layout.mainFirst
      (fun i => realRows S (old.layout.members.getD i noId) .main) ρ with
  | none => exact zeroG_is
  | some p =>
    obtain ⟨i, b⟩ := p
    have hi : i < old.layout.members.size := by
      have := tableRow_lt h
      omega
    obtain ⟨x, e, _⟩ := hx i hi
    show (rowsAt S old w i).main ((shapeAt S old i).mainDeg == 3) b j =
      w (old.layout.members.getD i noId) .main
        (b + j * 2 ^ S.rowBits (old.layout.members.getD i noId) .main)
    rw [shapeAt_seat hk hi, there_bits e]
    unfold rowsAt
    rw [there_shape e]
    rfl

/-- `foldEndAt`'s mask table is `tablesOf`'s. -/
theorem maskForm_is (H : LeftFits S G old) (w : Words GE) (hp : Padded S w) (ρ j : Nat)
    (hρ : ρ < 2 ^ old.layout.h) :
    maskForm S old w ρ j = (tablesOf S old.layout w).mask (ρ + 2 ^ old.layout.h * j) := by
  obtain ⟨_, hk, _, hz, hx⟩ := H.facts
  rw [← mask_is H.lay H.once hz w hp ρ j hρ]
  unfold maskForm
  have hrows : ∀ i, i < old.layout.maskFirst.size →
      (shapeAt S old i).maskRows = realRows S (old.layout.members.getD i noId) .mask := by
    intro i hi
    obtain ⟨x, e, _⟩ := hx i (by omega)
    rw [shapeAt_seat hk (by omega), there_shape e, there_real e]
    rfl
  rw [tableRow_congr old.layout.maskFirst _ _ ρ hrows]
  cases h : tableRow old.layout.maskFirst
      (fun i => realRows S (old.layout.members.getD i noId) .mask) ρ with
  | none => exact zeroG_is
  | some p =>
    obtain ⟨i, b⟩ := p
    have hi : i < old.layout.members.size := by
      have := tableRow_lt h
      omega
    obtain ⟨x, e, _⟩ := hx i hi
    show (rowsAt S old w i).mask b j =
      w (old.layout.members.getD i noId) .mask
        (b + j * 2 ^ S.rowBits (old.layout.members.getD i noId) .mask)
    rw [there_bits e]
    unfold rowsAt
    rw [there_shape e]
    rfl

/-- **`foldEndAt`'s tables are the library's.** -/
theorem mu_is (H : LeftFits S G old) (w : Words GE) (hp : Padded S w) :
    muAt S old w = msgOf (stageAt S old) (tablesOf S old.layout w) := by
  have hk := stage_rows H
  funext x
  cases x with
  | inl x =>
    have hr : Sz.rowNo x.1 < 2 ^ old.layout.k := hk ▸ rowNo_lt x.1
    exact (mainForm_is H w hp _ x.2.val hr).trans
      (congrArg (fun t => (tablesOf S old.layout w).main (Sz.rowNo x.1 + 2 ^ t * x.2.val)) hk.symm)
  | inr x =>
    exact maskForm_is H w hp _ x.2.val (rowNo_lt x.1)

/-! ## 4 The main row and the two mask rows of `leftAt` -/

/-- `leftAt`'s main row, unfolded. -/
theorem left_main (S : Statement) (old : SingleRows) (w : Words GE)
    (j : Fin (stageAt S old).C.l) :
    (leftAt S old w).main j.val =
      foldMsg (stageAt S old) (muAt S old w) (freshAt S old w) (pointAt S old) (.inl j) :=
  dif_pos j.isLt

/-- `leftAt`'s first mask row (the fold of the group's mask rows), unfolded. -/
theorem left_mask0 (S : Statement) (old : SingleRows) (w : Words GE)
    (i : Fin (stageAt S old).Z.l) :
    (leftAt S old w).mask 0 i.val =
      foldMsg (stageAt S old) (muAt S old w) (freshAt S old w) (pointAt S old) (.inr (.inl i)) :=
  (dif_pos i.isLt).trans (if_pos rfl)

/-- `leftAt`'s second mask row (the fold of the fresh mask's rows), unfolded. -/
theorem left_mask1 (S : Statement) (old : SingleRows) (w : Words GE)
    (i : Fin (stageAt S old).Z.l) :
    (leftAt S old w).mask 1 i.val =
      foldMsg (stageAt S old) (muAt S old w) (freshAt S old w) (pointAt S old) (.inr (.inr i)) :=
  (dif_pos i.isLt).trans (if_neg (by decide))

/-! ## 5 The kept members -/

/-- A list is the list of its entries, in order. -/
theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The entries at the seats where a test says yes, in order, are the entries at which it says yes. -/
theorem filter_seats {α : Type} (l : List α) (p : α → Bool) (d : α) :
    ((List.range l.length).filter fun i => p (l.getD i d)).map (fun i => l.getD i d) =
      l.filter p := by
  have e : ((List.range l.length).map fun i => l.getD i d).filter p =
      ((List.range l.length).filter (p ∘ fun i => l.getD i d)).map fun i => l.getD i d :=
    List.filter_map
  rw [range_map_getD] at e
  exact e.symm

/-- `foldEndAt`'s own "keptNos", at `leftAt`'s members. -/
def keptNos (S : Statement) (old : SingleRows) : List Nat :=
  (List.range (membersAt S old).length).filter fun i =>
    (((membersAt S old)[i]?).map (·.kept)).getD false

/-- `keptNos`, in terms of the pairs. -/
theorem keptNos_eq (S : Statement) (old : SingleRows) :
    keptNos S old =
      (List.range (pairs old).length).filter fun i => ((pairs old).getD i (noId, false)).2 := by
  unfold keptNos membersAt
  rw [show (old.layout.members.zip old.layout.kept).toList = pairs old from rfl, List.length_map]
  refine List.filter_congr fun i _ => ?_
  rw [List.getElem?_map, List.getD_eq_getElem?_getD]
  cases (pairs old)[i]? <;> rfl

/-- **The kept member number a**: `switchKept` and `keptNos` name the same seat. -/
theorem kept_seat (hk : old.layout.kept.size = old.layout.members.size) {a o : Nat}
    (h : (switchKept old)[a]? = some o) :
    ∃ i, (keptNos S old)[a]? = some i ∧ i < old.layout.members.size ∧
      old.layout.members.getD i noId = o ∧ old.layout.kept.getD i false = true := by
  have e : (switchKept old).toList =
      ((keptNos S old).map fun i => (pairs old).getD i (noId, false)).map (·.1) := by
    rw [keptNos_eq, filter_seats (pairs old) (·.2) (noId, false)]
    unfold switchKept pairs
    rw [Array.toList_map, Array.toList_filter]
  rw [← Array.getElem?_toList, e, List.getElem?_map, List.getElem?_map] at h
  cases hi : (keptNos S old)[a]? with
  | none =>
    rw [hi] at h
    cases h
  | some i =>
    rw [hi] at h
    have hmem : i ∈ keptNos S old := List.mem_of_getElem? hi
    rw [keptNos_eq, List.mem_filter, List.mem_range, pairs_length hk] at hmem
    have hg : (pairs old).getD i (noId, false) =
        (old.layout.members.getD i noId, old.layout.kept.getD i false) := by
      rw [List.getD_eq_getElem?_getD, pairs_get hk hmem.1]
      rfl
    rw [hg] at hmem
    refine ⟨i, rfl, hmem.1, ?_, hmem.2⟩
    have this : ((pairs old).getD i (noId, false)).1 = o := Option.some.inj h
    rw [hg] at this
    exact this

/-- **A kept member's table**: `leftAt`'s, cut to the real rows, is the kept part of `tablesOf`. -/
theorem left_kept (H : LeftFits S G old) (w : Words GE) (hp : Padded S w) (a o : Nat)
    (h : (switchKept old)[a]? = some o) (i : Nat) :
    ((leftAt S old w).kept a).entryIn (S.oracles.getD o default).shape i =
      (tablesOf S old.layout w).kept o i := by
  obtain ⟨_, hk, _, _, hx⟩ := H.facts
  obtain ⟨s, hs, hlt, ho, hkept⟩ := kept_seat (S := S) hk h
  obtain ⟨x, e, _⟩ := hx s hlt
  rw [ho] at e
  have hK : KeptAt old.layout o := ⟨s, ho ▸ find_seat H.once hlt, hkept⟩
  rw [tablesOf_kept_at w hK i]
  have hfield : ((leftAt S old w).kept a).main =
      (rowsAt S old w s).main ((shapeAt S old s).mainDeg == 3) := by
    show (rowsAt S old w ((keptNos S old).getD a (membersAt S old).length)).main
      ((shapeAt S old ((keptNos S old).getD a (membersAt S old).length)).mainDeg == 3) = _
    rw [List.getD_eq_getElem?_getD, hs]
    rfl
  unfold Held.entryIn Held.entry
  rw [hfield, shapeAt_seat hk hlt, there_shape e]
  by_cases hr : i % 2 ^ ceilLog2 x.shape.mainRows < x.shape.mainRows
  · rw [if_pos hr]
    unfold rowsAt
    rw [ho, there_shape e]
    show w o .main (i % 2 ^ ceilLog2 x.shape.mainRows +
      i / 2 ^ ceilLog2 x.shape.mainRows * 2 ^ ceilLog2 x.shape.mainRows) = _
    rw [Nat.mul_comm, Nat.mod_add_div]
  · rw [if_neg hr]
    refine (hp o .main i ?_).symm
    rw [there_real e, there_bits e]
    exact Nat.le_of_not_lt hr

/-! ## 6 The two theorems -/

/-- **Row by row**: `leftAt`'s rows are the parts of `foldedAt`, its kept tables those of `tablesOf`. -/
theorem left_is (S : Statement) (G : Group) (old : SingleRows) (w : Words GE)
    (H : LeftFits S G old) (hp : Padded S w) :
    (∀ j : Fin (stageAt S old).C.l, (leftAt S old w).main j.val = foldedAt S old w (.inl j)) ∧
    (∀ i : Fin (stageAt S old).Z.l,
      (leftAt S old w).mask 0 i.val = foldedAt S old w (.inr (.inl i)) ∧
      (leftAt S old w).mask 1 i.val = foldedAt S old w (.inr (.inr i))) ∧
    ∀ (a o : Nat), (switchKept old)[a]? = some o → ∀ i : Nat,
      ((leftAt S old w).kept a).entryIn (S.oracles.getD o default).shape i =
        (tablesOf S old.layout w).kept o i := by
  have e := mu_is H w hp
  refine ⟨fun j => ?_, fun i => ⟨?_, ?_⟩, fun a o h i => left_kept H w hp a o h i⟩
  · rw [left_main, e]
    rfl
  · rw [left_mask0, e]
    rfl
  · rw [left_mask1, e]
    rfl

/-- The value of one form on a kept member: `ClaimTrue`'s summand is `keptVal`'s. -/
theorem kept_form (H : LeftFits S G old) (T : SwitchTarget) (w : Words GE) (hp : Padded S w)
    (f : KeptForm) (hf : f.oracle ∈ (switchKept old).toList) :
    (match (switchKept old).toList.idxOf? f.oracle with
      | some a =>
        ∑ i ∈ Finset.range
            (2 ^ (ceilLog2 ((sizesAt S old T).kept.getD a {}).mainRows +
              ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).logEll)),
          formAt f.c i * ((leftAt S old w).kept a).entryIn ((sizesAt S old T).kept.getD a {}) i
      | none => 0) =
      ∑ i ∈ Finset.range (keptLen S f.oracle),
        formAt f.c i * (tablesOf S old.layout w).kept f.oracle i := by
  obtain ⟨_, hk, _, _, hx⟩ := H.facts
  cases ha : (switchKept old).toList.idxOf? f.oracle with
  | none => exact absurd hf (List.idxOf?_eq_none_iff.1 ha)
  | some a =>
    obtain ⟨hlt, hget, _⟩ := List.idxOf?_eq_some_iff.1 ha
    have hsw : (switchKept old)[a]? = some f.oracle := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hlt, hget]
    have hshape : (sizesAt S old T).kept.getD a {} = (S.oracles.getD f.oracle default).shape := by
      show ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).getD a {} = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt, hget]
      rfl
    obtain ⟨s, _, hs, ho, _⟩ := kept_seat (S := S) hk hsw
    obtain ⟨x, e, hcode⟩ := hx s hs
    rw [ho] at e
    show (∑ i ∈ Finset.range _, formAt f.c i *
      ((leftAt S old w).kept a).entryIn ((sizesAt S old T).kept.getD a {}) i) = _
    rw [hshape]
    simp only [left_kept H w hp a f.oracle hsw]
    rw [there_shape e]
    rcases Nat.eq_zero_or_pos x.shape.mainRows with h0 | hpos
    · -- no main row: both sums are 0
      have hz : ∀ i, (tablesOf S old.layout w).kept f.oracle i = 0 := by
        intro i
        have hK : KeptAt old.layout f.oracle := by
          obtain ⟨s', _, hs', ho', hk'⟩ := kept_seat (S := S) hk hsw
          exact ⟨s', ho' ▸ find_seat H.once hs', hk'⟩
        rw [tablesOf_kept_at w hK i]
        refine hp f.oracle .main i ?_
        rw [there_real e]
        show x.shape.mainRows ≤ _
        omega
      simp only [hz, mul_zero, Finset.sum_const_zero]
    · have hhas : S.has f.oracle .main = true := by
        unfold Statement.has
        rw [e]
        exact decide_eq_true hpos
      have hc : x.shape.code = old.code := hcode.resolve_left (by omega)
      have hlen : keptLen S f.oracle = 2 ^ (ceilLog2 x.shape.mainRows +
          ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).logEll) := by
        show tableSize S f.oracle .main = _
        unfold tableSize Statement.tableBits Statement.placeBits
        rw [if_pos hhas, there_bits e, e]
        have hne : (x.shape.rows .main == 0) = false := by
          show (x.shape.mainRows == 0) = false
          exact beq_false_of_ne (by omega)
        simp only [hne, Bool.false_eq_true, if_false, hc]
        rfl
      rw [hlen]

/-- **`ClaimTrue` at `leftAt`, in the library's terms.** -/
theorem claimTrue_iff_tables (S : Statement) (G : Group) (old : SingleRows) (T : SwitchTarget)
    (w : Words GE) (H : LeftFits S G old) (hp : Padded S w) :
    ClaimTrue (sizesAt S old T) old (leftAt S old w) ↔
      (∀ f ∈ old.kept.toList, f.oracle ∈ (switchKept old).toList) ∧
      ∑ j, vecS (stageAt S old) old j * foldedAt S old w j +
        keptVal (keptLen S) (tablesOf S old.layout w).kept old.kept = readE old.target := by
  obtain ⟨h1, h2, _⟩ := left_is S G old w H hp
  unfold ClaimTrue
  refine and_congr_right fun hn => ?_
  have eMain : (∑ j ∈ Finset.range
        ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).ell,
      formAt old.c j * (leftAt S old w).main j) =
      ∑ j : Fin (stageAt S old).C.l, vecS (stageAt S old) old (.inl j) * foldedAt S old w (.inl j) := by
    show (∑ j ∈ Finset.range (stageAt S old).C.l, formAt old.c j * (leftAt S old w).main j) = _
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; rfl
  have eMask : (∑ r ∈ Finset.range 2, ∑ i ∈ Finset.range
        ((sizesAt S old T).codes.mask.getD (sizesAt S old T).maskCode default).ell,
      readE ((old.d.getD r #[]).getD i zeroE) * (leftAt S old w).mask r i) =
      (∑ i : Fin (stageAt S old).Z.l,
        vecS (stageAt S old) old (.inr (.inl i)) * foldedAt S old w (.inr (.inl i))) +
      ∑ i : Fin (stageAt S old).Z.l,
        vecS (stageAt S old) old (.inr (.inr i)) * foldedAt S old w (.inr (.inr i)) := by
    show (∑ r ∈ Finset.range 2, ∑ i ∈ Finset.range (stageAt S old).Z.l,
      readE ((old.d.getD r #[]).getD i zeroE) * (leftAt S old w).mask r i) = _
    rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range, Finset.sum_range]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ => by rw [(h2 i).1]; rfl
    · exact Finset.sum_congr rfl fun i _ => by rw [(h2 i).2]; rfl
  have eKept : (old.kept.toList.map fun f =>
      match (switchKept old).toList.idxOf? f.oracle with
      | some a =>
        ∑ i ∈ Finset.range
            (2 ^ (ceilLog2 ((sizesAt S old T).kept.getD a {}).mainRows +
              ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).logEll)),
          formAt f.c i * ((leftAt S old w).kept a).entryIn ((sizesAt S old T).kept.getD a {}) i
      | none => 0).sum = keptVal (keptLen S) (tablesOf S old.layout w).kept old.kept := by
    unfold keptVal
    exact congrArg List.sum (List.map_congr_left fun f hf => kept_form H T w hp f (hn f hf))
  have eSum : (∑ j, vecS (stageAt S old) old j * foldedAt S old w j) =
      (∑ j : Fin (stageAt S old).C.l,
        vecS (stageAt S old) old (.inl j) * foldedAt S old w (.inl j)) +
      ((∑ i : Fin (stageAt S old).Z.l,
        vecS (stageAt S old) old (.inr (.inl i)) * foldedAt S old w (.inr (.inl i))) +
      ∑ i : Fin (stageAt S old).Z.l,
        vecS (stageAt S old) old (.inr (.inr i)) * foldedAt S old w (.inr (.inr i))) := by
    rw [Fintype.sum_sum_type (fun j : (stageAt S old).cMid.J =>
      vecS (stageAt S old) old j * foldedAt S old w j)]
    refine congrArg₂ (· + ·) rfl ?_
    exact Fintype.sum_sum_type _
  show (∑ j ∈ Finset.range
        ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).ell,
      formAt old.c j * (leftAt S old w).main j) +
    (old.kept.toList.map fun f =>
      match (switchKept old).toList.idxOf? f.oracle with
      | some a =>
        ∑ i ∈ Finset.range
            (2 ^ (ceilLog2 ((sizesAt S old T).kept.getD a {}).mainRows +
              ((sizesAt S old T).codes.base.getD (sizesAt S old T).code default).logEll)),
          formAt f.c i * ((leftAt S old w).kept a).entryIn ((sizesAt S old T).kept.getD a {}) i
      | none => 0).sum +
    (∑ r ∈ Finset.range 2, ∑ i ∈ Finset.range
        ((sizesAt S old T).codes.mask.getD (sizesAt S old T).maskCode default).ell,
      readE ((old.d.getD r #[]).getD i zeroE) * (leftAt S old w).mask r i) = readE old.target ↔ _
  rw [eMain, eMask, eKept, eSum]
  constructor <;> intro h <;> rw [← h] <;> ring

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.stageAt
#print axioms ProofFile.Honest.K10.LeftIs.freshAt
#print axioms ProofFile.Honest.K10.LeftIs.pointAt
#print axioms ProofFile.Honest.K10.LeftIs.foldedAt
#print axioms ProofFile.Honest.K10.LeftIs.LeftFits
#print axioms ProofFile.Honest.K10.LeftIs.LeftFits.facts
#print axioms ProofFile.Honest.K10.LeftIs.stage_rows
#print axioms ProofFile.Honest.K10.LeftIs.toList_get
#print axioms ProofFile.Honest.K10.LeftIs.pairs
#print axioms ProofFile.Honest.K10.LeftIs.pairs_length
#print axioms ProofFile.Honest.K10.LeftIs.pairs_get
#print axioms ProofFile.Honest.K10.LeftIs.shapeAt
#print axioms ProofFile.Honest.K10.LeftIs.shapeAt_seat
#print axioms ProofFile.Honest.K10.LeftIs.there_shape
#print axioms ProofFile.Honest.K10.LeftIs.there_bits
#print axioms ProofFile.Honest.K10.LeftIs.there_real
#print axioms ProofFile.Honest.K10.LeftIs.zeroG_is
#print axioms ProofFile.Honest.K10.LeftIs.rowsAt
#print axioms ProofFile.Honest.K10.LeftIs.mainForm
#print axioms ProofFile.Honest.K10.LeftIs.maskForm
#print axioms ProofFile.Honest.K10.LeftIs.muAt
#print axioms ProofFile.Honest.K10.LeftIs.mainForm_is
#print axioms ProofFile.Honest.K10.LeftIs.maskForm_is
#print axioms ProofFile.Honest.K10.LeftIs.mu_is
#print axioms ProofFile.Honest.K10.LeftIs.left_main
#print axioms ProofFile.Honest.K10.LeftIs.left_mask0
#print axioms ProofFile.Honest.K10.LeftIs.left_mask1
#print axioms ProofFile.Honest.K10.LeftIs.range_map_getD
#print axioms ProofFile.Honest.K10.LeftIs.filter_seats
#print axioms ProofFile.Honest.K10.LeftIs.keptNos
#print axioms ProofFile.Honest.K10.LeftIs.keptNos_eq
#print axioms ProofFile.Honest.K10.LeftIs.kept_seat
#print axioms ProofFile.Honest.K10.LeftIs.left_kept
#print axioms ProofFile.Honest.K10.LeftIs.left_is
#print axioms ProofFile.Honest.K10.LeftIs.kept_form
#print axioms ProofFile.Honest.K10.LeftIs.claimTrue_iff_tables
