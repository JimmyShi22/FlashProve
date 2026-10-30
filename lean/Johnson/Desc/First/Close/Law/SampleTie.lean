-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/SampleTie.lean: A MEMBER's SAMPLE ROW: THE TYPED FORM, CARRIED TO THE
FOLD's INPUT CODE, AND THE PROGRAM's ROW, LAID ALONE AS A VECTOR: WHAT EACH IS AT AN INDEX; AND THE
TIE OFF THE FREE ROWS FROM WHAT IS LEFT BETWEEN THEM. Theorems.

Why. The law of the closing (K10) on vectors asks, for each typed row of the group, that its form,
arranged (`R.Sh.rho.fm`), plus further weights on free rows alone, is the program's row laid alone
(`rowVec`, Johnson/Desc/First/Close/Law/BatTie.lean). For a member's sample row that is one true
tie. It has three thirds: what the typed side is at an index; what the program's side is at an
index; and the middle: that the row's coefficient on an entry of the message's table is the sample's
matrix at that entry. This file has the two outer thirds, and the tie from the middle as a premise.

What is said.
  The program's side. `NamesOne w o`: the row has no coefficient on another message than o.
    `rowVec_main`, `rowVec_mask`: **at the vertex b and the place x the vector of such a row is o's
    weight at the index (the vertex's number + 2^k · x) times the row's coefficient on the entry of
    o's own table that belongs to the index.** `rowVec_kept`, `rowVec_kept_other`,
    `rowVec_offCorner`: at a kept slot.
  The typed side. `fm_main`, `fm_mask`: **where the vertex b holds the row r, the carried form at
    (b, x) is the form on the rows as sent, at (r, x).** `fm_kept`: at a kept slot, at the corner 0
    .. 0: at the slot's row, if every kept row names its slot. `fm_corner`: at another corner: 0.
    `flat_fm`, `flat_fm_main`, `flat_fm_mask`: the form on the rows as sent is, member by member,
    the member's view's form of the form's share on that member. `atMem_self`, `atMem_other`: the
    shares of a form on one member. `fm_zero`: a change of shape that meets the laws carries 0 to 0.
  The tie. `SampleFits`: what is left: on the member's own rows, THE MIDDLE under o's weight (main,
    kept, mask); on another member's rows, o has no weight or the row no coefficient (mainElse,
    keptElse, maskElse): that is «the layout's block of o is where the arrangement puts a's rows»;
    the form stands on a alone; the views meet the laws; every kept row names its slot.
    `sample_tie`: **then, off the free rows, the carried form is the program's row, laid alone.**
    `BlockAt` (the layout against the arrangement: once for a member of a group), `Middle` (once for
    a sample row), `sampleFits_of`: the two debts apart give `SampleFits`.

Limits. `SampleFits` IS SHOWN OF NOTHING: its main, kept and mask are the middle third and the
premise on the layout in one; at a member's own rows `sample_tie` adds the re-indexing alone. What a
view's form is at a real member (the cases of Johnson/Top/H/MemberOnto.lean) is not opened here. No
member, no tooth. It rests on Johnson/Top/H/GroupRowsOnto.lean (`rep_of_ord`, `rep_of_kept`,
`rep_of_ordZ`). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BatTie
import Johnson.Top.H.GroupRowsOnto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

/-! ## 1 The program's side at an index -/

/-- The row names the oracle message o alone: it has no coefficient on another message's tables. -/
def NamesOne (w : OnBytes.Row) (o : ℕ) : Prop :=
  ∀ o', o' ≠ o → ∀ part e, readE (w.coefficient o' part e) = 0

section RowVecAt
variable {S : Sig GE} {R : RowsK S} (N : SlotNames R)

/-- A sum over numbers of which one alone counts. -/
theorem sum_one (n o : ℕ) (f : ℕ → GE) (h : ∀ o', o' ≠ o → f o' = 0) (ho : n ≤ o → f o = 0) :
    ∑ o' ∈ Finset.range n, f o' = f o := by
  by_cases hn : o < n
  · exact Finset.sum_eq_single o (fun o' _ hne => h o' hne)
      fun hno => absurd (Finset.mem_range.2 hn) hno
  · rw [ho (Nat.le_of_not_lt hn)]
    exact Finset.sum_eq_zero fun o' ho' =>
      h o' fun e => hn (e ▸ Finset.mem_range.1 ho')

/-- **ON THE CUBE OF MAIN ROWS**: the vector of a row that names o alone, at the vertex b and the
place x: o's weight at the index J = the vertex's number + 2^(h + g) · x, times the row's
coefficient on the entry of o's own main table that belongs to J. -/
theorem rowVec_main (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ)
    (h1 : NamesOne w o) (b : Fin (R.s.h + R.s.g) → Bool) (x : Fin R.s.C.l) :
    rowVec N T L w (.inl (b, (none, x))) =
      mainWeight (K := GE) T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) *
        readE (w.coefficient o .main
          (mainBack T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val))) := by
  show w.mainSum rdE T L oneE (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) = _
  rw [Row.mainSum_eq rdE T L L.top oneE w _ fun o' ho' => mainWeight_top T L o' _ ho', rdE.one,
    mul_one, rowMain]
  exact sum_one L.top o _ (fun o' hne => by
      show _ * readE _ = 0
      rw [h1 o' hne, mul_zero])
    fun ho => by rw [mainWeight_top T L o _ ho, zero_mul]

/-- **ON THE CUBE OF MASK ROWS**: the like. -/
theorem rowVec_mask (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ)
    (h1 : NamesOne w o) (b : Fin R.s.h → Bool) (x : Fin R.s.Z.l) :
    rowVec N T L w (.inr (b, x)) =
      maskWeight (K := GE) T L o (Sz.rowNo b + 2 ^ R.s.h * x.val) *
        readE (w.coefficient o .mask (maskBack T L o (Sz.rowNo b + 2 ^ R.s.h * x.val))) := by
  show w.maskSum rdE T L oneE (Sz.rowNo b + 2 ^ R.s.h * x.val) = _
  rw [Row.maskSum_eq rdE T L L.top oneE w _ fun o' ho' => maskWeight_top T L o' _ ho', rdE.one,
    mul_one, rowMask]
  exact sum_one L.top o _ (fun o' hne => by
      show _ * readE _ = 0
      rw [h1 o' hne, mul_zero])
    fun ho => by rw [maskWeight_top T L o _ ho, zero_mul]

/-- **AT A KEPT SLOT, AT THE CORNER 0 .. 0**: the slot's message's weight as a kept member, times
the row's coefficient on the entry that the slot's name names. -/
theorem rowVec_kept (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (q : R.Kp)
    (x : Fin R.s.C.l) :
    rowVec N T L w (.inl (fun _ => false, (some q, x))) =
      keptWeight (K := GE) L (N.orc q) * readE (w.coefficient (N.orc q) .main (N.idx q x)) :=
  if_pos rfl

/-- At a slot of another message than the one that the row names: 0. -/
theorem rowVec_kept_other (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ)
    (h1 : NamesOne w o) (q : R.Kp) (hq : N.orc q ≠ o) (x : Fin R.s.C.l) :
    rowVec N T L w (.inl (fun _ => false, (some q, x))) = 0 := by
  rw [rowVec_kept, h1 _ hq, mul_zero]

/-- At another corner of a kept slot: 0. -/
theorem rowVec_offCorner (T : Statement) (L : GroupLayout) (w : OnBytes.Row)
    (b : Fin (R.s.h + R.s.g) → Bool) (hb : b ≠ fun _ => false) (q : R.Kp) (x : Fin R.s.C.l) :
    rowVec N T L w (.inl (b, (some q, x))) = 0 :=
  if_neg hb

end RowVecAt

/-! ## 2 The typed side at an index -/

section FmAt
variable {S : Sig GE} (R : RowsK S)

/-- **ON THE CUBE OF MAIN ROWS**: where the vertex b holds the row r, the carried form at (b, x) is
the form on the rows as sent, at (r, x). -/
theorem fm_main (v : R.G.C.J → GE) {b : Fin (R.s.h + R.s.g) → Bool}
    {r : Σ a : R.G.A, Fin (R.nM a)} (h : R.Sh.am.src (b, none) = some r) (x : R.Sh.Cb.J) :
    R.Sh.rho.fm v (.inl (b, (none, x))) = R.Sh.flat.fm v (.inl (r, x)) := by
  show R.Sh.am.place (fun n => R.Sh.flat.fm v (.inl n)) ((b, none), x) = _
  simp only [Arr.place, h]
  split
  · rfl
  · rename_i hne
    exact absurd (R.rep_of_ord h) hne

/-- **AT A KEPT SLOT, AT THE CORNER 0 .. 0**: the form on the rows as sent, at the slot's row. -/
theorem fm_kept (hS : ∀ q, R.slot (R.kept q) = some q) (v : R.G.C.J → GE) (q : R.Kp)
    (x : R.Sh.Cb.J) :
    R.Sh.rho.fm v (.inl (fun _ => false, (some q, x))) = R.Sh.flat.fm v (.inl (R.kept q, x)) := by
  show R.Sh.am.place (fun n => R.Sh.flat.fm v (.inl n)) ((fun _ => false, some q), x) = _
  have hs : R.Sh.am.src (fun _ => false, some q) = some (R.kept q) := rfl
  simp only [Arr.place, hs]
  split
  · rfl
  · rename_i hne
    exact absurd (R.rep_of_kept hS q) hne

/-- At another corner of a kept slot: 0. -/
theorem fm_corner (hS : ∀ q, R.slot (R.kept q) = some q) (v : R.G.C.J → GE)
    {b : Fin (R.s.h + R.s.g) → Bool} (hb : b ≠ fun _ => false) (q : R.Kp) (x : R.Sh.Cb.J) :
    R.Sh.rho.fm v (.inl (b, (some q, x))) = 0 := by
  show R.Sh.am.place (fun n => R.Sh.flat.fm v (.inl n)) ((b, some q), x) = _
  have hs : R.Sh.am.src (b, some q) = some (R.kept q) := rfl
  simp only [Arr.place, hs]
  split
  · rename_i he
    exact absurd (congrArg Prod.fst ((R.rep_of_kept hS q).symm.trans he)).symm hb
  · rfl

/-- **ON THE CUBE OF MASK ROWS**: the like. -/
theorem fm_mask (v : R.G.C.J → GE) {b : Fin R.s.h → Bool} {r : Σ a : R.G.A, Fin (R.nZ a)}
    (h : R.Sh.az.src b = some r) (y : R.Sh.Zb.J) :
    R.Sh.rho.fm v (.inr (b, y)) = R.Sh.flat.fm v (.inr (r, y)) := by
  show R.Sh.az.place (fun n => R.Sh.flat.fm v (.inr n)) (b, y) = _
  simp only [Arr.place, h]
  split
  · rfl
  · rename_i hne
    exact absurd (R.rep_of_ordZ h) hne

/-- **The form on the rows as sent** is, member by member, the member's view's form of the form's
share on that member. -/
theorem flat_fm (v : R.G.C.J → GE) (n : R.Sh.Cflat.J) :
    R.Sh.flat.fm v n =
      (R.view (gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).1).fm
        (fun j => v ⟨(gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).1, j⟩)
        (gatE R.Sh.Rm R.Sh.Rz R.Sh.Cb.J R.Sh.Zb.J n).2 := rfl

/-- At a main row as sent: the member's view's form, at (row, place). -/
theorem flat_fm_main (v : R.G.C.J → GE) (a : R.G.A) (r : Fin (R.nM a)) (x : R.Sh.Cb.J) :
    R.Sh.flat.fm v (.inl (⟨a, r⟩, x)) = (R.view a).fm (fun j => v ⟨a, j⟩) (.inl (r, x)) := rfl

/-- At a mask row as sent. -/
theorem flat_fm_mask (v : R.G.C.J → GE) (a : R.G.A) (r : Fin (R.nZ a)) (y : R.Sh.Zb.J) :
    R.Sh.flat.fm v (.inr (⟨a, r⟩, y)) = (R.view a).fm (fun j => v ⟨a, j⟩) (.inr (r, y)) := rfl

end FmAt

/-! ## 3 A form on one member -/

/-- The share of a form on the member a: on a itself the form. -/
theorem atMem_self {St A : Type} [DecidableEq A] {Jf : A → Type} (a : A) (sl : Slf GE St (Jf a))
    (st : St) : (fun j => Slf.atMem a sl st ⟨a, j⟩) = sl st := by
  funext j
  show (if h : a = a then sl st (h ▸ j) else 0) = _
  rw [dif_pos rfl]

/-- On another member: 0. -/
theorem atMem_other {St A : Type} [DecidableEq A] {Jf : A → Type} (a : A) (sl : Slf GE St (Jf a))
    (st : St) {m : A} (hm : m ≠ a) : (fun j => Slf.atMem a sl st ⟨m, j⟩) = 0 := by
  funext j
  show (if h : m = a then sl st (h ▸ j) else 0) = _
  rw [dif_neg hm]
  rfl

/-! ## 4 The tie off the free rows -/

section Tie
variable {S : Sig GE} {R : RowsK S} (N : SlotNames R)

/-- **What is left between the two sides**, for a form u on the member a and a row w of the program
that names the oracle message o alone. On a's own rows: THE MIDDLE: the view's form of u at (row,
place) is the row's coefficient on the entry of o's table that belongs to the index, under o's
weight there. On another member's rows: o has no weight, or the row no coefficient. -/
structure SampleFits (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ) (a : R.G.A)
    (u : (R.G.C.J → GE)) : Prop where
  /-- u stands on the member a alone -/
  alone : ∀ m, m ≠ a → (fun j => u ⟨m, j⟩) = 0
  /-- the members' views meet the laws of a change of shape -/
  laws : ∀ m, (R.view m).Laws
  /-- every kept row names its slot -/
  slots : ∀ q, R.slot (R.kept q) = some q
  main : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (r : Fin (R.nM a)) (x : Fin R.s.C.l),
    R.Sh.am.src (b, none) = some ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inl (r, x)) =
      mainWeight (K := GE) T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) *
        readE (w.coefficient o .main
          (mainBack T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val)))
  mainElse : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (m : R.G.A) (r : Fin (R.nM m)) (x : Fin R.s.C.l),
    R.Sh.am.src (b, none) = some ⟨m, r⟩ → m ≠ a →
    mainWeight (K := GE) T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) *
      readE (w.coefficient o .main
        (mainBack T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val))) = 0
  kept : ∀ (q : R.Kp) (r : Fin (R.nM a)) (x : Fin R.s.C.l), R.kept q = ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inl (r, x)) =
      keptWeight (K := GE) L (N.orc q) * readE (w.coefficient (N.orc q) .main (N.idx q x))
  keptElse : ∀ (q : R.Kp) (m : R.G.A) (r : Fin (R.nM m)) (x : Fin R.s.C.l), R.kept q = ⟨m, r⟩ →
    m ≠ a →
    keptWeight (K := GE) L (N.orc q) * readE (w.coefficient (N.orc q) .main (N.idx q x)) = 0
  mask : ∀ (b : Fin R.s.h → Bool) (r : Fin (R.nZ a)) (y : Fin R.s.Z.l),
    R.Sh.az.src b = some ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inr (r, y)) =
      maskWeight (K := GE) T L o (Sz.rowNo b + 2 ^ R.s.h * y.val) *
        readE (w.coefficient o .mask (maskBack T L o (Sz.rowNo b + 2 ^ R.s.h * y.val)))
  maskElse : ∀ (b : Fin R.s.h → Bool) (m : R.G.A) (r : Fin (R.nZ m)) (y : Fin R.s.Z.l),
    R.Sh.az.src b = some ⟨m, r⟩ → m ≠ a →
    maskWeight (K := GE) T L o (Sz.rowNo b + 2 ^ R.s.h * y.val) *
      readE (w.coefficient o .mask (maskBack T L o (Sz.rowNo b + 2 ^ R.s.h * y.val))) = 0

/-- A change of shape that meets the laws carries the form 0 to 0. -/
theorem fm_zero {P : Type} {C C' : LdCode GE P} {ρ : Reshape C C'} (h : ρ.Laws) : ρ.fm 0 = 0 := by
  funext j
  have e := h.val 0 (Pi.single j 1, 0)
  simpa [Pi.single_apply] using e

/-- **OFF THE FREE ROWS THE CARRIED FORM IS THE PROGRAM's ROW, LAID ALONE.** -/
theorem sample_tie (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ) (a : R.G.A)
    (u : R.G.C.J → GE) (h1 : NamesOne w o) (H : SampleFits N T L w o a u) (j : R.Sh.Cin.J)
    (hj : ¬ Johnson.Top.H.ArrAdd.FreeAt R.Sh j) : R.Sh.rho.fm u j = rowVec N T L w j := by
  rcases j with ⟨b, k, x⟩ | ⟨b, y⟩
  · have hj' : R.Sh.am.src (b, k) ≠ none := hj
    cases k with
    | none =>
      cases hs : R.Sh.am.src (b, none) with
      | none => exact absurd hs hj'
      | some r =>
        obtain ⟨m, r⟩ := r
        rw [fm_main R u hs x, flat_fm_main, rowVec_main N T L w o h1 b x]
        by_cases hm : m = a
        · subst hm
          exact H.main b r x hs
        · rw [H.alone m hm, fm_zero (H.laws m), H.mainElse b m r x hs hm]
          rfl
    | some q =>
      by_cases hb : b = fun _ => false
      · subst hb
        rw [fm_kept R H.slots u q x, rowVec_kept]
        cases hk : R.kept q with
        | mk m r =>
          show (R.view m).fm (fun j => u ⟨m, j⟩) (.inl (r, x)) = _
          by_cases hm : m = a
          · subst hm
            exact H.kept q r x hk
          · rw [H.alone m hm, fm_zero (H.laws m), H.keptElse q m r x hk hm]
            rfl
      · rw [fm_corner R H.slots u hb q x, rowVec_offCorner N T L w b hb q x]
  · have hj' : R.Sh.az.src b ≠ none := hj
    cases hs : R.Sh.az.src b with
    | none => exact absurd hs hj'
    | some r =>
      obtain ⟨m, r⟩ := r
      rw [fm_mask R u hs y, flat_fm_mask, rowVec_mask N T L w o h1 b y]
      by_cases hm : m = a
      · subst hm
        exact H.mask b r y hs
      · rw [H.alone m hm, fm_zero (H.laws m), H.maskElse b m r y hs hm]
        rfl

/-- **THE LAYOUT AGAINST THE ARRANGEMENT** (once for a member of a group): the layout's block of the
oracle message o is where the arrangement puts the member a's rows: there o's weight is 1; on
another member's rows it is 0; a's kept rows stand in slots that name o, a kept member; another
member's in slots that name another message. -/
structure BlockAt (T : Statement) (L : GroupLayout) (o : ℕ) (a : R.G.A) : Prop where
  main : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (r : Fin (R.nM a)) (x : Fin R.s.C.l),
    R.Sh.am.src (b, none) = some ⟨a, r⟩ →
    mainWeight (K := GE) T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) = 1
  mainElse : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (m : R.G.A) (r : Fin (R.nM m)) (x : Fin R.s.C.l),
    R.Sh.am.src (b, none) = some ⟨m, r⟩ → m ≠ a →
    mainWeight (K := GE) T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) = 0
  kept : ∀ (q : R.Kp) (r : Fin (R.nM a)), R.kept q = ⟨a, r⟩ →
    N.orc q = o ∧ keptWeight (K := GE) L o = 1
  keptElse : ∀ (q : R.Kp) (m : R.G.A) (r : Fin (R.nM m)), R.kept q = ⟨m, r⟩ → m ≠ a → N.orc q ≠ o
  mask : ∀ (b : Fin R.s.h → Bool) (r : Fin (R.nZ a)) (y : Fin R.s.Z.l),
    R.Sh.az.src b = some ⟨a, r⟩ →
    maskWeight (K := GE) T L o (Sz.rowNo b + 2 ^ R.s.h * y.val) = 1
  maskElse : ∀ (b : Fin R.s.h → Bool) (m : R.G.A) (r : Fin (R.nZ m)) (y : Fin R.s.Z.l),
    R.Sh.az.src b = some ⟨m, r⟩ → m ≠ a →
    maskWeight (K := GE) T L o (Sz.rowNo b + 2 ^ R.s.h * y.val) = 0

/-- **THE MIDDLE** (once for a sample row): the view's form of u's share on a, at (row, place), is
the row's coefficient on the entry of o's own table that belongs to the index. -/
structure Middle (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ) (a : R.G.A)
    (u : R.G.C.J → GE) : Prop where
  main : ∀ (b : Fin (R.s.h + R.s.g) → Bool) (r : Fin (R.nM a)) (x : Fin R.s.C.l),
    R.Sh.am.src (b, none) = some ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inl (r, x)) =
      readE (w.coefficient o .main
        (mainBack T L o (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val)))
  kept : ∀ (q : R.Kp) (r : Fin (R.nM a)) (x : Fin R.s.C.l), R.kept q = ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inl (r, x)) = readE (w.coefficient o .main (N.idx q x))
  mask : ∀ (b : Fin R.s.h → Bool) (r : Fin (R.nZ a)) (y : Fin R.s.Z.l),
    R.Sh.az.src b = some ⟨a, r⟩ →
    (R.view a).fm (fun j => u ⟨a, j⟩) (.inr (r, y)) =
      readE (w.coefficient o .mask (maskBack T L o (Sz.rowNo b + 2 ^ R.s.h * y.val)))

/-- The two, apart, give what is left between the two sides. -/
theorem sampleFits_of (T : Statement) (L : GroupLayout) (w : OnBytes.Row) (o : ℕ) (a : R.G.A)
    (u : R.G.C.J → GE) (h1 : NamesOne w o) (alone : ∀ m, m ≠ a → (fun j => u ⟨m, j⟩) = 0)
    (laws : ∀ m, (R.view m).Laws) (slots : ∀ q, R.slot (R.kept q) = some q)
    (B : BlockAt N T L o a) (M : Middle N T L w o a u) : SampleFits N T L w o a u where
  alone := alone
  laws := laws
  slots := slots
  main := fun b r x h => by rw [M.main b r x h, B.main b r x h, one_mul]
  mainElse := fun b m r x h hm => by rw [B.mainElse b m r x h hm, zero_mul]
  kept := fun q r x h => by
    obtain ⟨e1, e2⟩ := B.kept q r h
    rw [M.kept q r x h, e1, e2, one_mul]
  keptElse := fun q m r x h hm => by rw [h1 _ (B.keptElse q m r h hm), mul_zero]
  mask := fun b r y h => by rw [M.mask b r y h, B.mask b r y h, one_mul]
  maskElse := fun b m r y h hm => by rw [B.maskElse b m r y h hm, zero_mul]

end Tie

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.sum_one
#print axioms VerifiableInference.Desc.First.Close.rowVec_main
#print axioms VerifiableInference.Desc.First.Close.rowVec_mask
#print axioms VerifiableInference.Desc.First.Close.rowVec_kept
#print axioms VerifiableInference.Desc.First.Close.rowVec_kept_other
#print axioms VerifiableInference.Desc.First.Close.rowVec_offCorner
#print axioms VerifiableInference.Desc.First.Close.fm_main
#print axioms VerifiableInference.Desc.First.Close.fm_kept
#print axioms VerifiableInference.Desc.First.Close.fm_corner
#print axioms VerifiableInference.Desc.First.Close.fm_mask
#print axioms VerifiableInference.Desc.First.Close.flat_fm
#print axioms VerifiableInference.Desc.First.Close.flat_fm_main
#print axioms VerifiableInference.Desc.First.Close.flat_fm_mask
#print axioms VerifiableInference.Desc.First.Close.atMem_self
#print axioms VerifiableInference.Desc.First.Close.atMem_other
#print axioms VerifiableInference.Desc.First.Close.fm_zero
#print axioms VerifiableInference.Desc.First.Close.sample_tie
#print axioms VerifiableInference.Desc.First.Close.sampleFits_of
