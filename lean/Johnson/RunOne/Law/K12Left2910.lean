-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left2910.lean: The key file's
tables, rows 2.9 | 2.10 (the proximity tests on G_u and on G_omega): CLAUSE (7) («the word») OF
`MemberLeft` (Johnson/Desc/K12/Coin/MemberAtYes.lean) | THE LAST CLAUSE OF `CoreLeft`, A MEMBER AT A TIME:
«a member's word off the frame's strings, at the tree number that the numbering gives its place in the
book, is the committed word at the member's seat». Statements and proofs: calls.
OVER THREE OTHER FILES' TOOLS: `seven_of_parts` (SevenOfParts.lean: the clause from the entry ·
SeatFits at the one member · ShownAt · SeatIs · the depth) ·
`seatIs_of_made` (Johnson/Desc/K12/Coin/FramesTie.lean: SeatIs from what gpOf has made, the member's place
in the book, and ShapeIs at the tree there) · `book_of_fixes` (Coin/FirstBook.lean). KIN:
`nuOf_is_place` (NuOfPlace.lean) is `nu_29` at lo := 0; `word_15` (Word15.lean) is the like at row 1.15.
WHAT PARTS THE TWO ROWS. 2.9 (the first arm; numbering by labels, nuOf π (nlAt π lo) t): the book must be
in order (BookOrd 0) and the place's first tree 0: then the numbering is z ↦ lo + z. 2.10 (the second arm;
noAt t₁ t₂ 1 = z ↦ t₁ + z): no label is read: nothing is asked of the book's order; but the plain data's
book is NOT the state's: it is the book behind the receiving of the fold's own mask: a receiving keeps
every place and every tree's shape (`recvP_keeps`, Johnson/Desc/K12/Law/OutK.lean).
  `nu_29` · `seatIs_29` | `seatIs_210` · `word_29` | `word_210`.
  BESIDE THEM: row 2.10 AT THE NUMBERING BY LABELS nuOf π (nlAt π lo) t (which the seam's core
  member by member asks, `core_behind_QWm`): `keeps_210` · `nu_210` · `seatIs_210L` · `word_210L`: there
  the book's order and firstTree = 0 come back (a receiving keeps each tree's number).
What it is not. NO EXAMPLE. PREMISES, NONE PAID HERE: the mask · the book's order (both out of the border's
promise by guard_29, KeyBookAtSeats.lean) · firstTree = 0 · off₂ q = lo + q · the book's place of the
message (out of the promise: Free₂.placed) · hshape (the book's tree there stands and has the shape that
the IOP as written in Lean tells): NOBODY's at the shared chain · SeatFits at the member · ShownAt · the
frame's depth · the entry. ONE CLAUSE OF SEVEN. It pays no field of the tables. No soundness is claimed.
Nothing on hiding.

-/
import Johnson.RunOne.Law.SevenOfParts
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.K12.Coin.GameBook
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Law.OutK
import Johnson.RunOne.KeyFillBaseAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Left2910
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf BookOrd)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open H2K.First (made_of entered)
open H2K.Pin (strOf layOf)
open LPFD.CandLaid (sixS)

/-- **The numbering by labels is z ↦ lo + z**, where the mask has come, the place's first tree is 0 and
the book is in order. -/
theorem nu_29 (π : P12) (lo : ℕ) (t : T12) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D)
    (hmk : t.mask.isSome = true) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book) (z : ℕ)
    (hz : z < t.book.trees.size) : nuOf π (nlAt π lo) t z = lo + z := by
  rw [nuOf_of_fixes hf, book_of_fixes π t hmk a rest G0 Ly D hf]
  unfold nlAt H2K.First.numAt
  have hT : t.book.trees[z]? = some t.book.trees[z] := Array.getElem?_eq_getElem hz
  rw [hft, hT, Option.map_some, Option.getD_some, hB z _ hT]
  omega

/-- **SeatIs at a member, row 2.9's numbering.** -/
theorem seatIs_29 (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = lo + q) (t : T12)
    (hmk : t.mask.isSome = true) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout}
    {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (k : ℕ)
    (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix k = (off₂ q.1, q.2)) (o : VerifiableInference.Desc.Oracle)
    (hshape : ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o) :
    SeatIs (nuOf π (nlAt π lo) t) D.book (D.mems.get j) (atSix k).1 (atSix k).2 o := by
  have hbk := book_of_fixes π t hmk a rest G0 Ly D hf
  obtain ⟨T0, hT0, hS0⟩ := hshape
  refine seatIs_of_made (made_of π _ a Ly D (hf.2.2.2 default)) _ j _ _ o (fun z u e => ?_)
    (fun z u T e eT => ?_)
  · rw [hbk, hq] at e
    obtain rfl := Option.some.inj e
    have hz : z < t.book.trees.size := (Array.getElem?_eq_some_iff.1 hT0).1
    exact ⟨by rw [nu_29 π lo t hf hmk hft hB z hz, ← hoff, hat], by rw [hat]⟩
  · rw [hbk, hq] at e
    obtain rfl := Option.some.inj e
    rw [hbk, hT0] at eT
    obtain rfl := Option.some.inj eT
    exact hS0

/-- **SeatIs at a member, row 2.10's numbering.** -/
theorem seatIs_210 (π : P12) (t₁ t₂ : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = t₁ + q) (t : T12)
    (hm0 : t.mask = none) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group}
    {Ly : GroupLayout} {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D)
    (j : Fin D.mems.length) (k : ℕ) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (hat : atSix k = (off₂ q.1, q.2))
    (o : VerifiableInference.Desc.Oracle)
    (hshape : ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o) :
    SeatIs (noAt t₁ t₂ 1) D.book (D.mems.get j) (atSix k).1 (atSix k).2 o := by
  have hM := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨T0, hT0, hS0⟩ := hshape
  obtain ⟨cu, _, he⟩ := hM.ent
  unfold entered at he
  dsimp only at he
  rw [hm0] at he
  obtain ⟨x, hx, he2⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨id, _, e3⟩ := Option.map_eq_some_iff.1 he2
  have hK := (H2K.Out.recvP_keeps (ids := x.1) (d1 := x.2) hx).2.2
  have eb : x.2.book = D.book := congrArg (fun w : ℕ × Statement × TreeBook => w.2.2) e3
  rw [eb] at hK
  have hq' : D.book.place[(D.mems.get j).id]? = some q := hK.place _ _ hq
  obtain ⟨T', hT', f1, _⟩ := hK.tree q.1 T0 hT0
  refine seatIs_of_made hM _ j _ _ o (fun z u e => ?_) (fun z u T e eT => ?_)
  · rw [hq'] at e
    obtain rfl := Option.some.inj e
    exact ⟨by show t₁ + z = _; rw [← hoff, hat], by rw [hat]⟩
  · rw [hq'] at e
    obtain rfl := Option.some.inj e
    rw [hT'] at eT
    obtain rfl := Option.some.inj eT
    rw [f1]
    exact hS0

/-- Where the first fold sends its own mask, the plain data's book is the state's behind one receiving:
every place stands, and every tree's shape and number. -/
theorem keeps_210 (π : P12) (t : T12) (hm0 : t.mask = none) {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain}
    (hf : Fixes π t a rest G0 Ly D) : BookKeeps t.book D.book := by
  obtain ⟨cu, _, he⟩ := (made_of π _ a Ly D (hf.2.2.2 default)).ent
  unfold entered at he
  dsimp only at he
  rw [hm0] at he
  obtain ⟨x, hx, he2⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨id, _, e3⟩ := Option.map_eq_some_iff.1 he2
  have hK := (H2K.Out.recvP_keeps (ids := x.1) (d1 := x.2) hx).2.2
  have eb : x.2.book = D.book := congrArg (fun w : ℕ × Statement × TreeBook => w.2.2) e3
  rw [eb] at hK
  exact hK

/-- **The numbering by labels is z ↦ lo + z at the state's own trees, in the second arm too.** -/
theorem nu_210 (π : P12) (lo : ℕ) (t : T12) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    {G0 : OnBytes.Group} {Ly : GroupLayout} {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D)
    (hm0 : t.mask = none) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book) (z : ℕ)
    (hz : z < t.book.trees.size) : nuOf π (nlAt π lo) t z = lo + z := by
  have hT : t.book.trees[z]? = some t.book.trees[z] := Array.getElem?_eq_getElem hz
  obtain ⟨T', hT', _, f2, _⟩ := (keeps_210 π t hm0 hf).tree z _ hT
  rw [nuOf_of_fixes hf]
  unfold nlAt H2K.First.numAt
  rw [hft, hT', Option.map_some, Option.getD_some, f2, hB z _ hT]
  omega

/-- **SeatIs at a member, row 2.10, at the numbering by labels.** -/
theorem seatIs_210L (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = lo + q) (t : T12)
    (hm0 : t.mask = none) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout}
    {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length) (k : ℕ)
    (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix k = (off₂ q.1, q.2)) (o : VerifiableInference.Desc.Oracle)
    (hshape : ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o) :
    SeatIs (nuOf π (nlAt π lo) t) D.book (D.mems.get j) (atSix k).1 (atSix k).2 o := by
  have hK := keeps_210 π t hm0 hf
  obtain ⟨T0, hT0, hS0⟩ := hshape
  have hq' : D.book.place[(D.mems.get j).id]? = some q := hK.place _ _ hq
  obtain ⟨T', hT', f1, _⟩ := hK.tree q.1 T0 hT0
  refine seatIs_of_made (made_of π _ a Ly D (hf.2.2.2 default)) _ j _ _ o (fun z u e => ?_)
    (fun z u T e eT => ?_)
  · rw [hq'] at e
    obtain rfl := Option.some.inj e
    have hz : z < t.book.trees.size := (Array.getElem?_eq_some_iff.1 hT0).1
    exact ⟨by rw [nu_210 π lo t hf hm0 hft hB z hz, ← hoff, hat], by rw [hat]⟩
  · rw [hq'] at e
    obtain rfl := Option.some.inj e
    rw [hT'] at eT
    obtain rfl := Option.some.inj eT
    rw [f1]
    exact hS0

section
variable {XI : Type} (F : FileDescription XI) (Fr₂ : Frame)

/-- **Clause (7) at a member, row 2.9.** -/
theorem word_29 (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = lo + q) (t : T12)
    (hmk : t.mask.isSome = true) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout}
    {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length)
    (i : Fin six.length) (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix i.val = (off₂ q.1, q.2)) (y : Fr₂.E.Str) (e0 : ℕ)
    (hx : six.get i = ((D.mems.get j).sh, e0))
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).1
        (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₂ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  SevenOfParts.seven_of_parts csKey F Fr₂ _ D.book y (D.mems.get j) ⟨sixS, i⟩ e0 hx hF hS
    (fun o ho => seatIs_29 π lo off₂ hoff t hmk hft hB hf j i.val q hq hat o (htold o ho)) hd

/-- **Clause (7) at a member, row 2.10.** -/
theorem word_210 (π : P12) (t₁ t₂ : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = t₁ + q) (t : T12)
    (hm0 : t.mask = none) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group}
    {Ly : GroupLayout} {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D)
    (j : Fin D.mems.length) (i : Fin six.length) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (hat : atSix i.val = (off₂ q.1, q.2))
    (y : Fr₂.E.Str) (e0 : ℕ) (hx : six.get i = ((D.mems.get j).sh, e0))
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₂ (noAt t₁ t₂ 1) D.book y (D.mems.get j).t).1
        (W0 Fr₂ (noAt t₁ t₂ 1) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₂ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  SevenOfParts.seven_of_parts csKey F Fr₂ _ D.book y (D.mems.get j) ⟨sixS, i⟩ e0 hx hF hS
    (fun o ho => seatIs_210 π t₁ t₂ off₂ hoff t hm0 hf j i.val q hq hat o (htold o ho)) hd

/-- **Clause (7) at a member, row 2.10, at the numbering by labels.** -/
theorem word_210L (π : P12) (lo : ℕ) (off₂ : ℕ → ℕ) (hoff : ∀ q, off₂ q = lo + q) (t : T12)
    (hm0 : t.mask = none) (hft : π.nums.firstTree = 0) (hB : BookOrd 0 t.book)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : OnBytes.Group} {Ly : GroupLayout}
    {D : H2K.First.Plain} (hf : Fixes π t a rest G0 Ly D) (j : Fin D.mems.length)
    (i : Fin six.length) (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix i.val = (off₂ q.1, q.2)) (y : Fr₂.E.Str) (e0 : ℕ)
    (hx : six.get i = ((D.mems.get j).sh, e0))
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).1
        (W0 Fr₂ (nuOf π (nlAt π lo) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₂ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  SevenOfParts.seven_of_parts csKey F Fr₂ _ D.book y (D.mems.get j) ⟨sixS, i⟩ e0 hx hF hS
    (fun o ho => seatIs_210L π lo off₂ hoff t hm0 hft hB hf j i.val q hq hat o (htold o ho)) hd

end

end Johnson.RunOne.Law.K12Left2910

#print axioms Johnson.RunOne.Law.K12Left2910.nu_29
#print axioms Johnson.RunOne.Law.K12Left2910.seatIs_29
#print axioms Johnson.RunOne.Law.K12Left2910.seatIs_210
#print axioms Johnson.RunOne.Law.K12Left2910.word_29
#print axioms Johnson.RunOne.Law.K12Left2910.word_210
#print axioms Johnson.RunOne.Law.K12Left2910.keeps_210
#print axioms Johnson.RunOne.Law.K12Left2910.nu_210
#print axioms Johnson.RunOne.Law.K12Left2910.seatIs_210L
#print axioms Johnson.RunOne.Law.K12Left2910.word_210L
