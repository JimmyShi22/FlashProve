-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Left32.lean: The key file's
tables, row 3.2 (the proximity test on the last chain's own group): THE LAST CLAUSE OF `CoreLeft`
(Johnson/Desc/K12/Coin/CoreBehindQ.lean) AT THE NUMBERING BY LABELS no := nuOf π (nlKW t₁) t: «a member's
word off the frame's strings, at the tree number that no gives its place in the book, is the committed
word at the member's seat». Statements and proofs; calls and two small case splits.
WHY. `law_32_coreF` (K12Law32Core.lean) asks nothing of the book: the seam's core is called at the labels'
own numbering. What that saves is owed in this clause, and in ONE field of its payer's premise:
`SeatIs no book m j t o` (Johnson/Desc/K12/Coin/FramesTie.lean) has six fields, of which «tree :
no m.t = j» alone reads the numbering.
  `nu_W`: where the book is in the last chain's order (`BookOrdW t₁ 1`, Johnson/Desc/K12/Law/FirstBookW.lean:
    the tree at the place z bears the number z, but Omega's at t₁, which bears 1), nlKW t₁ of the number
    at a place z ≤ t₁ is the tables' own off₃ z: but at the place 1.
  `nu_W_not`: A NEGATIVE RESULT, KEPT: at the place 1 (where 1 < t₁) the numbering by labels is WRONG: the
    first chain's tree 1 and Omega's both bear the number 1. Harmless: no member's seat is tree 1
    (`seats_024`).
  `seat_tree_32`: SeatIs' fields tree · part · inBook at a member of the plain data whose message the
    book places where atSix k says, k ∈ [0, 2, 4].
  `word_32`: the clause at that member: by `wordsOf_is_strOf`
    (Johnson/Desc/Sound/FramesMeet.lean: general in no and the book). `word_32_mem`: the
    same in the clause's own letters, at the member ⟨sixS, i⟩.
BESIDE THEM. KIN, CALLED HERE: `seven_of_parts`
(SevenOfParts.lean): `word_32`'s tail, and better: SeatFits at the one member ·
`seatIs_of_made` | `ShapeIs` (FramesTie.lean): `seat_tree_32`'s part | inBook and htold's three in one
structure. `seatIs_32` · `word_32S`: over them; htold in the form «the tree stands and ShapeIs»,
in which `shapeIs_32` (BookAt32.lean) hands it. What stays this file's own: `nu_W` ·
`nu_W_not` · the tie of the labels' numbering to off₃.
What it is not. NO EXAMPLE. PREMISES, NONE PAID HERE: BookOrdW t₁ 1 t.book and the count of its trees:
guard_32_public (KeyOmegaPublic.lean), itself under four steps of the shared chain
that are not typed · the book's place of the message (out of the border's promise: Free₃.placed | .omega)
· htold (SeatIs' main · mask · log: the book's tree has the shape that the IOP as written in Lean tells of
it): NOBODY's at the key file · SeatFits · ShownAt · the frame's depth. It pays ONE clause of CoreLeft, a
member at a time. It pays no field of the tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12Law32Core
import Johnson.Desc.K12.Law.FirstBookW
import Johnson.Desc.K12.Coin.LabelsAtKeyW
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.Sound.FramesMeet
import Johnson.RunOne.Law.SevenOfParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Left32
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open H2K.First (BookOrdW made_of)
open H2K.Pin (strOf layOf)
open Johnson.RunOne.Law.K12Law32Core (seats_024)
open LPFD.CandLaid (sixS)

/-- The number that the book's tree at a place bears, in the last chain's order. -/
theorem numAt_W (t₁ : ℕ) (B : TreeBook) (hB : BookOrdW t₁ 1 B) (z : ℕ) (hz : z < B.trees.size) :
    H2K.First.numAt B z = if z = t₁ then 1 else z := by
  obtain ⟨T, hT⟩ : ∃ T, B.trees[z]? = some T := ⟨B.trees[z], Array.getElem?_eq_getElem hz⟩
  unfold H2K.First.numAt
  rw [hT]
  exact hB z T hT

/-- **The labels' numbering is the tables' own off₃**, at every place up to Omega's but the place 1. -/
theorem nu_W (t₁ : ℕ) (B : TreeBook) (off₃ : ℕ → ℕ) (hB : BookOrdW t₁ 1 B)
    (hlow : ∀ q, q < t₁ → off₃ q = q) (hω : off₃ t₁ = t₁ + 1) (z : ℕ) (hz : z < B.trees.size)
    (hle : z ≤ t₁) (h1 : z = 1 → z = t₁) : nlKW t₁ (H2K.First.numAt B z) = off₃ z := by
  rw [numAt_W t₁ B hB z hz]
  by_cases e : z = t₁
  · rw [if_pos e, e, hω]
    simp [nlKW]
  · rw [if_neg e, hlow z (by omega)]
    have : z ≠ 1 := fun h => e (h1 h)
    simp [nlKW, this]

/-- **At the place 1 it is wrong.** -/
theorem nu_W_not (t₁ : ℕ) (B : TreeBook) (hB : BookOrdW t₁ 1 B) (h : 1 < B.trees.size)
    (ht : 1 < t₁) : nlKW t₁ (H2K.First.numAt B 1) ≠ 1 := by
  rw [numAt_W t₁ B hB 1 h, if_neg (by omega)]
  simp [nlKW]
  omega

/-- **SeatIs' tree · part · inBook at a member.** -/
theorem seat_tree_32 (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ) (hA : AtOk atSix off₂ off₃ t₁)
    (hω : off₃ t₁ = t₁ + 1) (t : T12) (hmask : t.mask.isSome = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain)
    (hf : Fixes π t a rest G0 Ly D) (hB : BookOrdW t₁ 1 t.book)
    (hsz : t.book.trees.size = t₁ + 1) (j : Fin D.mems.length) (k : ℕ) (hk : k ∈ [0, 2, 4])
    (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix k = (off₃ q.1, q.2)) :
    nuOf π (nlKW t₁) t (D.mems.get j).t = (atSix k).1 ∧ (D.mems.get j).part = (atSix k).2 ∧
      (D.book.trees[(D.mems.get j).t]?).map (·.shape) = some (D.mems.get j).tsh := by
  have hbk := book_of_fixes π t hmask a rest G0 Ly D hf
  have hP := ((made_of π _ a Ly D (hf.2.2.2 default)).mem j).2
  have hpl := hP.place
  rw [hbk, hq] at hpl
  obtain ⟨T, hT, hTs, _⟩ := hP.tree
  have e1 : q.1 = (D.mems.get j).t := congrArg Prod.fst (Option.some.inj hpl)
  have e2 : q.2 = (D.mems.get j).part := congrArg Prod.snd (Option.some.inj hpl)
  have hlt : q.1 < t.book.trees.size := by
    rw [e1, ← hbk]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  have h1 : q.1 = 1 → q.1 = t₁ := by
    intro h
    by_contra hne
    have h2 : off₃ q.1 = q.1 := hA.low q.1 (by omega)
    have h3 : (atSix k).1 = 1 := by rw [hat]; exact h2.trans h
    obtain ⟨s0, s2, s4⟩ := seats_024
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [nuOf_of_fixes hf, hbk, ← e1, nu_W t₁ t.book off₃ hB hA.low hω q.1 hlt (by omega) h1, hat]
  · rw [hat, ← e2]
  · rw [hT, ← hTs]
    rfl

/-- **The last clause of `CoreLeft` at a member.** -/
theorem word_32 {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ)
    (hA : AtOk atSix off₂ off₃ t₁) (hω : off₃ t₁ = t₁ + 1) (t : T12)
    (hmask : t.mask.isSome = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain) (hf : Fixes π t a rest G0 Ly D)
    (hB : BookOrdW t₁ 1 t.book) (hsz : t.book.trees.size = t₁ + 1) (j : Fin D.mems.length)
    (i : Fin six.length) (hk : i.val ∈ [0, 2, 4]) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (hat : atSix i.val = (off₃ q.1, q.2))
    (y : Fr₃.E.Str) (hF : Sound.SeatFits F csKey six (seatAt six numSix atSix))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      (D.mems.get j).tsh.mainSymbols.toList = o.tenants.map (·.main) ∧
      (D.mems.get j).tsh.maskSymbols.toList = o.tenants.map (·.mask) ∧
      (D.mems.get j).tsh.logN = o.logLength)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₃.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength)
    (e0 : ℕ) (he : six.get i = ((D.mems.get j).sh, e0)) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).1
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey six (seatAt six numSix atSix) (strsOf Fr₃ y) i) := by
  obtain ⟨s1, s2, s3⟩ := seat_tree_32 π t₁ off₂ off₃ hA hω t hmask a rest G0 Ly D hf hB hsz j i.val hk
    q hq hat
  rw [Sound.wordsOf_is_strOf csKey F six (seatAt six numSix atSix) Fr₃ (nuOf π (nlKW t₁) t) D.book y
    i (D.mems.get j) hF hS
    (fun o ho => ⟨s1, s3, s2, (htold o ho).1, (htold o ho).2.1, (htold o ho).2.2⟩) hd]
  have key : ∀ p : OracleShape × ℕ, p = ((D.mems.get j).sh, e0) →
      HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).2)
        (strOf csKey p.1 p.2 (layOf (D.mems.get j))
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).1
          (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).2) := by
    rintro _ rfl
    exact HEq.rfl
  exact key _ he

/-- **The same in the letters of `CoreLeft`'s last clause**, at the member ⟨sixS, i⟩ of Sound.Mem:
sixS is ⟨six, seatAt six numSix atSix⟩ by its text. -/
theorem word_32_mem {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ)
    (hA : AtOk atSix off₂ off₃ t₁) (hω : off₃ t₁ = t₁ + 1) (t : T12)
    (hmask : t.mask.isSome = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain) (hf : Fixes π t a rest G0 Ly D)
    (hB : BookOrdW t₁ 1 t.book) (hsz : t.book.trees.size = t₁ + 1) (j : Fin D.mems.length)
    (i : Fin six.length) (hk : i.val ∈ [0, 2, 4]) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (hat : atSix i.val = (off₃ q.1, q.2))
    (y : Fr₃.E.Str) (hF : Sound.SeatFits F csKey six (seatAt six numSix atSix))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      (D.mems.get j).tsh.mainSymbols.toList = o.tenants.map (·.main) ∧
      (D.mems.get j).tsh.maskSymbols.toList = o.tenants.map (·.mask) ∧
      (D.mems.get j).tsh.logN = o.logLength)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₃.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength)
    (e0 : ℕ) (he : six.get i = ((D.mems.get j).sh, e0)) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).1
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₃ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  word_32 F Fr₃ π t₁ off₂ off₃ hA hω t hmask a rest G0 Ly D hf hB hsz j i hk q hq hat y hF hS htold hd
    e0 he

/-! ## The same over two other files' tools, in the form in which the tree's shape is handed -/

/-- **SeatIs at a member, whole**: by `seatIs_of_made`; the tree's shape in its own
structure `ShapeIs`, with the tree's standing. -/
theorem seatIs_32 (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ) (hA : AtOk atSix off₂ off₃ t₁)
    (hω : off₃ t₁ = t₁ + 1) (t : T12) (hmask : t.mask.isSome = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain)
    (hf : Fixes π t a rest G0 Ly D) (hB : BookOrdW t₁ 1 t.book)
    (hsz : t.book.trees.size = t₁ + 1) (j : Fin D.mems.length) (k : ℕ) (hk : k ∈ [0, 2, 4])
    (q : ℕ × ℕ) (hq : t.book.place[(D.mems.get j).id]? = some q)
    (hat : atSix k = (off₃ q.1, q.2)) (o : VerifiableInference.Desc.Oracle)
    (hshape : ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o) :
    SeatIs (nuOf π (nlKW t₁) t) D.book (D.mems.get j) (atSix k).1 (atSix k).2 o := by
  obtain ⟨s1, s2, _⟩ := seat_tree_32 π t₁ off₂ off₃ hA hω t hmask a rest G0 Ly D hf hB hsz j k hk q hq
    hat
  have hbk := book_of_fixes π t hmask a rest G0 Ly D hf
  have hM := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨T0, hT0, hS0⟩ := hshape
  have hpl := (hM.mem j).2.place
  refine seatIs_of_made hM _ j _ _ o (fun z u e => ?_) (fun z u T e eT => ?_)
  · rw [hpl] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨s1, s2⟩
  · rw [hbk, hq] at e
    obtain rfl := Option.some.inj e
    rw [hbk, hT0] at eT
    obtain rfl := Option.some.inj eT
    exact hS0

/-- **The last clause of `CoreLeft` | clause (7) of `MemberLeft` at a member**: by
`seven_of_parts` (SevenOfParts.lean): SeatFits is asked at the one member alone. -/
theorem word_32S {XI : Type} (F : FileDescription XI) (Fr₃ : Frame) (π : P12) (t₁ : ℕ) (off₂ off₃ : ℕ → ℕ)
    (hA : AtOk atSix off₂ off₃ t₁) (hω : off₃ t₁ = t₁ + 1) (t : T12)
    (hmask : t.mask.isSome = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : OnBytes.Group) (Ly : GroupLayout) (D : H2K.First.Plain) (hf : Fixes π t a rest G0 Ly D)
    (hB : BookOrdW t₁ 1 t.book) (hsz : t.book.trees.size = t₁ + 1) (j : Fin D.mems.length)
    (i : Fin six.length) (hk : i.val ∈ [0, 2, 4]) (q : ℕ × ℕ)
    (hq : t.book.place[(D.mems.get j).id]? = some q) (hat : atSix i.val = (off₃ q.1, q.2))
    (y : Fr₃.E.Str) (e0 : ℕ) (hx : six.get i = ((D.mems.get j).sh, e0))
    (hF : Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hS : Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₃ y) i)
    (htold : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∃ T, t.book.trees[q.1]? = some T ∧ ShapeIs T.shape o)
    (hd : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      ∀ e ∈ Fr₃.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ o.logLength) :
    HEq (strOf csKey (D.mems.get j).sh e0 (layOf (D.mems.get j))
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).1
        (W0 Fr₃ (nuOf π (nlKW t₁) t) D.book y (D.mems.get j).t).2)
      (Sound.wordsOf F csKey (⟨sixS, i⟩ : Sound.Mem).1.l (⟨sixS, i⟩ : Sound.Mem).1.seat
        (strsOf Fr₃ y) (⟨sixS, i⟩ : Sound.Mem).2) :=
  SevenOfParts.seven_of_parts csKey F Fr₃ _ D.book y (D.mems.get j) ⟨sixS, i⟩ e0 hx hF hS
    (fun o ho => seatIs_32 π t₁ off₂ off₃ hA hω t hmask a rest G0 Ly D hf hB hsz j i.val hk q hq hat
      o (htold o ho)) hd

end Johnson.RunOne.Law.K12Left32

#print axioms Johnson.RunOne.Law.K12Left32.nu_W
#print axioms Johnson.RunOne.Law.K12Left32.nu_W_not
#print axioms Johnson.RunOne.Law.K12Left32.seat_tree_32
#print axioms Johnson.RunOne.Law.K12Left32.word_32
#print axioms Johnson.RunOne.Law.K12Left32.word_32_mem
#print axioms Johnson.RunOne.Law.K12Left32.seatIs_32
#print axioms Johnson.RunOne.Law.K12Left32.word_32S
