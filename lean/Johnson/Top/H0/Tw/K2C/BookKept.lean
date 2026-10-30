-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/BookKept.lean: the kind «the code switch»: WHAT THE SWITCH DOES TO THE BOOK OF
TREES AND TO THE COUNT OF ROOTS. NO BLOCK IMPORTS THIS FILE.
The switch writes the book twice. (1) Its sending lays the new trees: inside sendP that is the work
of the plain ground's receiving recvP alone; what recvP does to the book is not proved here: it is a
premise of yes_hands. (2) The reading of the old rows counts, at each tree that it opens, at how
many
lists the tree has been opened (openOne: «lists := lists + 1»): so the book's trees do turn there;
but no tree comes or goes, and no tree's number, source, shape or parts turn.
  SameNumbers A B   the two books have trees at the same indices, each with the number, the source,
                    the shape and the parts that it had, and the same places
  openOne_same · readOld_same · switchBehind_same     the three steps of the reading
  yes_book          a yes of the decision, at any of its three sorts of place: with the state d'
                    that sendP returns (yes_sendP): SameNumbers d'.book s'.book, and the count of
                    roots behind the block is the one that sendP returns
  admitP_book · sampleLoop_book · sendP_book
                    behind sendP's receiving nothing writes the book or the count of roots
  yes_hands         a property of (book, roots) that recvP keeps at the chain's first tree's number,
                    and that reads no more of a book than SameNumbers keeps, is handed on by a yes
                    of
                    the switch
  ordered_same      «as many roots as trees; every tree bears its place's number, counted from ft»
                    meets the second of these two premises; the first (recvP keeps it) is another
                    file's: Johnson/Desc/Book/BookNumbers.lean's recvP_numbered says the like
  headFrontQ_book · headOpenQ_book · finishFrontQ_book · finishBehindQ_book
                    the four quiet steps leave the book and the count of roots
Frame facts: they say what the text does not write. No Mathlib. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.SendsOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 openOne readOld)

/-- Trees at the same indices, each with the number, the source, the shape and the parts that it
had; the same places. -/
def SameNumbers (A B : TreeBook) : Prop :=
  B.trees.size = A.trees.size ∧ B.place = A.place ∧
    ∀ (z : Nat) (T : Tree), B.trees[z]? = some T → ∃ T₀,
        A.trees[z]? = some T₀ ∧ T.number = T₀.number ∧ T.src = T₀.src ∧ T.shape = T₀.shape ∧
          T.parts = T₀.parts

theorem SameNumbers.refl (A : TreeBook) : SameNumbers A A := 
  ⟨rfl, rfl, fun _ T h => ⟨T, h, rfl, rfl, rfl, rfl⟩⟩

theorem SameNumbers.trans {A B C : TreeBook} (h : SameNumbers A B) (k : SameNumbers B C) :
    SameNumbers A C := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, fun z T hT => ?_⟩
  obtain ⟨T₁, h₁, e₁, f₁, g₁, i₁⟩ := k.2.2 z T hT
  obtain ⟨T₀, h₀, e₀, f₀, g₀, i₀⟩ := h.2.2 z T₁ h₁
  exact ⟨T₀, h₀, e₁.trans e₀, f₁.trans f₀, g₁.trans g₀, i₁.trans i₀⟩

/-- One more list counted at one tree. -/
theorem counted_same (A : TreeBook) (t : Nat) :
    SameNumbers A { A with trees := A.trees.modify t fun x => { x with lists := x.lists + 1 } } :=
        by
  refine ⟨by simp, rfl, fun z T hT => ?_⟩
  simp only [Array.getElem?_modify] at hT
  split at hT
  · cases hz : A.trees[z]? with
    | none => simp [hz] at hT
    | some T₀ =>
      simp only [hz, Option.map_some, Option.some.injEq] at hT
      exact ⟨T₀, rfl, by rw [← hT], by rw [← hT], by rw [← hT], by rw [← hT]⟩
  · exact ⟨T, hT, rfl, rfl, rfl, rfl⟩

theorem openOne_same {S : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} {t : Nat}
    {s s' : TreeBook × List _root_.Tw.K2.Col × Array (Nat × Array Nat × Array (Array F))}
    (h : openOne S ft pos B0 t s = .ok s') : SameNumbers s.1 s'.1 := by
  obtain ⟨tree, tree0, a⟩ := (_root_.Tw.K2.openOne_iff _ _ _ _ _ _ _).1 h
  rw [a.out]
  exact counted_same _ _

theorem opens_same {S : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} :
    ∀ (l : List Nat) (s s' : TreeBook × List _root_.Tw.K2.Col × Array (Nat × Array Nat × Array
        (Array F))),
      l.foldlM (fun a t => openOne S ft pos B0 t a) s = .ok s' → SameNumbers s.1 s'.1
  | [], s, s', h => by
    cases h
    exact SameNumbers.refl _
  | t :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := bindOk h
    exact (openOne_same h1).trans (opens_same l m s' h2)

theorem readOld_same {i : SwIn} {pos : Positions} {B : TreeBook} {left y}
    (h : readOld i pos = .ok (B, left, y)) : SameNumbers i.book B := by
  obtain ⟨places, cols, opened, k⟩ := readOld_inv h
  exact opens_same _ _ _ k.hOpen

theorem switchBehind_same {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    SameNumbers i.book o.book := by
  obtain ⟨c, y, S1, S2, S3, rows, b⟩ := switchBehind_inv h
  exact readOld_same b.hRead

/-- **A yes of the decision: from what the sending returns to the record behind.** -/
theorem yes_book {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ =
          some (ids, sd, an, took, d') ∧
      SameNumbers d'.book s'.book ∧ s'.roots = d'.roots := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩
        x r₁ r₂ (flat p gs) = .ok (w, roots) →
      ∃ ids sd an took d', Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit)
        ⟨p.samples, p.firstTree⟩ false ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others)
          r₁ r₂ = some (ids, sd, an, took, d') ∧
      SameNumbers d'.book w.book ∧ roots = d'.roots := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, switchBehind_same k.hBehind, k.hRoots⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2

/-! ### The sending itself: behind the receiving nothing writes the book or the count of roots -/

theorem optBindB {α β : Type} {x : Option α} {f : α → Option β} {b : β} (h : (x >>= f) = some b) :
    ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem admitP_book {L : Type} {d d' : Desc.Plain.DState L} {o : Nat} {rows : Array OnBytes.Row}
    (h : Desc.Ground.admitP d o rows = some d') : d'.book = d.book ∧ d'.roots = d.roots := by
  unfold Desc.Ground.admitP at h
  split at h
  · cases hx : d.st.oracles[o]? with
    | none => simp [hx] at h
    | some x =>
      cases hp : Desc.Own.padMade d.st.codes x.shape with
      | none => simp [hx, hp] at h
      | some places =>
        simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl⟩
  · cases h

theorem sampleLoop_book {p : Desc.Plain.GPar} {codes : Codes} {seeds : List SampleSeed} :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : Desc.Plain.DState Unit) (left : List E),
      Desc.Plain.sampleLoop Desc.Plain.groundG p codes seeds l ys d = some (d', left) →
        d'.book = d.book ∧ d'.roots = d.roots
  | [], ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, rfl⟩
  | (o, s) :: l, ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d₁ ha
        obtain ⟨b1, r1⟩ := admitP_book (d := d) (d' := d₁) ha
        obtain ⟨b2, r2⟩ := sampleLoop_book l ys' d₁ d' left h
        exact ⟨b2.trans b1, r2.trans r1⟩

/-- A yes of sendP: the book and the count of roots behind it are those behind its receiving. -/
theorem sendP_book {p : Desc.Plain.GPar} {own : Bool} {d d' : Desc.Plain.DState Unit}
    {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView} {ids sd an need}
    (h : Desc.Plain.sendP Desc.Plain.groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d')) :
    ∃ d₁, Desc.Ground.recvP p.firstTree d sent = some (ids, d₁) ∧ d'.book = d₁.book ∧
      d'.roots = d₁.roots := by
  unfold Desc.Plain.sendP at h
  obtain ⟨⟨ids', d₁⟩, h1, h⟩ := optBindB h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := optBindB h
  obtain ⟨seeds, _, h⟩ := optBindB h
  obtain ⟨an', _, h⟩ := optBindB h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBindB h
    dsimp only at h
    split at h
    · cases h
      obtain ⟨b, r⟩ := sampleLoop_book _ _ _ _ _ h2
      exact ⟨d₁, h1, b, r⟩
    · cases h
  · cases h

/-- **What a property of (book, roots) needs so that a yes of the switch hands it on**: the plain
ground's receiving at the chain's first tree's number keeps it, and it reads of a book no more than
SameNumbers keeps. -/
theorem yes_hands {P : TreeBook → Nat → Prop} {p : P2}
    (hRecv : ∀ (d d₁ : Desc.Plain.DState Unit) (sent : Array OracleNotice) (ids : Array Nat),
      Desc.Ground.recvP p.firstTree d sent = some (ids, d₁) → P d.book d.roots → P d₁.book d₁.roots)
    (hSame : ∀ (A B : TreeBook) (r : Nat), SameNumbers A B → P A r → P B r)
    {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') (hs : P s.book s.roots) : P s'.book s'.roots := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hx, hb, hr⟩ := yes_book h
  obtain ⟨d₁, h1, b, r⟩ := sendP_book hx
  have h2 := hRecv _ _ _ _ h1 hs
  rw [hr, r]
  exact hSame _ _ _ hb (by rw [b]; exact h2)

/-- The invariant «as many roots as trees, and every tree bears its place's number, counted from
ft» reads no more of a book than SameNumbers keeps. -/
theorem ordered_same (ft : Nat) (A B : TreeBook) (r : Nat) (h : SameNumbers A B)
    (k : r = A.trees.size ∧ ∀ z T, A.trees[z]? = some T → T.number = ft + z) :
    r = B.trees.size ∧ ∀ z T, B.trees[z]? = some T → T.number = ft + z := by
  refine ⟨k.1.trans h.1.symm, fun z T hT => ?_⟩
  obtain ⟨T₀, h₀, e, _⟩ := h.2.2 z T hT
  rw [e]
  exact k.2 z T₀ h₀

/-! ### The four quiet steps leave the book and the count of roots -/

theorem mark_book (s : S) (n : String) : (s.mark n).book = s.book ∧ (s.mark n).roots = s.roots := by
  unfold S.mark
  split <;> exact ⟨rfl, rfl⟩

theorem enterFin_book (s : S) : s.enterFin.book = s.book ∧ s.enterFin.roots = s.roots := by
  unfold S.enterFin
  split
  · exact ⟨rfl, rfl⟩
  · exact mark_book s _

theorem enterHead_book (s : S) (tl : HTailF2) :
    (s.enterHead tl).book = s.book ∧ (s.enterHead tl).roots = s.roots := by
  unfold S.enterHead
  split
  · exact ⟨rfl, rfl⟩
  · exact mark_book s _

theorem openHead_book (s : S) : s.openHead.book = s.book ∧ s.openHead.roots = s.roots := by
  unfold S.openHead
  split
  · split
    · exact mark_book s _
    · exact ⟨rfl, rfl⟩
  · exact mark_book s _

theorem headFrontQ_book {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  have e := enterHead_book s tl
  rw [← enterHeadQ k.enters] at e
  rw [k.out]
  exact e

theorem headOpenQ_book {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  have e := openHead_book s
  rw [← openHeadQ k.opens] at e
  rw [k.out']
  exact e

theorem finishFrontQ_book {s s' : S} (h : finishFrontQ s = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s s').1 h
  have e := enterFin_book s
  rw [← enterFinQ k.enters] at e
  rw [k.out]
  exact e

theorem finishBehindQ_book {s s' : S} (h : finishBehindQ s = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots := by
  obtain ⟨a, m, _, _, rfl⟩ := (finishBehindQ_iff s s').1 h
  exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switchBehind_same
#print axioms VerifiableInference.Desc.First.K2.yes_book
#print axioms VerifiableInference.Desc.First.K2.sendP_book
#print axioms VerifiableInference.Desc.First.K2.yes_hands
#print axioms VerifiableInference.Desc.First.K2.ordered_same
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_book
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_book
