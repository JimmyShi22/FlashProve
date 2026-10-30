-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawBookNames.lean: THE SMALLNESS TEST: "THE BOOK NAMES": WHAT IS LEFT OF THE
TEST `Named.namedB` BEHIND THE YES OF THE STEP THAT CLOSES THE LIST OF TABLES, CUT INTO INVARIANTS
OF THE CARRIED RECORD THAT A WALK OVER THE BLOCKS CAN CARRY.

`BookNames p s` (Johnson/Desc/First/K8/LawNamed.lean): the book has each message in which an array
lies that the matrix multiplies, in a tree that the place names, and lists it there. Here it follows
from:
  `Book.BookFits B` (Johnson/Desc/Book/BookFits.lean): THE BOOK'S TWO TABLES ARE
    INVERSE: where `place` has a message at tenant t of tree j, tree j's list of parts has that
    message at t. `partAt_of_fits`: in this file's letters.
  `BookHas s`: every oracle message of the statement has a place in the book.
  `SentHere a b a' b' B L`: AT THE LINK UNDER WAY: the kept messages' copies and the link's own
    messages of moment 0 sit in trees with numbers from a up to b; its own messages of moment 1 in
    trees from a' up to b'. Meant: a, b: the number of trees in front of and behind the link's first
    sending; a', b': the like at the sending of the reads.
  `sentHere_of_lists`: IT FOLLOWS from what the two sendings give, at the record in front of the
    draw: the frame's list of own messages is own0 ++ ids; the kept copies and own0 sit in trees
    from a up to b, ids in trees from a' up to b'; and the shape lists the link's messages of moment
    0 in front of own0's length and those of moment 1 behind.
  `moments_cut`, `momentsOk_of_shapeOk`: THE LAST OF THESE FOLLOWS FROM THE PUBLIC TEST ON THE SHAPE
    (`reqShapeOk`, OnBytes/Iop/Req.lean: a link's messages come by moment), where own0's length is
    the number of the link's messages of moment 0.
  `sentHere_of_cut`, `cut_of_shapeOk`, `sentHere_of_cut_shape`: THE SAME FROM A CUT OF THE FRAME'S
    LIST of own messages at the frame's own number of messages of moment 0: the form in which
    another file's walk over the link's blocks ends.
  `earlyB tl L`: A TEST ON PUBLIC VALUES, WITH CODE: every array that the matrix multiplies lies in
    a message that was born at another link, or has moment 0 or 1. `earlyB_false_of_late`: IT CAN
    SAY NO: where one such array lies in a message of this link with another moment.
    `earlyB_of_order`: IT FOLLOWS FROM THE GUARD OF ORDER where the link has had at most two moments
    (`L.moments ≤ 2`) and the frame's number of the link is the link's.
  `liesAt_spec`, `namedNow_kept`: what the running text's two readings say. THE MOMENT in
    `Order.liesAt`'s value and the moment in `SentHere` ARE READ OFF ONE TABLE: the frame's shape,
    at the link and the message's number.
  `bookNames_of_inv`: **these four, a yes of the guard of order, and "the place names the trees from
    a up to b and from a' up to b'" give `BookNames p s`.**
  `namedAt_of_inv`: **so the test at the carried record says yes.** THIS IS THE THEOREM TO CITE:
    `BookNames` alone holds idly where no link is open.
Definitions, statements and proofs.
Limits. NONE OF THE FOUR IS SHOWN OF ANY RECORD HERE. `BookFits` and `BookHas` are made at every
sending and kept by every block that leaves the book and the statement's messages; `SentHere` is
made by two sendings of the link and kept by whatever leaves the book's old places and the frame's
two lists: laws on other blocks. THAT THE RUN'S FOUR NUMBERS a, b, a', b' ARE THE PLAN'S, so that
the place names just these trees, IS A PREMISE (`hM`, `hR`), as is that a tree's number in the book
is its number in the first chain's order of sending. That a kept copy holds the earlier link's array
is the switch's law, not said here.

-/
import Johnson.Desc.First.K8.LawNamed
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Named
open OnBytes OnBytes.Model

/-- Where the book's two tables are inverse (`Book.BookFits`), `partAt` at a message's place gives
the message. -/
theorem partAt_of_fits {B : TreeBook} (h : Book.BookFits B) {o : Nat} {jt : Nat × Nat}
    (hq : B.place[o]? = some jt) : partAt B jt.1 jt.2 = some o := by
  obtain ⟨t, a, b⟩ := h o jt hq
  unfold partAt
  rw [a]
  exact b

/-- Every oracle message of the statement has a place in the book. -/
def BookHas (s : S) : Prop := s.book.place.size = s.st.oracles.size

/-- At the link under way: in which trees the kept copies and the link's own messages sit. -/
def SentHere (a b a' b' : Nat) (B : TreeBook) (L : LinkCtx) : Prop :=
  (∀ o ∈ L.check.frame.keptBefore.toList, ∀ jt : Nat × Nat, B.place[o]? = some jt →
    a ≤ jt.1 ∧ jt.1 < b) ∧
  ∀ (j o : Nat) (sh : Params.ReqLink) (m : Params.ReqMessage), L.check.frame.own[j]? = some o →
    L.check.frame.shape.link[L.check.frame.link]? = some sh → sh.messages[j]? = some m →
    ∀ jt : Nat × Nat, B.place[o]? = some jt →
      (m.moment = 0 → a ≤ jt.1 ∧ jt.1 < b) ∧ (m.moment = 1 → a' ≤ jt.1 ∧ jt.1 < b')

/-- **`SentHere` from what the link's two sendings give**: own0: the link's own messages that its
first sending sent; ids: those that the sending of the reads sent. -/
theorem sentHere_of_lists {a b a' b' : Nat} {B : TreeBook} {L : LinkCtx} (own0 ids : Array Nat)
    (hown : L.check.frame.own = own0 ++ ids)
    (hK : ∀ o ∈ L.check.frame.keptBefore.toList,
      ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b)
    (h0 : ∀ o ∈ own0.toList, ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b)
    (h1 : ∀ o ∈ ids.toList, ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a' ≤ jt.1 ∧ jt.1 < b')
    (h3 : ∀ (j : Nat) (sh : Params.ReqLink) (m : Params.ReqMessage),
      L.check.frame.shape.link[L.check.frame.link]? = some sh → sh.messages[j]? = some m →
      (m.moment = 0 → j < own0.size) ∧ (m.moment = 1 → own0.size ≤ j)) :
    SentHere a b a' b' B L := by
  refine ⟨fun o ho jt hjt => ?_, fun j o sh m ho hsh hm jt hjt => ⟨fun e0 => ?_, fun e1 => ?_⟩⟩
  · obtain ⟨jt', e, x1, x2⟩ := hK o ho
    obtain rfl : jt' = jt := Option.some.inj (e.symm.trans hjt)
    exact ⟨x1, x2⟩
  · have hj := (h3 j sh m hsh hm).1 e0
    rw [hown, Array.getElem?_append_left hj] at ho
    obtain ⟨jt', e, x1, x2⟩ := h0 o (Array.mem_toList_iff.2 (Array.mem_of_getElem? ho))
    obtain rfl : jt' = jt := Option.some.inj (e.symm.trans hjt)
    exact ⟨x1, x2⟩
  · have hj := (h3 j sh m hsh hm).2 e1
    rw [hown, Array.getElem?_append_right hj] at ho
    obtain ⟨jt', e, x1, x2⟩ := h1 o (Array.mem_toList_iff.2 (Array.mem_of_getElem? ho))
    obtain rfl : jt' = jt := Option.some.inj (e.symm.trans hjt)
    exact ⟨x1, x2⟩

/-! ## The shape lists a link's messages by moment -/

/-- Behind a message of moment t no message has a lesser moment. -/
theorem moments_ge : ∀ (t : Nat) (ms : List Params.ReqMessage), reqMomentsOk t ms = true →
    ∀ (j : Nat) (m : Params.ReqMessage), ms[j]? = some m → t ≤ m.moment
  | _, [], _, _, _, h => by simp at h
  | t, m0 :: ms, hk, j, m, h => by
    simp only [reqMomentsOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hk
    cases j with
    | zero =>
      obtain rfl : m0 = m := by simpa using h
      omega
    | succ k =>
      have := moments_ge m0.moment ms hk.2 k m (by simpa using h)
      omega

/-- **The messages of moment 0 stand in front, as many as there are; those of moment 1 behind
them.** -/
theorem moments_cut : ∀ (ms : List Params.ReqMessage), reqMomentsOk 0 ms = true →
    ∀ (j : Nat) (m : Params.ReqMessage), ms[j]? = some m →
      (m.moment = 0 → j < (ms.filter fun x => x.moment == 0).length) ∧
        (m.moment = 1 → (ms.filter fun x => x.moment == 0).length ≤ j)
  | [], _, _, _, h => by simp at h
  | m0 :: ms, hk, j, m, h => by
    simp only [reqMomentsOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hk
    obtain ⟨h0, hr⟩ := hk
    rcases h0 with h0 | h0
    · rw [h0] at hr
      have hf : ((m0 :: ms).filter fun x => x.moment == 0).length =
          (ms.filter fun x => x.moment == 0).length + 1 := by
        rw [List.filter_cons_of_pos (by simpa using h0)]
        rfl
      rw [hf]
      cases j with
      | zero =>
        obtain rfl : m0 = m := by simpa using h
        exact ⟨fun _ => by omega, fun e => by omega⟩
      | succ k =>
        obtain ⟨a, b⟩ := moments_cut ms hr k m (by simpa using h)
        exact ⟨fun e => by have := a e; omega, fun e => by have := b e; omega⟩
    · have hall : ∀ (k : Nat) (x : Params.ReqMessage), (m0 :: ms)[k]? = some x → 1 ≤ x.moment := by
        intro k x hx
        cases k with
        | zero =>
          obtain rfl : m0 = x := by simpa using hx
          omega
        | succ k' =>
          have := moments_ge m0.moment ms hr k' x (by simpa using hx)
          omega
      have hf : ((m0 :: ms).filter fun x => x.moment == 0) = [] := by
        refine List.filter_eq_nil_iff.2 fun x hx => ?_
        obtain ⟨k, hk'⟩ := List.getElem?_of_mem hx
        have := hall k x hk'
        simp only [beq_iff_eq]
        omega
      rw [hf]
      exact ⟨fun e => by have := hall j m h; omega, fun _ => Nat.zero_le _⟩

/-- What the public test on the shape gives of one link. -/
theorem momentsOk_of_shapeOk {s : Params.ReqShape} (h : reqShapeOk s = true) {l : Nat}
    {sh : Params.ReqLink} (hl : s.link[l]? = some sh) : reqMomentsOk 0 sh.messages = true := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hx := h.1.1.1.1.1.1.2 (sh, l) (List.mk_mem_zipIdx_iff_getElem?.2 hl)
  have hk := hx.1
  unfold reqLinkOk at hk
  simp only [Bool.and_eq_true] at hk
  exact hk.1.2

/-- Under the public test on the shape: the frame's own number of messages of moment 0 cuts the
link's list of messages. -/
theorem cut_of_shapeOk {f : ReqFrame} (h : reqShapeOk f.shape = true) (j : Nat)
    (sh : Params.ReqLink) (m : Params.ReqMessage) (hsh : f.shape.link[f.link]? = some sh)
    (hm : sh.messages[j]? = some m) :
    (m.moment = 0 → j < (f.atMoment 0).length) ∧ (m.moment = 1 → (f.atMoment 0).length ≤ j) := by
  have e : f.atMoment 0 = sh.messages.filter fun x => x.moment == 0 := by
    unfold ReqFrame.atMoment
    rw [hsh]
    rfl
  rw [e]
  exact moments_cut sh.messages (momentsOk_of_shapeOk h hsh) j m hm

/-- **`SentHere` from a cut of the frame's list of own messages**: below k0 in trees from a up to b,
from k0 on in trees from a' up to b'. -/
theorem sentHere_of_cut {a b a' b' : Nat} {B : TreeBook} {L : LinkCtx} (k0 : Nat)
    (hK : ∀ o ∈ L.check.frame.keptBefore.toList,
      ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b)
    (hOwn : ∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat, B.place[o]? = some jt ∧
      ((j < k0 ∧ a ≤ jt.1 ∧ jt.1 < b) ∨ (k0 ≤ j ∧ a' ≤ jt.1 ∧ jt.1 < b')))
    (h3 : ∀ (j : Nat) (sh : Params.ReqLink) (m : Params.ReqMessage),
      L.check.frame.shape.link[L.check.frame.link]? = some sh → sh.messages[j]? = some m →
      (m.moment = 0 → j < k0) ∧ (m.moment = 1 → k0 ≤ j)) :
    SentHere a b a' b' B L := by
  refine ⟨fun o ho jt hjt => ?_, fun j o sh m ho hsh hm jt hjt => ?_⟩
  · obtain ⟨jt', e, x1, x2⟩ := hK o ho
    obtain rfl : jt' = jt := Option.some.inj (e.symm.trans hjt)
    exact ⟨x1, x2⟩
  · obtain ⟨jt', e, hc⟩ := hOwn j o ho
    obtain rfl : jt' = jt := Option.some.inj (e.symm.trans hjt)
    obtain ⟨c0, c1⟩ := h3 j sh m hsh hm
    refine ⟨fun e0 => ?_, fun e1 => ?_⟩
    · rcases hc with ⟨_, x1, x2⟩ | ⟨hk, _, _⟩
      · exact ⟨x1, x2⟩
      · have := c0 e0
        omega
    · rcases hc with ⟨hk, _, _⟩ | ⟨_, x1, x2⟩
      · have := c1 e1
        omega
      · exact ⟨x1, x2⟩

/-- The same with the cut at the frame's own number of messages of moment 0, under the public test
on the shape. -/
theorem sentHere_of_cut_shape {a b a' b' : Nat} {B : TreeBook} {L : LinkCtx}
    (hs : reqShapeOk L.check.frame.shape = true)
    (hK : ∀ o ∈ L.check.frame.keptBefore.toList,
      ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b)
    (hOwn : ∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat, B.place[o]? = some jt ∧
      ((j < (L.check.frame.atMoment 0).length ∧ a ≤ jt.1 ∧ jt.1 < b) ∨
        ((L.check.frame.atMoment 0).length ≤ j ∧ a' ≤ jt.1 ∧ jt.1 < b'))) :
    SentHere a b a' b' B L :=
  sentHere_of_cut _ hK hOwn fun j sh m hsh hm => cut_of_shapeOk hs j sh m hsh hm

/-- A test on public values: every array that the matrix multiplies lies in a message that was born
at another link, or has moment 0 or 1. -/
def earlyB (tl : HTailF2) (L : LinkCtx) : Bool :=
  (arrays tl).all fun t =>
    match Order.liesAt L t with
    | none => false
    | some w => w.born != L.check.frame.link || w.moment == 0 || w.moment == 1

/-- **The test can say no**: one array in a message of this link with another moment. -/
theorem earlyB_false_of_late {tl : HTailF2} {L : LinkCtx} {t : Nat} {w : Order.Lies}
    (ht : t ∈ arrays tl) (hw : Order.liesAt L t = some w) (hb : w.born = L.check.frame.link)
    (h0 : w.moment ≠ 0) (h1 : w.moment ≠ 1) : earlyB tl L = false := by
  cases h : earlyB tl L with
  | false => rfl
  | true =>
    have he := List.all_eq_true.1 h t ht
    simp only [hw, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at he
    rcases he with (he | he) | he
    · exact absurd hb he
    · exact absurd he h0
    · exact absurd he h1

/-- **The test follows from the guard of order**, where the link has had at most two moments and the
frame's number of the link is the link's. -/
theorem earlyB_of_order {tl : HTailF2} {L : LinkCtx} {S₀ : Statement}
    (hO : Order.orderOk tl L S₀ = true) (hl : L.check.frame.link = L.link) (hm : L.moments ≤ 2) :
    earlyB tl L = true := by
  refine List.all_eq_true.2 fun t ht => ?_
  obtain ⟨_, h1, h2⟩ := VerifiableInference.Desc.K8.ReadsQuiet.orderOk_fixed hO
  have hf : Order.fixed L S₀ t = true := by
    unfold arrays at ht
    rcases List.mem_append.1 ht with ht | ht
    · exact h1 t (by simpa using ht)
    · obtain ⟨n, hn, e⟩ := List.mem_filterMap.1 ht
      exact h2 n (List.mem_range.1 hn) t e
  obtain ⟨w, _, _, a1, a2, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.fixed_sampled hf
  simp only [a1, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases hb : w.born = L.link
  · unfold Order.sentInFront at a2
    rw [if_pos (by simpa using hb)] at a2
    have : w.moment < L.moments := by simpa using a2
    omega
  · exact Or.inl (Or.inl (by rw [hl]; exact hb))

/-- What `Order.liesAt` says of the message's moment. -/
theorem liesAt_spec {L : LinkCtx} {t : Nat} {w : Order.Lies} (h : Order.liesAt L t = some w) :
    ∃ sh m, L.check.frame.shape.link[w.born]? = some sh ∧ sh.messages[w.message]? = some m ∧
      w.moment = m.moment := by
  simp only [Order.liesAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨named, _, laid, _, sh, hsh, m, hm, rfl⟩ := h
  exact ⟨sh, m, hsh, hm, rfl⟩

/-- A message born at another link is named, now, among the kept copies. -/
theorem namedNow_kept {f : ReqFrame} {w : Order.Lies} {o : Nat} (h : Order.namedNow f w = some o)
    (hb : w.born ≠ f.link) : o ∈ f.keptBefore.toList := by
  unfold Order.namedNow at h
  split at h
  · rw [if_neg (by simpa using hb)] at h
    split at h
    · exact nomatch h
    · exact Array.mem_toList_iff.2 (Array.mem_of_getElem? h)
  · exact nomatch h

/-- **The invariants give "the book names".** -/
theorem bookNames_of_inv {p : Par} {s : S} {a b a' b' : Nat} (h1 : Book.BookFits s.book)
    (h2 : BookHas s) (hL : ∀ L, s.link? = some L → SentHere a b a' b' s.book L)
    (hE : ∀ tl L, s.tl? = some tl → s.link? = some L →
      earlyB tl L = true ∧ Order.orderOk tl L s.st = true)
    (hM : ∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn)
    (hR : ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn) :
    BookNames p s := by
  intro tl L ht hl o ho
  obtain ⟨hEa, hO⟩ := hE tl L ht hl
  obtain ⟨t, htm, hto⟩ := mem_msgs.1 ho
  obtain ⟨o', x, e1, e2, _⟩ := msgNow_of_order hO htm
  obtain rfl : o = o' := Option.some.inj (hto.symm.trans e1)
  have hlt : o < s.book.place.size := by
    rw [h2]
    exact (Array.getElem?_eq_some_iff.1 e2).1
  obtain ⟨jt, hjt⟩ : ∃ jt, s.book.place[o]? = some jt := ⟨_, Array.getElem?_eq_getElem hlt⟩
  refine ⟨jt, hjt, ?_, partAt_of_fits h1 hjt⟩
  unfold msgNow at hto
  cases hw : Order.liesAt L t with
  | none => simp [hw] at hto
  | some w =>
    rw [hw] at hto
    have hn : Order.namedNow L.check.frame w = some o := hto
    have he := List.all_eq_true.1 hEa t htm
    simp only [hw, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at he
    obtain ⟨hK, hOwn⟩ := hL L hl
    by_cases hb : w.born = L.check.frame.link
    · obtain ⟨sh, m, a1, a2, a3⟩ := liesAt_spec hw
      rw [hb] at a1
      have ho' : L.check.frame.own[w.message]? = some o := by
        rw [namedNow_own L w hb] at hn
        unfold ownNow at hn
        split at hn
        · exact hn
        · exact nomatch hn
      obtain ⟨c0, c1⟩ := hOwn w.message o sh m ho' a1 a2 jt hjt
      rcases he with (he | he) | he
      · exact absurd hb he
      · obtain ⟨x1, x2⟩ := c0 (a3 ▸ he)
        exact hM _ x1 x2
      · obtain ⟨x1, x2⟩ := c1 (a3 ▸ he)
        exact hR _ x1 x2
    · obtain ⟨x1, x2⟩ := hK o (namedNow_kept hn hb) jt hjt
      exact hM _ x1 x2

/-- So the test at the carried record says yes. -/
theorem namedAt_of_inv {p : Par} {s : S} {a b a' b' : Nat} {tl : HTailF2} {L : LinkCtx}
    (ht : s.tl? = some tl) (hl : s.link? = some L) (h1 : Book.BookFits s.book) (h2 : BookHas s)
    (hS : SentHere a b a' b' s.book L) (hEa : earlyB tl L = true)
    (hO : Order.orderOk tl L s.st = true)
    (hM : ∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn)
    (hR : ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn) :
    namedAt p s = true := by
  unfold namedAt
  rw [ht, hl]
  refine namedB_of_order hO (bookNames_of_inv h1 h2 (fun L' e => ?_) (fun tl' L' e1 e2 => ?_) hM hR
    tl L ht hl)
  · obtain rfl : L = L' := Option.some.inj (hl.symm.trans e)
    exact hS
  · obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans e1)
    obtain rfl : L = L' := Option.some.inj (hl.symm.trans e2)
    exact ⟨hEa, hO⟩

end VerifiableInference.Desc.First.K8.Named

#print axioms VerifiableInference.Desc.First.K8.Named.sentHere_of_lists
#print axioms VerifiableInference.Desc.First.K8.Named.moments_cut
#print axioms VerifiableInference.Desc.First.K8.Named.sentHere_of_cut_shape
#print axioms VerifiableInference.Desc.First.K8.Named.momentsOk_of_shapeOk
#print axioms VerifiableInference.Desc.First.K8.Named.earlyB_false_of_late
#print axioms VerifiableInference.Desc.First.K8.Named.earlyB_of_order
#print axioms VerifiableInference.Desc.First.K8.Named.partAt_of_fits
#print axioms VerifiableInference.Desc.First.K8.Named.liesAt_spec
#print axioms VerifiableInference.Desc.First.K8.Named.namedNow_kept
#print axioms VerifiableInference.Desc.First.K8.Named.bookNames_of_inv
#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_of_inv
