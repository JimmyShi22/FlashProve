-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/StillKeeps.lean: the kind «the code switch»: WHATEVER RELATION ON STATEMENTS
THE EIGHT PLAIN FUNCTIONS THAT BRING NO MESSAGE IN KEEP (CoreStill, Johnson/Desc/CoreKeeps.lean),
THE SWITCH's OWN STEPS AROUND ITS RECEIVING KEEP; and so: BEHIND A YES OF THE SWITCH THE BOOK HAS
AS MANY PLACES AS THE STATEMENT HAS MESSAGES. NO BLOCK IMPORTS THIS FILE.
WHY BESIDE K2C/Keeps.lean: that file asks GroundKeeps R, which the receiving must keep too: «the
number of messages stays» is no such relation. Here the receiving stands apart.
  Still Q              CoreStill at a relation that reads the two statements alone
  closeLedgerG_still · joinG_still · addRowsG_still · newGroupG_still · joins_still ·
  switchBehind_still · firstFront_still · finishFront_still · firstBehind_still
                       K2C/Keeps.lean's nine, over Still Q: the same proofs
  sampleLoop_still     behind sendP's receiving the statement is written by the admitting alone
  recvP_size           the receiving brings in just as many messages as are announced
  yes_size             a yes of the decision: with the front x that the block takes off the
                       record: x.st has s.st's number of messages, and s'.st has as many more as x
                       announces
  yes_has              a yes of the decision, at any of its three sorts of place:
                       s'.book.place.size = s'.st.oracles.size: NO PREMISE ON s: the receiving's
                       own test pins the two in front, both rise by the sending's number of
                       messages, and what follows leaves both
  headFrontQ_size · headOpenQ_size · finishFrontQ_size · finishBehindQ_size
                       the four quiet steps leave the number of messages
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SeatedAt
import Johnson.Desc.CoreKeepsSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 closeLedgerG joinG addRowsG
    newGroupG dOf firstFront
  finishFront firstBehind)
open VerifiableInference.Desc.Ground (CoreStill coreStill_size)

/-- CoreStill at a relation that reads the two statements alone. -/
abbrev Still (Q : Statement → Statement → Prop) : Prop := CoreStill fun a b => Q a.st b.st

variable {Q : Statement → Statement → Prop}

theorem still_refl (H : Still Q) (S : Statement) : Q S S := H.refl ⟨S, {}, 0⟩

theorem still_trans (H : Still Q) {A B C : Statement} (h : Q A B) (k : Q B C) : Q A C :=
  H.trans (A := ⟨A, {}, 0⟩) (B := ⟨B, {}, 0⟩) (C := ⟨C, {}, 0⟩) h k

theorem closeLedgerG_still (H : Still Q) {S S' : Statement} {o : Nat} (h : closeLedgerG S o =
    .ok S') : Q S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    exact H.closeLedger (dOf S) d o hd
  · cases h

theorem joinG_still (H : Still Q) {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g
    o kept = .ok S') :
    Q S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact H.join (dOf S) d g o kept hd
  · cases h

theorem addRowsG_still (H : Still Q) {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : Q S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    exact CoreStill.addRows H (dOf S) d g rows hd
  · cases h

theorem newGroupG_still (H : Still Q) {S S' : Statement} {c m g : Nat} (h : newGroupG S c m =
    .ok (S', g)) :
    Q S S' := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    exact H.newGroup (dOf S) d c m _ hd
  · cases h

/-- A fold of joins. -/
theorem joins_still (H : Still Q) {α : Type} (f : Statement → α → Except String Statement)
    (hf : ∀ S a S', f S a = .ok S' → Q S S') : ∀ (l : List α) (S S' : Statement),
        l.foldlM f S = .ok S' → Q S S'
  | [], S, S', h => by
    cases h
    exact still_refl H _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨T, h1, h2⟩ := bindOk h
    exact still_trans H (hf _ _ _ h1) (joins_still H f hf l T S' h2)

theorem switchBehind_still (H : Still Q) {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    Q i.st o.st := by
  obtain ⟨c, y, S1, S2, S3, rows, b⟩ := switchBehind_inv h
  have h1 : Q i.st S1 := by
    have hl := b.hLedger
    split at hl
    · exact closeLedgerG_still H hl
    · cases hl
      exact still_refl H _
  have h2 : Q S1 S2 := joinG_still H b.hJoinG
  have h3 : Q S2 S3 := by
    have hk := b.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact joins_still H _ (fun _ _ _ e => joinG_still H e) _ _ _ hk
  have h4 : Q S3 o.st := addRowsG_still H b.hAdded
  exact still_trans H h1 (still_trans H h2 (still_trans H h3 h4))

theorem firstFront_still (H : Still Q) {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S f = .ok x) : Q S x.st := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_still H a.opened

theorem finishFront_still (H : Still Q) {S : Statement} {f : ReqFrame} {x :
    _root_.Tw.K2.Front}
    (h : finishFront S f = .ok x) : Q S x.st := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_still H a.opened

theorem firstBehind_still (H : Still Q) {S : Statement} {x : _root_.Tw.K2.Front} {s :
    Switched} {plain : List E}
    {S' : Statement} {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x s plain = .ok (S', f,
        mine)) : Q S S' := by
  obtain ⟨mask, a⟩ := (_root_.Tw.K2.firstBehind_iff S x s plain S' f mine).1 h
  exact joins_still H _ (fun _ _ _ e => joinG_still H e) _ _ _ a.joins


theorem sampleLoop_still (H : Still Q) {p : Desc.Plain.GPar} {codes : Codes}
    {seeds : List SampleSeed} :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : Desc.Plain.DState Unit) (left : List E),
      Desc.Plain.sampleLoop Desc.Plain.groundG p codes seeds l ys d = some (d', left) → Q d.st d'.st
  | [], ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact still_refl H _
  | (o, s) :: l, ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d₁ ha
        exact still_trans H (H.admit d d₁ o rows ha) (sampleLoop_still H l ys' d₁ d' left h)

/-- A yes of sendP: its receiving, and Q from the statement behind the receiving on. -/
theorem sendP_still (H : Still Q) {p : Desc.Plain.GPar} {own : Bool}
    {d d' : Desc.Plain.DState Unit} {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView} {ids sd an need}
    (h : Desc.Plain.sendP Desc.Plain.groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d')) :
    ∃ d₁, Desc.Ground.recvP p.firstTree d sent = some (ids, d₁) ∧ Q d₁.st d'.st := by
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
      exact ⟨d₁, h1, sampleLoop_still H _ _ _ _ _ h2⟩
    · cases h
  · cases h

theorem recvP_size {L : Type} {ft : Nat} {d d' : Desc.Plain.DState L} {sent : Array OracleNotice}
    {ids : Array Nat} (h : Desc.Ground.recvP ft d sent = some (ids, d')) :
    d'.st.oracles.size = d.st.oracles.size + sent.size := by
  unfold Desc.Ground.recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    show (d.st.oracles ++ sent.map _).size = _
    rw [Array.size_append, Array.size_map]
  · cases h

/-- The relation «as many messages». -/
abbrev SameSize (S S' : Statement) : Prop := S'.oracles.size = S.oracles.size

theorem yes_size {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, FrontOf p s x ∧ x.st.oracles.size = s.st.oracles.size ∧
      x.st.oracles.size = s.book.place.size ∧
      s'.st.oracles.size = x.st.oracles.size + (switchNotices x.T x.others).size ∧
      s'.book.place.size = s.book.place.size + (switchNotices x.T x.others).size := by
  have H : Still SameSize := coreStill_size
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩
        x r₁ r₂ (flat p gs) = .ok (w, roots) →
      x.st.oracles.size = s.book.place.size ∧
      w.st.oracles.size = x.st.oracles.size + (switchNotices x.T x.others).size ∧
      w.book.place.size = s.book.place.size + (switchNotices x.T x.others).size := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    obtain ⟨d₁, h1, q1⟩ := sendP_still H hx
    obtain ⟨d₂, h2, b, _⟩ := sendP_book hx
    obtain rfl : d₁ = d₂ := by
      have := h1.symm.trans h2
      injection this with this
      exact congrArg Prod.snd this
    obtain ⟨_, lay, _, St⟩ := Desc.Book.recvP_seat _ _ _ _ _ h1
    have q2 : SameSize d'.st w.st := switchBehind_still H k.hBehind
    have sb := switchBehind_same k.hBehind
    refine ⟨St.step, ?_, ?_⟩
    · exact q2.trans (q1.trans (recvP_size h1))
    · rw [sb.2.1]
      show d'.book.place.size = _
      rw [b]
      exact St.count
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨a1, a2, a3⟩ := key k.hSwitch
    refine ⟨x, Or.inl ⟨hp, k.hFront⟩, firstFront_still H k.hFront, a1, ?_, ?_⟩
    · rw [k.hOut]
      exact (firstBehind_still H k.hBehind).trans a2
    · rw [k.hOut]
      exact a3
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨a1, a2, a3⟩ := key k.hSwitch
    refine ⟨_, Or.inr (Or.inl ⟨hp, a, G, k.hHere, k.hGroup, rfl⟩), rfl, a1, ?_, ?_⟩
    · rw [k.hOut]
      exact a2
    · rw [k.hOut]
      exact a3
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨a1, a2, a3⟩ := key k.hSwitch
    refine ⟨_, Or.inr (Or.inr ⟨hp, a, G, k.hHere, k.hLaid, rfl⟩), rfl, a1, ?_, ?_⟩
    · rw [k.hOut]
      exact a2
    · rw [k.hOut]
      exact a3

/-- **Behind a yes of the switch the book has as many places as the statement has messages.** -/
theorem yes_has {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    s'.book.place.size = s'.st.oracles.size := by
  obtain ⟨x, _, _, a1, a2, a3⟩ := yes_size h
  rw [a2, a3, a1]

theorem headFrontQ_size {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.st.oracles.size = s.st.oracles.size := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  rw [k.out]
  exact firstFront_still (Q := SameSize) coreStill_size k.front

theorem headOpenQ_size {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    s'.st.oracles.size = s.st.oracles.size := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  rw [k.out']
  exact firstBehind_still (Q := SameSize) coreStill_size k.behind

theorem finishFrontQ_size {s s' : S} (h : finishFrontQ s = .ok s') :
    s'.st.oracles.size = s.st.oracles.size := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s s').1 h
  rw [k.out]
  exact finishFront_still (Q := SameSize) coreStill_size k.front

theorem finishBehindQ_size {s s' : S} (h : finishBehindQ s = .ok s') :
    s'.st.oracles.size = s.st.oracles.size := by rw [finishBehindQ_st h]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switchBehind_still
#print axioms VerifiableInference.Desc.First.K2.yes_size
#print axioms VerifiableInference.Desc.First.K2.yes_has
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_size
