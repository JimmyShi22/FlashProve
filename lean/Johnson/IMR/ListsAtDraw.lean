-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ListsAtDraw.lean: THE LINK-LOCAL STRETCH AT THE PROOF FILE's SEAT:
AT A LAYERS' OR AN ATTENTION LINK l, 1 ≤ l < 24, IN THE GOALS' SCOPE: IN WHICH TREES THE MESSAGES
LIE WHOSE NUMBERS THE LIVE FRAME's TWO LISTS (keptBefore, own) HOLD AT THE RECORD IN FRONT OF KIND
K8's BLOCK.

THE BLOCKS BETWEEN, by the driver's list of kinds and the seats (Johnson/IMR/K2Seat.lean,
K3Seat.lean,
K4Seat.lean, K5Seat.lean, K1Seat.lean, FlatScope.lean): c.blocksInOrder[14 l + 2 + i] is the link's hearing
block number i: 0: kind K2's switch, with a block of the frames' lot joined behind, or alone; 1:
kind K3's lookup; 2: kind K4's or K5's block; 3: kind K1's sending of the reads with the quiet step
behind the reads joined; 4: kind K8's block.
  tools: two_of_send, live_between, live_open, link_between; Johnson/IMR/FoldTools.lean and
    Johnson/IMR/OpenWalk.lean
    hold the others.
  LV, framesOf_live, frameBlock_live: EVERY block of the frames' lot, whichever, leaves the live
    state of the calls, the book and the count of roots: so it need not be known which is joined.
  first_lists: the first sending's block.
  ctx_link, quiet_fwd, quiet_back: a Quiet step leaves the open link's state of the calls, its count
    of moments and its number.
  open_roots: as many roots as trees, by Johnson/IMR/OpenWalk.lean's open_fold.
  commit_lists, reads_lists: the reads' block: commitAtS_frame
    (Johnson/Desc/K1/Law/FrameAtLater.lean) and commitAtS_seated (SeatedAtRecord.lean).
  stretch_end, mid_stretch: the stretch's end and its middle, for all three sorts of first block.
  lists_at_draw: THE TOP.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: the files on the book's
names.
Not claimed: that the three counts of roots are the plan's numbers; which message of the shape
own[j] is; anything at link 0 or at the head's link. No soundness.
-/
import Johnson.IMR.BookNamesFront
import Johnson.IMR.FoldTools
import Johnson.IMR.OpenWalk
import Johnson.IMR.K1Seat
import Johnson.IMR.K2Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.FlatScope
import Johnson.Top.H0.Tw.K2C.LinkNumbers
import Johnson.Desc.K1.Law.SeatedAtRecord
import Johnson.Desc.K1.Law.FrameAtLater
import Johnson.Desc.K1.Law.LinkAtLater
import Johnson.IMR.FrameSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

/-! ## Tools -/

theorem two_of_send {L : Type} {P : K1.Par} {owed : Option Nat}
    {d : _root_.Desc.Plain.DState L} {rs : List Fmt.RoundView}
    {x : Array Nat × _root_.Desc.Plain.DState L} (h : K1.decideSend P owed d rs = .ok x) :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  match rs, h with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  | [], h => exact absurd h (by simp [K1.decideSend])
  | [_], h => exact absurd h (by simp [K1.decideSend])
  | _ :: _ :: _ :: _, h => exact absurd h (by simp [K1.decideSend])

theorem live_between {s : S} (h : s.atBetween = true) : s.live = s.check := by
  unfold S.atBetween at h
  unfold S.live S.link?
  split at h
  · rename_i hb
    rw [hb]
  · cases h

theorem live_open {s : S} {L : LinkCtx} (h : s.link? = some L) : s.live = L.check := by
  unfold S.live
  rw [h]

/-! ## Every block of the frames' lot -/

/-- The live state of the calls, the book and the count of roots stay; and a link that stands open
behind a step from between the links has passed one moment and bears its frame's number. -/
def LV (s t : S) : Prop :=
  t.live = s.live ∧ t.book = s.book ∧ t.roots = s.roots ∧
    (s.atBetween = true → ∀ L, t.link? = some L → L.moments = 1 ∧ L.link = L.check.frame.link)

theorem link_between {s : S} (h : s.atBetween = true) : s.link? = none := by
  unfold S.atBetween at h
  unfold S.link?
  split at h
  · rename_i hb
    rw [hb]
  · cases h

open Johnson.Desc.First.Walk in
theorem enters_live {f : S → Except String S} (he : Fn Enters f)
    (hl : ∀ s t, f s = .ok t → s.atBetween = true ∧ ∃ L, t.link? = some L ∧ L.check = s.check ∧
      L.moments = 1 ∧ L.link = s.check.frame.link) :
    Fn LV f := fun s t h => by
  obtain ⟨hB, L, h1, h2, h3, h4⟩ := hl s t h
  refine ⟨by rw [live_open h1, h2, live_between hB], (he s t h).2.2.1, (he s t h).2.2.2,
    fun _ L' hL' => ?_⟩
  obtain rfl : L = L' := Option.some.inj (h1.symm.trans hL')
  exact ⟨h3, by rw [h4, h2]⟩

open Johnson.Desc.First.Walk in
theorem clearWith_live (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) : Fn LV (clearWith X counts left row) :=
  fun _ t h => ⟨(Law.clear_carries h).1, (Law.clear_carries h).2.1, (Law.clear_carries h).2.2.1,
    fun _ L hL => by
      rw [link_between (Law.clear_carries h).2.2.2.2.2.2.2.2.2] at hL
      cases hL⟩

open Johnson.Desc.First.Walk in
theorem tailHead_live (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    Fn LV (Close.tailHead X lay lin) := clearWith_live _ _ _ _

open Johnson.Desc.First.Walk in
theorem layFront_live (l : Nat) : Fn LV (layFront l) := fun s t h => by
  rw [(Law.layFront_ok h).1]
  exact ⟨rfl, rfl, rfl, fun hB L hL => by rw [link_between hB] at hL; cases hL⟩

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
theorem framesOf_live {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn LV f.lay ∧ Fn LV f.opened ∧ Fn LV f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨layFront_live l, fun s t k => by
          cases k
          exact ⟨rfl, rfl, rfl, fun hB L hL => by rw [link_between hB] at hL; cases hL⟩,
        tailHead_live _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_live 0, enters_live (openLayZero_enters _ _ _) (fun s t k =>
            ⟨(Law.openLayZero_ok k).1, _, (Law.openLayZero_ok k).2.2.2.2.2.1, rfl, rfl,
              (Law.openLayZero_ok k).2.2.1.symm⟩),
          clearWith_live _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_live l, enters_live (openAtt_enters _) (fun s t k =>
            ⟨(Law.openAtt_ok k).1, _, (Law.openAtt_ok k).2.2.2.2.1, rfl, rfl,
              (Law.openAtt_ok k).2.2.2.1.symm⟩),
          clearWith_live _ _ _ _⟩
      · cases e
        exact ⟨layFront_live l, enters_live (openLay_enters _) (fun s t k =>
            ⟨(Law.openLay_ok k).1, _, (Law.openLay_ok k).2.2.2.2.2.1, rfl, rfl,
              (Law.openLay_ok k).2.2.2.1.symm⟩),
          clearWith_live _ _ _ _⟩

theorem frameBlock_live {Z : Pub} {fb : Block S Unit} (h : fb ∈ P1L20.blocksOf Z) :
    Decides LV fb := by
  unfold P1L20.blocksOf at h
  split at h
  · rename_i fs hfs
    obtain ⟨f, hf, h⟩ := List.mem_flatMap.1 h
    obtain ⟨k1, k2, k3⟩ := framesOf_live hfs f hf
    unfold ProofFile.frameBlocks at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact fun s _ _ t e => k1 s t e
    · exact fun s _ _ t e => k2 s t e
    · exact fun s _ _ t e => k3 s t e
  · obtain rfl := List.mem_singleton.1 h
    exact fun _ _ _ _ e => nomatch e

/-! ## The first sending's block -/

/-- The book places the message o in a tree whose number lies in [a, b). -/
def InTrees (B : TreeBook) (a b o : Nat) : Prop :=
  ∃ jt : Nat × Nat, B.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b

/-- What the first sending's block leaves, from s to t. -/
def FirstLists (s t : S) : Prop :=
  (∀ o ∈ t.live.frame.keptBefore.toList, InTrees t.book s.roots t.roots o) ∧
    (∀ (j o : Nat), t.live.frame.own[j]? = some o → InTrees t.book s.roots t.roots o) ∧
    t.live.frame.own.size = (s.check.frame.atMoment 0).length ∧
    t.live.frame.shape = s.check.frame.shape ∧ t.live.frame.link = s.check.frame.link ∧
    ∀ L, t.link? = some L → L.moments = 1 ∧ L.link = L.check.frame.link

theorem switch_lists {Z : Pub} {G : ProofFile.Ground} {l : Nat} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x)
    {s u : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok u) (hB : s.atBetween = true)
    (hR : s.roots = s.book.trees.size) : FirstLists s u := by
  rcases hx with ⟨-, hm⟩ | ⟨P, n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨v, a1, -⟩ := andThen_yes (n := x.name) h
      obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [e] at h
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link n) s rs
          gs = .ok u := h
      obtain ⟨t1, t2⟩ := K2.yes_link_trees rfl h' hR
      obtain ⟨y, lay, -, e1, e2, -, -, -, -, -, e3⟩ := K2.yes_link_frame rfl h'
      have hb : u.atBetween = true := by
        unfold S.atBetween
        rw [e2]
      rw [e1] at e3
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ := K2.link_inv rfl h'
      obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 Lk.hFront
      obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 Lk.hBehind
      have hsh : u.check.frame.shape = s.check.frame.shape := by
        rw [Lk.hOut]
        show f.shape = _
        rw [bA.frame]
        show x'.f.shape = _
        rw [a.out]
      have hlk : u.check.frame.link = s.check.frame.link := by
        rw [Lk.hOut]
        show f.link = _
        rw [bA.frame]
        show x'.f.link = _
        rw [a.out]
      unfold FirstLists
      rw [live_between hb]
      exact ⟨t1, t2, e3, hsh, hlk, fun L hL => by rw [link_between hb] at hL; cases hL⟩

/-- Behind the switch alone no link is open. -/
theorem switch_between {Z : Pub} {G : ProofFile.Ground} {l : Nat} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x)
    {s u : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok u) (hB : s.atBetween = true) : u.atBetween = true := by
  rcases hx with ⟨-, hm⟩ | ⟨P, n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨v, a1, -⟩ := andThen_yes (n := x.name) h
      obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [e] at h
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link n) s rs
          gs = .ok u := h
      obtain ⟨y, lay, -, -, e2, -⟩ := K2.yes_link_frame rfl h'
      unfold S.atBetween
      rw [e2]

theorem first_lists {Z : Pub} {G : ProofFile.Ground} {l : Nat} {b : Block S Cl} {x : Block S Unit}
    (hb : IM.LaidFramed Z b x.retype b.name
      { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hx : IM.K2Is Z G { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : b.decide s rs gs = .ok t) (hB : s.atBetween = true)
    (hR : s.roots = s.book.trees.size) : FirstLists s t := by
  rcases hb with ha | ⟨fb, hfb, e⟩
  · exact switch_lists hx ((IM.yes_alone ha (fun k => nomatch k) s t rs gs).1 h).1 hB hR
  · obtain ⟨u, a1, -, a2, -⟩ := IM.yes_with e h
    obtain ⟨k1, k2, k3, k4, k5, -⟩ := switch_lists hx a1 hB hR
    obtain ⟨v1, v2, v3, v4⟩ :=
      frameBlock_live hfb u _ _ t ((IM.guardMark_yes _ u t _ _).1 a2).1
    have hub : u.atBetween = true := switch_between hx a1 hB
    unfold FirstLists
    rw [v1, v2, v3]
    exact ⟨k1, k2, k3, k4, k5, v4 hub⟩

/-! ## The reads' block -/

theorem commitAtS_two {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS P link moment arrays : Block S Unit).decide s rs gs = .ok s') :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  simp only [K1.commitAtS] at h
  split at h
  · obtain ⟨y, hy, -⟩ := Keeps.emap_ok h
    obtain ⟨ids, d₁, f', h2, -⟩ := K1.commitOwn_ok P link moment arrays _ y rs gs hy
    exact two_of_send h2
  · cases h

/-- What the reads' sending leaves, from s to v. -/
def ReadsLists (s v : S) : Prop :=
  ∃ L L', s.link? = some L ∧ v.link? = some L' ∧
    L'.check.frame.keptBefore = L.check.frame.keptBefore ∧
    (∀ (j o : Nat), L'.check.frame.own[j]? = some o →
      (j < L.check.frame.own.size ∧ L.check.frame.own[j]? = some o) ∨
        (L.check.frame.own.size ≤ j ∧ InTrees v.book s.roots v.roots o)) ∧
    PlacesStay s.book v.book ∧ s.roots ≤ v.roots ∧
    L'.check.frame.shape = L.check.frame.shape ∧ L'.check.frame.link = L.check.frame.link ∧
    L'.moments = L.moments + 1 ∧ L'.link = L.link

theorem commit_lists {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s v : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS P link moment arrays : Block S Unit).decide s rs gs = .ok v)
    (hR : s.roots = s.book.trees.size) : ReadsLists s v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, L', a1, a2, e, -⟩ := K1.commitAtS_frame P link moment arrays s v r₁ r₂ gs h
  have Sd := K1.commitAtS_seated P link moment arrays s v r₁ r₂ gs h
  obtain ⟨M, M', b1, b2, m1, m2, -⟩ := K1.commitAtS_moments P link moment arrays s v _ gs h
  obtain rfl : L = M := Option.some.inj (a1.symm.trans b1)
  obtain rfl : L' = M' := Option.some.inj (a2.symm.trans b2)
  refine ⟨L, L', a1, a2, by rw [e], fun j o ho => ?_, Sd.seated.places, by rw [Sd.roots]; omega,
    by rw [e], by rw [e], m1, m2⟩
  rw [e] at ho
  have ho' : (L.check.frame.own ++
      (Array.range P.sent.size).map (· + s.st.oracles.size))[j]? = some o := ho
  by_cases lt : j < L.check.frame.own.size
  · rw [Array.getElem?_append_left lt] at ho'
    exact Or.inl ⟨lt, ho'⟩
  · refine Or.inr ⟨Nat.le_of_not_lt lt, ?_⟩
    rw [Array.getElem?_append_right (Nat.le_of_not_lt lt), Array.getElem?_map] at ho'
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 ho'
    obtain ⟨hi', ei⟩ := Array.getElem?_eq_some_iff.1 hi
    rw [Array.size_range] at hi'
    rw [Array.getElem_range] at ei
    subst ei
    refine ⟨_, by rw [Nat.add_comm]; exact Sd.seated.new _ hi', ?_, ?_⟩
    · show s.roots ≤ s.book.trees.size + _
      omega
    · show s.book.trees.size + _ < v.roots
      have := (Sd.seated.fits _ hi').1
      rw [Sd.roots]
      omega

/-- The reads' place's block, as kind K1's lot joins it: the sending, then a Quiet step. -/
theorem reads_lists {Z : Pub} {G : ProofFile.Ground} {l : Nat} {X : Stages.LinkH} {pr : Nat}
    {reads : Option (List Nat)} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok t)
    (hR : s.roots = s.book.trees.size) : ∃ v, ReadsLists s v ∧ Quiet v t := by
  obtain ⟨v, a1, a2⟩ := andThen_yes h
  exact ⟨v, commit_lists a1 hR,
    (orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2⟩

theorem alone_reads {Z : Pub} {G : ProofFile.Ground} {l : Nat} {X : Stages.LinkH} {pr : Nat}
    {reads : Option (List Nat)} {b : Block S Cl} {a : Place} (hk : a.kind ≠ KindName.K7)
    (la : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype b.name a)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : b.decide s rs gs = .ok t) (hR : s.roots = s.book.trees.size) :
    ∃ v, ReadsLists s v ∧ Quiet v t := by
  have h' : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok t :=
    ((IM.yes_alone la hk s t rs gs).1 h).1
  exact reads_lists h' hR

theorem alone_later {q : Params.First} {gp : _root_.Desc.Plain.GPar} {l pd m : Nat}
    {digits : Option (List Nat)} {b : Block S Cl} {a : Place} (hk : a.kind ≠ KindName.K7)
    (la : IM.LaidAlone ProofFile.sameReply b (K1.laterAt q gp l pd m digits : Block S Unit).retype
      b.name a)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : b.decide s rs gs = .ok t) (hR : s.roots = s.book.trees.size) :
    ∃ v, ReadsLists s v ∧ Quiet v t := by
  have h' : (K1.commitAtS (K1.parLater q gp l pd m) l m digits : Block S Unit).decide s rs gs =
      .ok t := ((IM.yes_alone la hk s t rs gs).1 h).1
  exact ⟨t, commit_lists h' hR, quiet_refl t⟩

/-! ## The fold -/

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- As many roots as trees, at every record in front of the blocks behind the last link. -/
theorem open_roots (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {ft : Nat} {p : ProofFile.InstPub} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok r) :
    r.1.roots = r.1.book.trees.size := by
  have K3 : SeatKeeps (PR numberedP) := seatKeeps_front
    (fun d d' sent ids e k => Book.recvP_numbered 0 d d' sent ids e k) numbered_sameNumbers
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  refine (open_fold K3 O trivial (fun _ _ _ => trivial) hk h ?_).1
  show numberedP (ProofFile.startS Z p).book (ProofFile.startS Z p).roots
  rw [(start_empty hZ p).1, (start_empty hZ p).2]
  exact empty_numbered

/-! ## A Quiet step and the open link -/

theorem ctx_link {s : S} {L : LinkCtx} (h : s.link? = some L) :
    (ctxOf s).2.map (fun x => x.2.2.1) = some L.link := by
  unfold S.link? at h
  unfold ctxOf
  split at h
  · rename_i a ha
    cases h
    simp [ha]
  · rename_i a ha
    cases h
    simp [ha]
  · rename_i a ha
    split at h
    · cases h
      simp [ha]
    · cases h
  · cases h

theorem quiet_fwd {s t : S} (q : Quiet s t) {L : LinkCtx} (h : s.link? = some L) :
    ∃ L', t.link? = some L' ∧ L'.check = L.check ∧ L'.moments = L.moments ∧ L'.link = L.link := by
  have e := q.open
  unfold openOf at e
  rw [h] at e
  obtain ⟨L', h', e'⟩ := Option.map_eq_some_iff.1 e
  have a := ctx_link h'
  rw [q.ctx, ctx_link h] at a
  exact ⟨L', h', congrArg Prod.fst e', congrArg Prod.snd e', (Option.some.inj a).symm⟩

theorem quiet_back {s t : S} (q : Quiet s t) {L' : LinkCtx} (h' : t.link? = some L') :
    ∃ L, s.link? = some L ∧ L'.check = L.check ∧ L'.moments = L.moments ∧ L'.link = L.link := by
  have e := q.open
  unfold openOf at e
  rw [h'] at e
  obtain ⟨L, h, e'⟩ := Option.map_eq_some_iff.1 e.symm
  have a := ctx_link h'
  rw [q.ctx, ctx_link h] at a
  exact ⟨L, h, (congrArg Prod.fst e').symm, (congrArg Prod.snd e').symm, (Option.some.inj a).symm⟩

theorem stays_some {A B : TreeBook} (h : PlacesStay A B) {o : Nat} {jt : Nat × Nat}
    (k : A.place[o]? = some jt) : B.place[o]? = some jt := by
  rw [h o (Array.getElem?_eq_some_iff.1 k).1]
  exact k

/-! ## The stretch, in three pieces -/

/-- **The end**: what the first sending's block left, two Quiet stretches and the reads' sending. -/
theorem stretch_end {t₀ t₁ t₃ v t₄ : S} (Fl : FirstLists t₀ t₁) (Q13 : Quiet t₁ t₃)
    (Rl : ReadsLists t₃ v) (Qv : Quiet v t₄) :
      ∃ L, t₄.link? = some L ∧
        (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∧
        (∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧
          ((j < (L.check.frame.atMoment 0).length ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∨
            ((L.check.frame.atMoment 0).length ≤ j ∧ t₁.roots ≤ jt.1 ∧ jt.1 < t₄.roots))) ∧
        L.check.frame.shape = t₀.check.frame.shape ∧
        L.check.frame.link = t₀.check.frame.link ∧
        L.check.frame.link = L.link ∧ L.moments = 2 := by
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := Fl
  obtain ⟨L3, Lv, a3, av, kb, ow, ps, -, sh, lk, mo, ln⟩ := Rl
  obtain ⟨L1, a1, c1, m1, n1⟩ := quiet_back Q13 a3
  obtain ⟨L4, a4, c4, m4, n4⟩ := quiet_fwd Qv av
  obtain ⟨mm, nn⟩ := F6 L1 a1
  rw [live_open a1] at F1 F2 F3 F4 F5
  have eb3 : t₃.book = t₁.book := Q13.1.2.2.1
  have er3 : t₃.roots = t₁.roots := Q13.1.2.2.2
  have eb4 : t₄.book = v.book := Qv.1.2.2.1
  have er4 : t₄.roots = v.roots := Qv.1.2.2.2
  have esh : L4.check.frame.shape = t₀.check.frame.shape := by rw [c4, sh, c1, F4]
  have elk : L4.check.frame.link = t₀.check.frame.link := by rw [c4, lk, c1, F5]
  have eat : (L4.check.frame.atMoment 0).length = L3.check.frame.own.size := by
    unfold ReqFrame.atMoment
    rw [esh, elk, c1, F3]
    rfl
  rw [eb3] at ps
  refine ⟨L4, a4, fun o ho => ?_, fun j o ho => ?_, esh, elk, ?_, ?_⟩
  · rw [c4, kb, c1] at ho
    obtain ⟨jt, x1, x2, x3⟩ := F1 o ho
    exact ⟨jt, by rw [eb4]; exact stays_some ps x1, x2, x3⟩
  · rw [c4] at ho
    rw [eat]
    rcases ow j o ho with ⟨lt, ho'⟩ | ⟨ge, jt, x1, x2, x3⟩
    · rw [c1] at ho'
      obtain ⟨jt, x1, x2, x3⟩ := F2 j o ho'
      exact ⟨jt, by rw [eb4]; exact stays_some ps x1, Or.inl ⟨lt, x2, x3⟩⟩
    · exact ⟨jt, by rw [eb4]; exact x1, Or.inr ⟨ge, by rw [← er3]; exact x2,
        by rw [er4]; exact x3⟩⟩
  · rw [c4, lk, c1, n4, ln, n1, nn]
  · rw [m4, mo, m1, mm]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The middle, at every layers' and attention link**: from the record behind the link's first
block to the record in front of kind K8's block: Quiet, the reads' sending, Quiet. -/
theorem mid_stretch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, l < 24 → ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₁ t₄ : S) (R₁ R₄ : List Fmt.RoundView)
      (C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 6)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄) →
      ∃ t₃ v, Quiet t₁ t₃ ∧ ReadsLists t₃ v ∧ Quiet v t₄ := by
  intro l h24 p R C t₁ t₄ R₁ R₄ C₁ C₄ f₁ f₄
  have hl : l ≤ 24 := by omega
  have h0 : c.front = [] := chainBy_noFront O.chain
  obtain ⟨Lk, b1, b1', eL, e1, k3, la1⟩ := IM.k3_of hS hR O l (by omega) false
  have ix1 : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  rw [ix1] at e1
  have q1 : Decides Quiet b1 := fun s rs gs t h =>
    (theStated_quiet _ _ _ _ _ _ k3).1 s rs gs t
      ((IM.yes_alone la1 (by intro k; cases k) s t rs gs).1 h).1
  obtain ⟨b2, e2, q2⟩ : ∃ b2, Lk.hear[2]? = some b2 ∧ Decides Quiet b2 := by
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b, y, eL', e, -, la, -⟩ := IM.k4_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      exact ⟨b, e, fun s rs gs t h => (blockAtC_quiet _).1 s rs gs t
        ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1⟩
    · obtain ⟨Lk', b, b', a, eL', e, k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      exact ⟨b, e, fun s rs gs t h => (k5AtN_quiet _ _ _ _ k5).1 s rs gs t
        ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1⟩
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[3]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    split <;> cases (l == 0) <;> rfl
  obtain ⟨Lk3, b3, Xl, pr, pd, reads, digits, eL3, e3, -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) 3 hk (by decide)
  obtain rfl : Lk = Lk3 := Option.some.inj (eL.symm.trans eL3)
  have i1 : c.blocksInOrder[14 * l + 3]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [(IM.flatIx_scope hS hR O hl 1).trans (by omega : 14 * l + 1 + 2 = 14 * l + 3)] at k
  have i2 : c.blocksInOrder[14 * l + 4]? = some b2 := by
    have k := IM.hear_at_flat eL e2
    rwa [(IM.flatIx_scope hS hR O hl 2).trans (by omega : 14 * l + 2 + 2 = 14 * l + 4)] at k
  have i3 : c.blocksInOrder[14 * l + 5]? = some b3 := by
    have k := IM.hear_at_flat eL e3
    rwa [(IM.flatIx_scope hS hR O hl 3).trans (by omega : 14 * l + 3 + 2 = 14 * l + 5)] at k
  have hk3 : 14 * l + 5 ≤ (frontOf c).length := by
    have k := flatIx_le h0 eL e3
    rw [IM.flatIx_scope hS hR O hl 3] at k
    omega
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_back (k := 14 * l + 5) f₄
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 14 * l + 4) f₃
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₁ f₂
  obtain ⟨rs2, gs2, d2⟩ := fold_next i2 f₂ f₃
  obtain ⟨rs3, gs3, d3⟩ := fold_next i3 f₃ f₄
  have hR3 : t₃.roots = t₃.book.trees.size := open_roots O hk3 f₃
  obtain ⟨v, Rl, Qv⟩ : ∃ v, ReadsLists t₃ v ∧ Quiet v t₄ := by
    rcases harm with ⟨-, la⟩ | ⟨-, la⟩
    · exact alone_reads (by intro k; cases k) la d3 hR3
    · exact alone_later (by intro k; cases k) la d3 hR3
  exact ⟨t₃, v, quiet_trans _ _ _ (q1 _ _ _ _ d1) (q2 _ _ _ _ d2), Rl, Qv⟩

/-- **IN THE GOALS' SCOPE, AT A LAYERS' OR AN ATTENTION LINK l, 1 ≤ l < 24: t₀, t₁, t₄: THE RECORDS
OF ONE FOLD FROM THE FIRST RECORD in front of the link's first sending, behind it, and in front of
kind K8's block: a link stands open at t₄; every kept copy lies in a tree of the first sending;
every message of the link's own lies, below the frame's number of messages of moment 0, in a tree of
the first sending, and from that number on in a tree of the reads' sending; the frame's shape and
link are those at t₀; the open link bears its frame's number and has passed two moments.** -/
theorem lists_at_draw {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, 1 ≤ l → l < 24 → ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 6)) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄) →
      ∃ L, t₄.link? = some L ∧
        (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∧
        (∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧
          ((j < (L.check.frame.atMoment 0).length ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∨
            ((L.check.frame.atMoment 0).length ≤ j ∧ t₁.roots ≤ jt.1 ∧ jt.1 < t₄.roots))) ∧
        L.check.frame.shape = t₀.check.frame.shape ∧
        L.check.frame.link = t₀.check.frame.link ∧
        L.check.frame.link = L.link ∧ L.moments = 2 := by
  intro l h1 h24 p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have hl : l ≤ 24 := by omega
  have h0 : c.front = [] := chainBy_noFront O.chain
  obtain ⟨Lk, b0, x, eL, e0, -, la0, hx⟩ := IM.k2_link_of hS hR O l h1 h24
  have i0 : c.blocksInOrder[14 * l + 2]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O hl 0).trans (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
  have hk0 : 14 * l + 2 ≤ (frontOf c).length := by
    have k := flatIx_le h0 eL e0
    rw [IM.flatIx_scope hS hR O hl 0] at k
    omega
  -- "laid": t₀ stands between the links
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr l (by omega)
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * l + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, hBm, -, -⟩ := Johnson.Desc.First.Walk.Law.layFront_ok hlf
  have hB : t₀.atBetween = true := by rw [et]; exact hBm
  have hR0 : t₀.roots = t₀.book.trees.size := open_roots O hk0 f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨t₃, v, Q13, Rl, Qv⟩ := mid_stretch hS hR O l h24 p R C t₁ t₄ R₁ R₄ C₁ C₄ f₁ f₄
  exact stretch_end (first_lists la0 hx d0 hB hR0) Q13 Rl Qv

end

#print axioms two_of_send
#print axioms frameBlock_live
#print axioms first_lists
#print axioms commit_lists
#print axioms reads_lists
#print axioms open_roots
#print axioms stretch_end
#print axioms mid_stretch
#print axioms lists_at_draw

end Meaning.K2
