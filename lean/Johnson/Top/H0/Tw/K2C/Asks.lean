-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Asks.lean: the kind «the code switch»: WHAT A YES ASKS, BOTH WAYS, OF THE
FUNCTIONS THAT K2C/Closed.lean KEEPS WHOLE. NO BLOCK IMPORTS THIS FILE.
K2C/Closed.lean gives the closed form of a yes as equations, and in these equations firstFront,
firstBehind, finishFront, finishBehind and openOne stand as names; of the quiet steps K2C/Reply.lean
says only what they leave. So a test INSIDE one of them could be struck from the text and every
statement there would stay true. Here each of them has one statement that names every one of its
tests, «if and only if»:
  firstFront_iff      [F1] [F0] [F2] [F3], the new group [F4-F6: kept as the plain ground's adapter
      newGroupG], and what is handed on
  firstBehind_iff     [F7] [F8] [F9], the own messages' joins [G17-G22: joinG], and the frame
      behind, field by field
  finishFront_iff     [F10] [F3], the new group, and what is handed on
  finishBehind_iff    [F11]
  openOne_iff         [G8] [G9] [G10] [G11] [G12], and the book, the columns left and the columns
      taken behind
  finishFrontQ_iff    [B0] [W8] [F3], finishFront, the record's own entering, [B3]
  finishBehindQ_iff   [B2] [F11]
  headFrontQ_iff      [B0] [W0], firstFront, the record's own entering, [B3]
  headOpenQ_iff       [B2] [Q0] [Q1], firstBehind, the walk's front [W1] [W2], the reply's one seat
      [Y0] [Y1], [C1] [C0], the record's own opening, and the record behind, field by field
  headPlanOk_iff      [P1] [P2] [P3]
  planOk_iff          the kind's own test on the plan, its four clauses; increasing_iff: what
      «increasing» means
WHAT STAYS A NAME: the plain ground's adapters (newGroupG, joinG); the walk's firstDue | finishDue |
front [W1] [W2] | firstKept; the record's own S.atBetween | enterFin? | enterHead? | openHead? |
covered [C1]; sizedOk [C0] and handedOk [P1] (what these two check: K2C/Yard.lean's sizedOk_iff |
handedOk_iff); and Own.colsStand (what it means: Johnson/Desc/Own/ShapesMean.lean's colsStand_iff).
No soundness is claimed: this says what the text asks, not that it asks enough.

-/
import Johnson.Top.H0.Tw.K2C.Reply

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)

/-- What firstFront's yes asks and hands on. -/
structure FrontAsks (S : Statement) (f : ReqFrame) (x : Front) (L : ReqLink) (G : ReqGroup) (S' :
    Statement) (g : Nat) : Prop where
  /-- [F1] a link's first message is due -/
  first : f.next = .first
  /-- [F0] the link is not link 0 -/
  later : f.link ≠ 0
  /-- [F2] the shape has the link -/
  link : f.shape.link[f.link]? = some L
  /-- [F3] the groups' list has the link's -/
  group : f.groups[f.link]? = some G
  /-- [F4-F6] the new group is opened -/
  opened : newGroupG S f.shape.code f.shape.maskCode = .ok (S', g)
  out : x = ⟨S', { f with group := g, moment := 1, own := #[] }, f.atMoment 0,
    ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})], G.target, L.plain⟩

theorem firstFront_iff (S : Statement) (f : ReqFrame) (x : Front) :
    firstFront S f = .ok x ↔ ∃ L G S' g, FrontAsks S f x L G S' g := by
  constructor
  · intro h
    unfold firstFront at h
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        split at h
        · rename_i L G hL hG
          dsimp only at h
          split at h
          · cases h
          · rename_i S' g hn
            cases h
            exact ⟨L, G, S', g, by simpa using h1, by simpa using h2, hL, hG, hn, rfl⟩
        · cases h
        · cases h
  · rintro ⟨L, G, S', g, a⟩
    unfold firstFront
    simp [a.first, a.later, a.link, a.group, a.opened, a.out]

/-- What firstBehind's yes asks and hands on. -/
structure BehindAsks (S : Statement) (x : Front) (s : Switched) (plain : List E) (S' : Statement) (f
    : ReqFrame) (mine : Array Nat) (mask : Nat) : Prop where
  /-- [F7] as many numbers came back as there were announcements -/
  numbers : s.others.size = x.others.size
  /-- [F8] the fresh mask's number is among them -/
  theMask : s.others[x.own.length]? = some mask
  theOwn : mine = s.others.extract 0 x.own.length
  /-- [F9] as many own messages as numbers -/
  own : x.own.length = mine.size
  /-- [G17-G22] each own message joins the group, kept iff it has a life -/
  joins : (zipT x.own mine.toList).foldlM (fun S y => joinG S x.f.group y.2 (decide (0 < y.1.life)))
      S = .ok S'
  frame : f = { x.f with
    plain := plain, keptBefore := s.kept, mask := some mask,
    atStart := x.f.atStart ++ s.others.extract (x.own.length + 1) s.others.size,
    own := x.f.own ++ mine, next := .laterOrClose }

theorem firstBehind_iff (S : Statement) (x : Front) (s : Switched) (plain : List E) (S' : Statement)
    (f : ReqFrame) (mine : Array Nat) :
    firstBehind S x s plain = .ok (S', f, mine) ↔ ∃ mask, BehindAsks S x s plain S' f mine mask :=
        by
  constructor
  · intro h
    unfold firstBehind at h
    dsimp only at h
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i mask hm
        split at h
        · cases h
        · rename_i h2
          split at h
          · cases h
          · rename_i S'' hj
            cases h
            exact ⟨mask, by simpa using h1, hm, rfl, by simpa using h2, hj, rfl⟩
  · rintro ⟨mask, a⟩
    have hm := a.theOwn
    subst hm
    unfold firstBehind
    dsimp only
    rw [if_neg (fun h => (bne_iff_ne.1 h) a.numbers), a.theMask]
    dsimp only
    rw [if_neg (fun h => (bne_iff_ne.1 h) a.own), a.joins, a.frame]

/-- What finishFront's yes asks and hands on. -/
structure FinishAsks (S : Statement) (f : ReqFrame) (x : Front) (G : ReqGroup) (S' : Statement) (g :
    Nat) : Prop where
  /-- [F10] a first message is due … -/
  first : f.next = .first
  /-- [F10] … and every link is behind -/
  last : f.link = f.shape.link.length
  /-- [F3] the groups' list has the last test's -/
  group : f.groups[f.link]? = some G
  /-- [F4-F6] the new group is opened -/
  opened : newGroupG S f.shape.code f.shape.maskCode = .ok (S', g)
  out : x = ⟨S', { f with group := g, moment := 1, own := #[] }, [], #[foldMaskNotice (f.foldShape
      f.link {})], G.target, 0⟩

theorem finishFront_iff (S : Statement) (f : ReqFrame) (x : Front) :
    finishFront S f = .ok x ↔ ∃ G S' g, FinishAsks S f x G S' g := by
  constructor
  · intro h
    unfold finishFront at h
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i G hG
        split at h
        · cases h
        · rename_i S' g hn
          cases h
          have h1' : f.next = .first ∧ f.link = f.shape.link.length := by simpa using h1
          exact ⟨G, S', g, h1'.1, h1'.2, hG, hn, rfl⟩
  · rintro ⟨G, S', g, a⟩
    unfold finishFront
    have hl := a.last
    simp [a.first, ← hl, a.group, a.opened, a.out]

/-- [F11] -/
theorem finishBehind_iff (s : Switched) (m : Nat) : finishBehind s = .ok m ↔ s.others[0]? = some m
    := by
  unfold finishBehind
  split
  · rename_i m' h
    rw [h]
    constructor
    · intro k; cases k; rfl
    · intro k; cases k; rfl
  · rename_i h
    rw [h]
    constructor
    · intro k; cases k
    · intro k; cases k

/-- The groups of the sampled messages that share the tree's leaves (openOne's own «groups»). -/
def leafGroups (S : Statement) (tree : Tree) : List (List Nat) :=
  tree.parts.toList.filterMap fun o =>
    (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups

/-- [G9] as one test: the sampled parts belong to the same groups; in a tree with a mask: to one
group at most. -/
def leafOk (S : Statement) (tree : Tree) : Bool :=
  match leafGroups S tree with
  | [] => true
  | a :: l => l.all (· == a) && (!tree.oneList || decide (a.length ≤ 1))

/-- openOne's text, with [G9] under its name and the «let»s laid in. -/
theorem openOne_eq (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s : TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :
    openOne S firstTree pos B0 t s =
      match s.1.trees[t]?, B0.trees[t]? with
      | some tree, some tree0 =>
        if !leafOk S tree then .error "G9: what shares a leaf"
        else if !(!tree.oneList || tree.lists == 0) then .error
            "G10: a tree with a mask is opened twice"
        else if !decide (tree0.shape.logN ≤ pos.logN) then .error
            "G11: the tree is longer than the range"
        else if (s.2.1.take (Blk.ownList tree0 pos).size).length == (Blk.ownList tree0 pos).size &&
            VerifiableInference.Desc.Own.colsStand (tree0.number - firstTree) (tree0.shape.mainWidth
                + tree0.shape.maskWidth)
              (s.2.1.take (Blk.ownList tree0 pos).size) (Blk.ownList tree0 pos).toList then
          .ok ({ s.1 with trees := s.1.trees.modify t fun x => { x with lists := x.lists + 1 } },
            s.2.1.drop (Blk.ownList tree0 pos).size,
            s.2.2.push (t, Blk.ownList tree0 pos, ((s.2.1.take (Blk.ownList tree0 pos).size).map fun
                y => y.2.2.toArray).toArray))
        else .error "G12: the opened columns do not fit"
      | _, _ => .error "G8: the tree is not in the book" := rfl

/-- What openOne's yes asks and hands on. s: the book so far, the columns left, the columns taken so
far. -/
structure OpenAsks (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s o : TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) (tree tree0 : Tree) :
        Prop where
  /-- [G8] the tree is in the book as it stands … -/
  here : s.1.trees[t]? = some tree
  /-- [G8] … and in the book in front of the reading -/
  there : B0.trees[t]? = some tree0
  /-- [G9] the sampled parts belong to the same groups; in a tree with a mask: to one group at most
  -/
  leaf : leafOk S tree = true
  /-- [G10] a tree that holds a message without a sample has not been opened before -/
  once : tree.oneList = true → tree.lists = 0
  /-- [G11] the tree is not longer than the list's range -/
  range : tree0.shape.logN ≤ pos.logN
  /-- [G12] the next columns are as many as the tree's own list … -/
  count : (s.2.1.take (Blk.ownList tree0 pos).size).length = (Blk.ownList tree0 pos).size
  /-- [G12] … each with the tree's key, at the list's position, of the tree's width -/
  stand : VerifiableInference.Desc.Own.colsStand (tree0.number - firstTree) (tree0.shape.mainWidth +
      tree0.shape.maskWidth)
    (s.2.1.take (Blk.ownList tree0 pos).size) (Blk.ownList tree0 pos).toList = true
  out : o = ({ s.1 with trees := s.1.trees.modify t fun x => { x with lists := x.lists + 1 } },
    s.2.1.drop (Blk.ownList tree0 pos).size,
    s.2.2.push (t, Blk.ownList tree0 pos, ((s.2.1.take (Blk.ownList tree0 pos).size).map fun y =>
        y.2.2.toArray).toArray))

theorem openOne_iff (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s o : TreeBook × List Col × Array (Nat × Array Nat × Array (Array F))) :
    openOne S firstTree pos B0 t s = .ok o ↔ ∃ tree tree0, OpenAsks S firstTree pos B0 t s o tree
        tree0 := by
  rw [openOne_eq]
  constructor
  · intro h
    split at h
    · rename_i tree tree0 h1 h2
      split at h
      · cases h
      · rename_i h9
        split at h
        · cases h
        · rename_i h10
          split at h
          · cases h
          · rename_i h11
            split at h
            · rename_i h12
              cases h
              have h12' := Bool.and_eq_true_iff.1 h12
              exact ⟨tree, tree0, h1, h2, by simpa using h9, by simpa using h10, by simpa using h11,
                beq_iff_eq.1 h12'.1, h12'.2, rfl⟩
            · cases h
    · cases h
  · rintro ⟨tree, tree0, a⟩
    have h10 : (!tree.oneList || tree.lists == 0) = true := by
      cases h : tree.oneList with
      | false => simp
      | true => simp [a.once h]
    have h11 : decide (tree0.shape.logN ≤ pos.logN) = true := by simpa using a.range
    have h12 : ((s.2.1.take (Blk.ownList tree0 pos).size).length == (Blk.ownList tree0 pos).size) =
        true := beq_iff_eq.2 a.count
    rw [a.here, a.there]
    simp only [a.leaf, h10, h11, h12, a.stand, a.out, Bool.not_true, Bool.false_eq_true, if_false,
        Bool.and_self, if_true]

end Tw.K2

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.Walk (firstDue finishDue front firstKept weightsAtZero emptySlots)

/-- "F.0.front": what its yes asks and lays. -/
structure FinishFrontAsks (s s' : S) (G : ReqGroup) (x : _root_.Tw.K2.Front) (s₁ : S) (a : FinOwn) :
    Prop where
  /-- [B0] the record stands between the links -/
  between : s.atBetween = true
  /-- [W8] the finish is due -/
  due : finishDue s.check = true
  /-- [F3] the groups' list has the last test's -/
  group : s.check.frame.groups[s.check.frame.link]? = some G
  /-- [F10] [F3] [F4-F6] -/
  front : _root_.Tw.K2.finishFront s.st s.check.frame = .ok x
  /-- the record enters the finish, by its own refusing form -/
  enters : s.enterFin? = .ok s₁
  /-- [B3] -/
  entered : s₁.here = .fin a
  out : s' = { s₁ with st := x.st, here := .fin { a with G := some G, fr := x.f } }

theorem finishFrontQ_iff (s s' : S) : finishFrontQ s = .ok s' ↔ ∃ G x s₁ a, FinishFrontAsks s s' G x
    s₁ a := by
  constructor
  · intro h
    unfold finishFrontQ at h
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        split at h
        · rename_i G x hG hx
          obtain ⟨s₁, he, h⟩ := bindOk h
          split at h
          · rename_i a ha
            cases h
            exact ⟨G, x, s₁, a, by simpa using h1, by simpa using h2, hG, hx, he, ha, rfl⟩
          · cases h
        · cases h
        · cases h
  · rintro ⟨G, x, s₁, a, k⟩
    unfold finishFrontQ
    simp only [k.between, k.due, k.group, k.front]
    simp [Except.bind, k.enters, k.entered, k.out]

/-- "F.0.quiet": [B2] [F11]. -/
theorem finishBehindQ_iff (s s' : S) :
    finishBehindQ s = .ok s' ↔ ∃ a m, s.here = .fin a ∧ a.sw.others[0]? = some m ∧ s' = { s with
        here := .fin { a with mask := some m } } := by
  constructor
  · intro h
    unfold finishBehindQ at h
    split at h
    · rename_i a ha
      cases hm : _root_.Tw.K2.finishBehind a.sw with
      | error e => simp [hm, Except.map] at h
      | ok m =>
        simp [hm, Except.map] at h
        exact ⟨a, m, ha, (_root_.Tw.K2.finishBehind_iff _ _).1 hm, h.symm⟩
    · cases h
  · rintro ⟨a, m, ha, hm, rfl⟩
    unfold finishBehindQ
    simp [ha, (_root_.Tw.K2.finishBehind_iff _ _).2 hm, Except.map]

/-- "H.0.front": what its yes asks and lays. -/
structure HeadFrontAsks (tl : HTailF2) (s s' : S) (x : _root_.Tw.K2.Front) (s₁ : S) (a : HeadOwn) :
    Prop where
  /-- [B0] the record stands between the links -/
  between : s.atBetween = true
  /-- [W0] a link's first call is due -/
  due : firstDue s.check = true
  /-- [F1] [F0] [F2] [F3] [F4-F6] -/
  front : _root_.Tw.K2.firstFront s.st s.check.frame = .ok x
  /-- the record enters the head's link, by its own refusing form -/
  enters : s.enterHead? tl = .ok s₁
  /-- [B3] -/
  entered : s₁.here = .head a
  out : s' = { s₁ with st := x.st, here := .head { a with fr := x.f } }

theorem headFrontQ_iff (tl : HTailF2) (s s' : S) : headFrontQ tl s = .ok s' ↔ ∃ x s₁ a,
    HeadFrontAsks tl s s' x s₁ a := by
  constructor
  · intro h
    unfold headFrontQ at h
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        obtain ⟨x, hx, h⟩ := bindOk h
        obtain ⟨s₁, he, h⟩ := bindOk h
        split at h
        · rename_i a ha
          cases h
          exact ⟨x, s₁, a, by simpa using h1, by simpa using h2, hx, he, ha, rfl⟩
        · cases h
  · rintro ⟨x, s₁, a, k⟩
    unfold headFrontQ
    simp [Except.bind, k.between, k.due, k.front, k.enters, k.entered, k.out]

/-- "H.1.quiet": what its yes asks and lays. -/
structure HeadOpenAsks (P : HeadPar) (s s' : S) (a : HeadOwn) (st : Statement) (f : ReqFrame) (mine
    : Array Nat) (L : LinkCtx)
    (out : Proof.LinksResult) (y : E) (cov : Head.Covered) (s₁ : S) (b : HeadOwn) : Prop where
  /-- [B2] the record stands in the head's link -/
  here : s.here = .head a
  /-- [Q0] the link is not opened yet -/
  fresh : a.opened = false
  /-- [Q1] it is not link 0 -/
  later : P.l ≠ 0
  /-- [F7] [F8] [F9] and the own messages' joins (firstBehind_iff) -/
  behind : _root_.Tw.K2.firstBehind s.st
    ⟨s.st, a.fr, s.check.frame.atMoment 0,
      ReqFrame.notices (s.check.frame.atMoment 0) ++ #[foldMaskNotice (s.check.frame.foldShape
          s.check.frame.link {})], default, 0⟩
    { (default : Switched) with kept := a.kept, others := a.ids } s.out.reply.toList = .ok (st, f,
        mine)
  /-- [W1] [W2]: the walk's own -/
  front : front P.X P.l (firstKept s.check f mine) s.out = .ok (L, out)
  /-- [Y0] a reply lies in the seat -/
  seat : s.out.reply = some y
  /-- [Y1] it is an entry of the vocabulary -/
  token : y.c1 = 0 ∧ y.c2 = 0 ∧ y.c0.toNat < P.V
  /-- [C1] the covered positions can be made -/
  covered : ({ s with out := out } : S).covered P.T P.V = .ok cov
  /-- [C0] their arrays have the length T (what it checks: K2C/Yard.lean's sizedOk_iff) -/
  sized : sizedOk cov P.T = true
  /-- the record opens the head's link, by its own refusing form -/
  opens : s.openHead? = .ok s₁
  /-- [B2] -/
  opened : s₁.here = .head b
  out' : s' = { s₁ with
    st := st, check := firstKept s.check f mine, out := out
    here := .head { b with
      L := L, F := emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } }

theorem headOpenQ_iff (P : HeadPar) (s s' : S) :
    headOpenQ P s = .ok s' ↔ ∃ a st f mine L out y cov s₁ b, HeadOpenAsks P s s' a st f mine L out y
        cov s₁ b := by
  constructor
  · intro h
    unfold headOpenQ at h
    split at h
    · rename_i a ha
      split at h
      · cases h
      · rename_i h0
        split at h
        · cases h
        · rename_i h1
          dsimp only at h
          obtain ⟨⟨st, f, mine⟩, hb, h⟩ := bindOk h
          dsimp only at h
          obtain ⟨⟨L, out⟩, hf, h⟩ := bindOk h
          dsimp only at h
          split at h
          · rename_i y hy
            split at h
            · cases h
            · rename_i hY
              split at h
              · cases h
              · rename_i cov hc
                split at h
                · cases h
                · rename_i hs
                  obtain ⟨s₁, h₁, h⟩ := bindOk h
                  split at h
                  · rename_i b hb'
                    cases h
                    simp at hY
                    exact ⟨a, st, f, mine, L, out, y, cov, s₁, b, ha, by simpa using h0, by simpa
                        using h1, hb, hf, hy,
                      ⟨hY.1.1, hY.1.2, hY.2⟩, hc, by simpa using hs, h₁, hb', rfl⟩
                  · cases h
          · cases h
    · cases h
  · rintro ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩
    unfold headOpenQ
    have hY : (y.c1 == 0 && y.c2 == 0 && Decidable.decide (y.c0.toNat < P.V)) = true := by
      simp [k.token.1, k.token.2.1, k.token.2.2]
    simp only [k.here, k.fresh, Bool.false_eq_true, if_false]
    rw [if_neg (by simpa using k.later)]
    have hc := k.covered
    simp only [k.here] at hc
    simp only [k.behind, Except.bind, k.front]
    simp only [k.seat, hY, Bool.not_true, Bool.false_eq_true, if_false, k.opens, k.opened, k.out']
    simp only [hc, k.sized, Bool.not_true, Bool.false_eq_true, if_false]

/-- What the kind's test on the plan means by «increasing»: each number of the list is below the
next. -/
theorem increasing_iff : ∀ l : List Nat, increasing l = true ↔ ∀ (i : Nat) (h : i + 1 < l.length),
    l[i]'(by omega) < l[i + 1]
  | [] => by simp [increasing]
  | [_] => by simp [increasing]
  | a :: b :: l => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq, increasing_iff (b :: l)]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ j => simpa using h j (by simpa using hi)
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
      simpa using h (i + 1) (by simpa using hi)

/-- The kind's test on the plan, as plain facts. -/
theorem planOk_iff (p : P2) : (codeSwitchKind p : Block S Unit).planOk = true ↔
    0 < p.positions ∧ p.sent.length = p.roots ∧ (∀ (i : Nat) (h : i + 1 < (p.read.map
        (·.1)).length), (p.read.map (·.1))[i]'(by omega) < (p.read.map (·.1))[i + 1]) ∧ p.logN ≤ 32
        := by
  rw [← increasing_iff]
  simp [codeSwitchKind, and_assoc]

/-- [P1] [P2] [P3]: the tests on the plan alone at "H.1.quiet", as plain facts (what [P1] checks:
K2C/Yard.lean's handedOk_iff). -/
theorem headPlanOk_iff (P : HeadPar) :
    headPlanOk P = true ↔ handedOk P.hp P.X.Tp P.X.Fp = true ∧ (P.O.tl.ix.TX.isEmpty = false ∧
        P.O.tl.kTX.back? = some P.kxb) ∧
      (P.hp.tl.ix.U.getD 2 none).isSome = true := by
  simp [headPlanOk, headPlanTests, and_assoc]

end VerifiableInference.Desc.First.K2

#print axioms Tw.K2.openOne_iff
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_iff
#print axioms VerifiableInference.Desc.First.K2.finishBehindQ_iff
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_iff
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_iff
#print axioms VerifiableInference.Desc.First.K2.headPlanOk_iff
#print axioms VerifiableInference.Desc.First.K2.increasing_iff
#print axioms VerifiableInference.Desc.First.K2.planOk_iff
#print axioms Tw.K2.firstFront_iff
#print axioms Tw.K2.firstBehind_iff
#print axioms Tw.K2.finishFront_iff
#print axioms Tw.K2.finishBehind_iff
