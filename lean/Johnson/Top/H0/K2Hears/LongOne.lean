-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/LongOne.lean: the code switch: WHAT THE TEXT HEARS AT A DRAWN
POSITION IS A FUNCTION OF THE PLACE's NUMBERS, THE RECORD IN FRONT WITH ITS FRONT, THE ORACLES AND
THAT POSITION. Third part: the join.

LongLocal.lean: the stretch of a position in the array of symbols is what rowsAt lays at that
position alone. LongCols.lean: if every column shown is orc's, each message's column at a listed
position is colOne, off orc. Here the two are joined at a yes of the kind's decision, and what they
read of the statement and the book BEHIND the sending is brought back to the front:
  loop_book, sendP_bookIs, sendOpen_book, sent_book  the book behind the sending that K2 runs is
                bookAt: what the plain ground's recvP makes of the front's statement, the record's
                book and number of roots, and the notices: nothing of the two rounds
  sent_shapes   the statement behind the sending has the codes and shapes of skelOf of the front
                (FrameOfFront.lean)
  columnOf_congr, colOne_congr  colOne reads of the statement a message's shape alone
  openedOne     each message's column at ONE position, as an array that rowsAt can read at number 0
  longFront     THE CARRIED ROWS' SYMBOLS AT THE POSITION q, off orc: a function of the place's
                numbers, the record in front, its front, orc and q
  heard_is_front  at a yes (Whole.lean's AtYes), if every column shown is orc's: the stretch of the
                listed position number k in the array that was heard is longFront at that position
No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.LongLocal
import Johnson.Top.H0.K2Hears.LongCols
import Johnson.Top.H0.K2Hands.FrameOfFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.Ground (recvP admitP)
open VerifiableInference.Desc.Own (rowsAt rowsAt_congr symbols_at)
open _root_.Tw.K2 (switchNotices sendByL8)

theorem loop_book {L : Type} (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L) (left : List E),
      sampleLoop groundG p codes seeds l ys d = some (d', left) → d'.book = d.book
  | [], ys, d, d', left, h => by
    cases h
    rfl
  | (o, s) :: l, ys, d, d', left, h => by
    unfold sampleLoop at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d1 h1
        have e : d1.book = d.book := by
          have h1' : admitP d o rows = some d1 := h1
          unfold admitP at h1'
          split at h1'
          · obtain ⟨x, -, h1'⟩ := optBind h1'
            obtain ⟨places, -, h1'⟩ := optBind h1'
            cases h1'
            rfl
          · cases h1'
        exact (loop_book p codes seeds l ys' d1 d' left h).trans e

/-- The book behind a sending: of the statement, the book and the number of roots in front, and the
notices. -/
def bookAt (ft : Nat) (S : Statement) (B : TreeBook) (roots : Nat) (notices : Array OracleNotice) :
    Option TreeBook :=
  (recvP ft (⟨S, B, roots, [], ()⟩ : DState Unit) notices).map (·.2.book)

theorem sendP_bookIs {p : GPar} {own : Bool} {d : DState Unit} {sent : Array OracleNotice}
    {r₁ r₂ : Fmt.RoundView} {x : Array Nat × List E × List E × Nat × DState Unit}
    (h : sendP groundG p own d sent r₁ r₂ = some x) :
    (recvP p.firstTree d sent).map (·.2.book) = some x.2.2.2.2.book := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := optBind h
  dsimp only at h
  obtain ⟨shapes, -, h⟩ := optBind h
  obtain ⟨seeds, -, h⟩ := optBind h
  obtain ⟨an, -, h⟩ := optBind h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBind h
    dsimp only at h
    split at h
    · cases h
      have hr : recvP p.firstTree d sent = some (ids, d₁) := h1
      rw [hr]
      exact congrArg some (loop_book p _ seeds _ an d₁ d₂ left h2).symm
    · cases h
  · cases h

theorem sendOpen_book {p : GPar} {owed : Option Nat} {sent : Array OracleNotice} {e₁ : Fmt.Entry}
    {d d' : DState Unit} {r₁ r₂ : Fmt.RoundView} {ids : Array Nat} {took : Nat}
    (h : VerifiableInference.Desc.First.Send.sendOpen groundG p owed sent e₁ d r₁ r₂ =
      some (ids, took, d')) : (recvP p.firstTree d sent).map (·.2.book) = some d'.book := by
  unfold VerifiableInference.Desc.First.Send.sendOpen at h
  split at h
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact sendP_bookIs hx
  · cases h

/-- **The book behind the sending that K2 runs.** -/
theorem sent_book {P : _root_.Tw.K2.Par9} {S : Statement} {B : TreeBook} {roots : Nat}
    {settled : Bool} {notices : Array OracleNotice} {rS rL : Fmt.RoundView} {y : _root_.Tw.K2.Sent}
    (h : sendByL8 P S B roots settled notices rS rL = .ok y) :
    bookAt P.firstTree S B roots notices = some y.book := by
  unfold sendByL8 at h
  split at h
  · rename_i ids took d hd
    cases h
    exact sendOpen_book hd
  · cases h

theorem sent_shapes {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    (h : SentOk x.st (switchNotices x.T x.others) y.ids y.st) : SameShapes (skelOf x) y.st := by
  refine ⟨h.codes, fun o => ?_⟩
  by_cases ho : o < x.st.oracles.size
  · rw [h.old o ho]
    unfold skelOf
    rw [OnBytes.Slice.stSent_old _ _ o ho]
  · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
    rw [h.shape i]
    unfold skelOf
    rw [OnBytes.Slice.stSent_new, Option.map_map]
    rfl

theorem columnOf_congr (x x' : OnBytes.Oracle) (h : x'.shape = x.shape) (a b : Nat) (c : Array F) :
    Blk.columnOf x' a b c = Blk.columnOf x a b c := by
  unfold Blk.columnOf
  rw [h]

theorem colOne_congr {S S' : Statement} (h : SameShapes S S') (B : TreeBook) (ft logN : Nat)
    (orc : Nat → Nat → List UInt64) (o : Nat) (p : Nat × Nat) (q : Nat) :
    colOne S' B ft logN orc o p q = colOne S B ft logN orc o p q := by
  have e := h.shape o
  unfold colOne
  cases B.trees[p.1]? with
  | none => rfl
  | some tree =>
    cases h1 : S'.oracles[o]? <;> cases h2 : S.oracles[o]? <;> simp [h1, h2] at e ⊢
    exact columnOf_congr _ _ e _ _ _

/-- Each message's column at one position. -/
def openedOne (S : Statement) (B : TreeBook) (ft logN : Nat) (orc : Nat → Nat → List UInt64)
    (idp : Array (Nat × Nat × Nat)) (q : Nat) : Array (Array Column) :=
  idp.map fun y => ((colOne S B ft logN orc y.1 y.2 q).map fun c => #[c]).getD #[]

/-- **The carried rows' symbols at the position q, off the oracles.** -/
def longFront (p : P2) (s : S) (x : _root_.Tw.K2.Front) (orc : Nat → Nat → List UInt64) (q : Nat) :
    Option (Array E) :=
  (bookAt (par9 p).firstTree x.st s.book s.roots (switchNotices x.T x.others)).bind fun B =>
    ((singleRowsOracles x.f.rows).mapM fun o => B.place[o]?).bind fun places =>
      rowsAt x.f.rows (openedOne (skelOf x) B (par9 p).firstTree p.logN orc
        ((singleRowsOracles x.f.rows).zip places) q) #[] 0

/-- **What was heard at a listed position is longFront there.** -/
theorem heard_is_front {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) {orc : Nat → Nat → List UInt64}
    (hc : ColsOf orc (flat p gs)) (k : Nat)
    (hk : k < (Positions.ofDraws p.logN r₂.drawn.poss).all.size) :
    ∃ seg, longFront p s x orc ((Positions.ofDraws p.logN r₂.drawn.poss).all.getD k 0) = some seg ∧
      ∀ j, j < x.f.rows.rows → Y[k * x.f.rows.rows + j]? = seg[j]? := by
  obtain ⟨B, left, hr⟩ := A.read
  obtain ⟨places, cols, opened, R⟩ := readOld_inv hr
  have hm : x.f.rows.masks = 2 := (Johnson.Top.H.check_facts A.check).1
  have hg := open_good _ _ _ R.hOpen hc (by intro m hm'; simp at hm')
  obtain ⟨seg, hseg, hY⟩ := symbols_at x.f.rows hm opened _ Y R.hLayout k hk
  refine ⟨seg, ?_, hY⟩
  unfold longFront
  rw [sent_book A.sentBy]
  have hp : (singleRowsOracles x.f.rows).mapM (fun o => y.book.place[o]?) = some places := R.hPlaces
  simp only [Option.bind_some, hp]
  rw [← hseg]
  refine rowsAt_congr x.f.rows opened _ #[] k 0 fun w => ?_
  obtain ⟨z1, z2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ R.hSymbols
  unfold openedOne
  by_cases hw : w < ((singleRowsOracles x.f.rows).zip places).size
  · have h1 := z2 w hw
    have hw' : w < opened.size := by rw [z1]; exact hw
    rw [Array.getElem?_eq_getElem hw'] at h1
    have h2 : opened[w][k]? = colOne y.st y.book (par9 p).firstTree p.logN orc
        ((singleRowsOracles x.f.rows).zip places)[w].1
        ((singleRowsOracles x.f.rows).zip places)[w].2
        ((Positions.ofDraws p.logN r₂.drawn.poss).all.getD k 0) := symbolsAt_one h1 hg k hk
    rw [Array.getElem?_eq_getElem hw', Array.getElem?_map, Array.getElem?_eq_getElem hw]
    simp only [Option.map_some, Option.bind_some]
    rw [h2, colOne_congr (sent_shapes A.sent)]
    cases colOne (skelOf x) y.book (par9 p).firstTree p.logN orc
      ((singleRowsOracles x.f.rows).zip places)[w].1 ((singleRowsOracles x.f.rows).zip places)[w].2
      ((Positions.ofDraws p.logN r₂.drawn.poss).all.getD k 0) <;> rfl
  · have ha : opened[w]? = none :=
      Array.getElem?_eq_none (by rw [z1]; exact Nat.le_of_not_lt hw)
    rw [ha, Array.getElem?_eq_none (by rw [Array.size_map]; exact Nat.le_of_not_lt hw)]
    rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sent_book
#print axioms VerifiableInference.Desc.First.K2.heard_is_front
