-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptSeatOf.lean: the code switch: SeatWord.lean's
KeptSeat (what ties a kept message of the switch's front to a seat of the table of joints: twelve
clauses), FROM TWO NOTIONS AT THE SEAT, THREE TESTS ON THE VERIFIER's STATE, AND FACTS ON
THE PLAN's LIST.
  BookSeat     the book's side of KeptSeat: eight of its clauses, at what the description tells of
               the seat's tree
SeatFitAt, seatFitAt_of  Sound.SeatFits AT ONE MEMBER. SeatFits speaks of
               EVERY member of the list: the law's «seat» has a meant
               value at the kept members alone, so that premise is bound too widely and most likely
               cannot be paid at the closed terms. The proofs spend it at the one member
  keptSeat_of  KeptSeat from SeatFitAt (a test on the plan alone) and ShownAt (every leaf is shown:
               the table's promise), and BookSeat: these two give the other four clauses: the
               description tells the tree and the tenant · every leaf's column has the tree's words
               · the tenant's main words are the shape's rows, one word or three a row
  bookSeat_of_tests  BookSeat from the three tests atFirstBook | atFirstSeats | atFirstFits
               (Johnson/Desc/K12/Door/DoorBools.lean: the fields bookInOrder | seatsCarried |
               bookFits of FoldFacts conclude just these at a reached state). The book
               behind the switch's sending keeps the old places and trees: recvP_keeps
               (Johnson/Desc/K12/Law/OutK.lean)
  book_of_there  where the front reads something at a position, that book is there
  keptSeat_of_fold  THE STATEMENT: the three in a row
WHAT IS STILL MISSING BESIDE FoldFacts' FIELDS, PLAINLY: SEVEN THINGS (eight hypotheses of
keptSeat_of_fold; beside them stand SeatFits, ShownAt, «the member has a main row» and «the front
reads something at some position»). (1) hold: the message's number is below the book's places: NO
FIELD SAYS THAT THE BOOK HAS A PLACE FOR EVERY MESSAGE OF THE STATEMENT. (2) hL: the plan's list has
(a tree, THE SEAT's TENANT) at the number old: so old must be THE PLAN's number of that kept member.
(3) hLs: the plan's list has that tree's shape. (4) hxo, hsh: the front's statement has the typed
shape at old (FoldFacts' msgShapes with a fact on its list, or storedB). (5) hlog: the listed
tree is as long as the main code's positions. (6) horc: the oracles' reading at the key tp is
Strs.col at THE SEAT's TREE: so the seat's tree must be the first of the frame's list with that key.
(7) hskip: the listed tree's shape's skip in front of the tenant is the description's. OF THESE (2),
(3), (5), (7) ARE FACTS ON PUBLIC LISTS ALONE: closed tests on the plan.
ALSO: the three tests are asked AT THE STATE t THAT THE WAY IN LETS IN; FoldFacts speaks of the
state at the border: at a place whose way in is not the identity one step lies between.
LIMITS. An assembly. None of the premises is shown at a real value. pinKept IS NOT PAID. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.SeatWord
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Law.OutK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Strs FileDescription wordOf)
open VerifiableInference.Desc.Sound (SeatFits ShownAt)
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

/-- **The book's side of KeptSeat**, at what the description tells of the seat's tree. -/
def BookSeat (p : K2.P2) (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ) (sh : OracleShape) (seat : ℕ × ℕ)
    (leaves : ℕ) (o : VerifiableInference.Desc.Oracle) : Prop :=
  ∃ (B : TreeBook) (tp : ℕ) (tr : Tree) (xo : OnBytes.Oracle),
    K2.bookAt (K2.par9 p).firstTree fx.st t.book t.roots (switchNotices fx.T fx.others) = some B ∧
    B.place[old]? = some (tp, seat.2) ∧ B.trees[tp]? = some tr ∧
    (K2.skelOf fx).oracles[old]? = some xo ∧ xo.shape = sh ∧
    (∀ x, x < leaves → (if tr.shape.logN == p.logN then x else x % 2 ^ tr.shape.logN) = x) ∧
    (∀ x, x < leaves → orc (tr.number - (K2.par9 p).firstTree) x = Y.col seat.1 x) ∧
    (tr.shape.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = o.mainSkip seat.2

/-- **Sound.SeatFits, at one member.** -/
def SeatFitAt {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (i : Fin l.length) : Prop :=
  ∃ o n, G.oracleAt (seat i).1 = some o ∧ o.tenants[(seat i).2]? = some n ∧
    o.logLength = aOf cs (l.get i).1 ∧ n.main = (l.get i).1.mainRows * (l.get i).1.mainDeg ∧
    n.mask = (l.get i).1.maskRows * 3 ∧
    ((l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) ∧
    (o.tenants.map fun t => t.main + t.mask).sum = o.words ∧
    ((l.get i).1.mainDeg = 1 ∨ (l.get i).1.mainDeg = 3)

theorem seatFitAt_of {Xi : Type} {G : FileDescription Xi} {cs : Codes} {l : List (OracleShape × ℕ)}
    {seat : Fin l.length → ℕ × ℕ} (h : SeatFits G cs l seat) (i : Fin l.length) :
    SeatFitAt G cs l seat i := h i

/-- **KeptSeat from two notions at the seat and the book's side.** -/
theorem keptSeat_of {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (i : Fin l.length) (hS : SeatFitAt G cs l seat i)
    (hm : (l.get i).1.mainRows ≠ 0) (p : K2.P2) (t : VerifiableInference.Desc.First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ)
    (hSh : ShownAt G cs l seat Y i)
    (hB : ∀ o, G.oracleAt (seat i).1 = some o →
      BookSeat p t fx orc Y old (l.get i).1 (seat i) (2 ^ (cMain cs (l.get i).1).a) o) :
    KeptSeat G p t fx orc Y old (l.get i).1 (seat i) (2 ^ (cMain cs (l.get i).1).a) := by
  obtain ⟨o, n, h1, h2, -, h4, -, h6, -, h8⟩ := hS
  obtain ⟨B, tp, tr, xo, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hB o h1
  have ea : (cMain cs (l.get i).1).a = aOf cs (l.get i).1 := h6.resolve_left hm
  refine ⟨B, tp, tr, xo, o, n, b1, b2, b3, b4, b5, b6, b7, h1, h2, ?_, b8, ?_⟩
  · intro x hx
    have hs := hSh x (by rw [← ea]; exact hx)
    unfold wordOf VerifiableInference.Desc.Oracle.cut at hs
    rw [h1, Option.bind_some, h2, Option.bind_some] at hs
    by_contra hne
    rw [if_neg hne] at hs
    cases hs
  · rw [h4]
    rcases h8 with e | e
    · rw [e, Nat.mul_one]
      rfl
    · rw [e, Nat.mul_comm]
      rfl

/-- **The book's side of KeptSeat, from three tests on the verifier's state and facts on the plan's
list.** L: the plan's places and trees' shapes. -/
theorem bookSeat_of_tests (p : K2.P2) (t : VerifiableInference.Desc.First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ) (sh : OracleShape)
    (seat : ℕ × ℕ) (leaves : ℕ) (o : VerifiableInference.Desc.Oracle)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (B : TreeBook)
    (hB : K2.bookAt (K2.par9 p).firstTree fx.st t.book t.roots (switchNotices fx.T fx.others) =
      some B)
    (hold : old < t.book.place.size) (tp : ℕ) (hL : L.places[old]? = some (tp, seat.2))
    (sh0 : TreeShape) (hLs : L.shapes[tp]? = some sh0)
    (xo : OnBytes.Oracle) (hxo : (K2.skelOf fx).oracles[old]? = some xo) (hsh : xo.shape = sh)
    (hlog : leaves ≤ 2 ^ sh0.logN)
    (horc : ∀ x, x < leaves → orc tp x = Y.col seat.1 x)
    (hskip : (sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = o.mainSkip seat.2) :
    BookSeat p t fx orc Y old sh seat leaves o := by
  unfold VerifiableInference.Desc.K12.Door.atFirstBook
    VerifiableInference.Desc.K12.Door.bookInOrderB at hIn
  unfold VerifiableInference.Desc.K12.Door.atFirstSeats
    VerifiableInference.Desc.K12.Door.seatsCarriedB at hSe
  unfold VerifiableInference.Desc.K12.Door.atFirstFits
    VerifiableInference.Desc.Sound.bookFitsB at hFi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hIn hSe hFi
  obtain ⟨⟨⟨s1, -⟩, s3⟩, -⟩ := hSe
  have hpl : t.book.place[old]? = some (tp, seat.2) := by
    rw [← Array.getElem?_toList, s1, List.getElem?_take, if_pos hold]
    exact hL
  have hf := hFi old hold
  rw [hpl] at hf
  cases htr : t.book.trees[tp]? with
  | none => simp [htr] at hf
  | some tr0 =>
    have htp : tp < t.book.trees.size := (Array.getElem?_eq_some_iff.1 htr).1
    have hs0 : tr0.shape = sh0 := by
      have e := congrArg (fun l => l[tp]?) s3
      simp only [List.getElem?_map, Array.getElem?_toList, htr, Option.map_some,
        List.getElem?_take, if_pos htp, hLs] at e
      exact Option.some.inj e
    have hn0 : tr0.number = (K2.par9 p).firstTree + tp := by
      have e := hIn.2 tp htp
      rw [htr] at e
      simpa using e
    have hB0 := hB
    unfold K2.bookAt at hB
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hB
    obtain ⟨-, -, hk⟩ := H2K.Out.recvP_keeps (ids := x.1) (d1 := x.2) hx
    obtain ⟨T', t1, t2, t3, -⟩ := hk.tree tp tr0 htr
    refine ⟨_, tp, T', xo, hB0, hk.place old _ hpl, t1, hxo, hsh, ?_, ?_, ?_⟩
    · intro y hy
      have hlt : y < 2 ^ T'.shape.logN := by
        rw [t2, hs0]
        exact Nat.lt_of_lt_of_le hy hlog
      split
      · rfl
      · exact Nat.mod_eq_of_lt hlt
    · intro y hy
      rw [t3, hn0, Nat.add_sub_cancel_left]
      exact horc y hy
    · rw [t2, hs0]
      exact hskip

/-- Where the front reads something at a position, the book behind the sending is there. -/
theorem book_of_there {p : K2.P2} {t : VerifiableInference.Desc.First.S}
    {fx : _root_.Tw.K2.Front} {orc : ℕ → ℕ → List UInt64} {q₀ : ℕ}
    (h0 : (K2.longFront p t fx orc q₀).isSome = true) :
    ∃ B, K2.bookAt (K2.par9 p).firstTree fx.st t.book t.roots (switchNotices fx.T fx.others) =
      some B := by
  unfold K2.longFront at h0
  cases hB : K2.bookAt (K2.par9 p).firstTree fx.st t.book t.roots
      (switchNotices fx.T fx.others) with
  | none => simp [hB] at h0
  | some B => exact ⟨B, rfl⟩

/-- **KeptSeat, from two notions at the seat, three tests on the verifier's state, and
facts on the plan's list.** -/
theorem keptSeat_of_fold {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (i : Fin l.length) (hS : SeatFitAt G cs l seat i)
    (hm : (l.get i).1.mainRows ≠ 0) (p : K2.P2) (t : VerifiableInference.Desc.First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ)
    (hSh : ShownAt G cs l seat Y i) (L : VerifiableInference.Desc.K12.Door.Laid)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx orc q₀).isSome = true)
    (hold : old < t.book.place.size) (tp : ℕ) (hL : L.places[old]? = some (tp, (seat i).2))
    (sh0 : TreeShape) (hLs : L.shapes[tp]? = some sh0)
    (xo : OnBytes.Oracle) (hxo : (K2.skelOf fx).oracles[old]? = some xo)
    (hsh : xo.shape = (l.get i).1) (hlog : 2 ^ (cMain cs (l.get i).1).a ≤ 2 ^ sh0.logN)
    (horc : ∀ x, x < 2 ^ (cMain cs (l.get i).1).a → orc tp x = Y.col (seat i).1 x)
    (hskip : ∀ o, G.oracleAt (seat i).1 = some o →
      (sh0.mainSymbols.extract 0 (seat i).2).foldl (· + ·) 0 = o.mainSkip (seat i).2) :
    KeptSeat G p t fx orc Y old (l.get i).1 (seat i) (2 ^ (cMain cs (l.get i).1).a) := by
  obtain ⟨B, hB⟩ := book_of_there h0
  exact keptSeat_of G cs l seat i hS hm p t fx orc Y old hSh fun o ho =>
    bookSeat_of_tests p t fx orc Y old _ _ _ o L hIn hSe hFi B hB hold tp hL sh0 hLs xo hxo hsh hlog
      horc (hskip o ho)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptSeat_of_fold

#print axioms VerifiableInference.Desc.First.K2Caller.bookSeat_of_tests

#print axioms VerifiableInference.Desc.First.K2Caller.keptSeat_of
