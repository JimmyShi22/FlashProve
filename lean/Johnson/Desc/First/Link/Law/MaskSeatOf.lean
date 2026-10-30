-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MaskSeatOf.lean: `MaskSeat` (MaskSeatWord.lean: what ties a member of
the code switch's front to a seat of the table of joints, for its mask rows: twelve clauses) FROM
THE TABLE's TWO NOTIONS AT THE SEAT AND THE BOOK's SIDE: `keptSeat_of`
(Johnson/Top/H0/K2Caller/KeptSeatOf.lean), which pays `KeptSeat`, carried to the mask words, step
for step. A definition and a theorem.

  `BookMask`: the book's side of MaskSeat: eight of its clauses, at what the description tells of
    the seat's tree: `BookSeat` with two clauses turned: the leaf that is read at the
    position x is x modulo the tree's length · the two skips in front of the tenant's MASK words
    are one.
  `maskSeat_of`: **SeatFitAt G cs l seat i (a test on the plan alone, at one member) · ShownAt G cs
    l seat Y i (every leaf is shown: the table's promise) · BookMask ⊢ MaskSeat G p t fx orc Y old
    (l.get i).1 (seat i) positions fun x => x % 2 ^ aOf cs (l.get i).1.** The two notions give the
    other four clauses: the description tells the tree and the tenant · every leaf that is read
    has the tree's words · the tenant's mask words are three a mask row.
Limits. `BookMask` is a premise (for `BookSeat` there is `bookSeat_of_tests`; the like for the
mask's skip is not typed). ShownAt is promised at the border IN FRONT of the closing at every member
(by a reading of the table, not shown here). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.MaskSeatWord
import Johnson.Top.H0.K2Caller.KeptSeatOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (ShownAt)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt)
open _root_.Tw.K2 (switchNotices)

/-- **The book's side of MaskSeat**, at what the description tells of the seat's tree. -/
def BookMask (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ) (sh : OracleShape) (seat : ℕ × ℕ)
    (positions a : ℕ) (o : VerifiableInference.Desc.Oracle) : Prop :=
  ∃ (B : TreeBook) (tp : ℕ) (tr : Tree) (xo : OnBytes.Oracle),
    First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
      (switchNotices fx.T fx.others) = some B ∧
    B.place[old]? = some (tp, seat.2) ∧ B.trees[tp]? = some tr ∧
    (First.K2.skelOf fx).oracles[old]? = some xo ∧ xo.shape = sh ∧
    (∀ x, x < positions →
      (if tr.shape.logN == p.logN then x else x % 2 ^ tr.shape.logN) = x % 2 ^ a) ∧
    (∀ x, x < positions →
      orc (tr.number - (First.K2.par9 p).firstTree) (x % 2 ^ a) = Y.col seat.1 (x % 2 ^ a)) ∧
    tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
      o.maskSkip seat.2

/-- **MaskSeat from the table's two notions at the seat and the book's side.** -/
theorem maskSeat_of {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (i : Fin l.length) (hS : SeatFitAt G cs l seat i)
    (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (Y : Strs) (old positions : ℕ) (hSh : ShownAt G cs l seat Y i)
    (hB : ∀ o, G.oracleAt (seat i).1 = some o →
      BookMask p t fx orc Y old (l.get i).1 (seat i) positions (aOf cs (l.get i).1) o) :
    MaskSeat G p t fx orc Y old (l.get i).1 (seat i) positions
      fun x => x % 2 ^ aOf cs (l.get i).1 := by
  obtain ⟨o, n, h1, h2, -, -, h5, -, -, -⟩ := hS
  obtain ⟨B, tp, tr, xo, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hB o h1
  refine ⟨B, tp, tr, xo, o, n, b1, b2, b3, b4, b5, b6, b7, h1, h2, ?_, b8, ?_⟩
  · intro x _
    have hs := hSh (x % 2 ^ aOf cs (l.get i).1) (Nat.mod_lt _ (Nat.two_pow_pos _))
    unfold wordOf VerifiableInference.Desc.Oracle.cut at hs
    rw [h1, Option.bind_some, h2, Option.bind_some] at hs
    by_contra hne
    rw [if_neg hne] at hs
    cases hs
  · rw [h5, Nat.mul_comm]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.maskSeat_of
