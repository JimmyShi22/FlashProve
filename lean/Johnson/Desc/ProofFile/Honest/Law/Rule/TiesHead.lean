-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesHead.lean: THE MASK's TIE AT A ROW THAT SPENDS ONE COIN
MORE BEHIND ITS SENDER's STRETCH (meant for kind K4's rows, where that coin is another message's; no
premise here asks that its owner differ): FROM ONE TEST WITH CODE ON THE BOOK. The frame's keeper's
`headStretch` (Honest/BookHeadStretch.lean) cuts what a row's parts spend into the head that is one
stretch of one sender's coins, and the rest. Where the rest is one entry of one coin of the
extension field, inside its owner's count, the tie of Law/Rule/TiesLen.lean ends at "j + 1 below the
number of the row's coins": kind K4's own form ("every coin but the last").

  1  `rowBeginsBy_head`   from the test's answer to `RowBeginsBy`, at r := the rest's one entry's
     count
  2  `maskTieOn_but_last`   ONE CALL, at r = 1

By an evaluation of ours at the small set (no theorem; its print is not in this library) the
test answers so at both K4's rows and at K11's: the head is the segment's mask row's share, the
rest one entry of one coin.

Limits. As Law/Rule/TiesLen.lean's. OF THE LAST COIN NOTHING IS SAID BUT THAT IT IS ONE: the tie on
it (the index masks' message) is nobody's yet: NO LEMMA HERE COVERS THE WHOLE ROW. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookHeadStretch
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

theorem rowBeginsBy_head {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt : Nat}
    {es₁ : List Ahead} {e : Ahead}
    (h : headStretch (rowEntries Bk p n 0) = some ((o, s₀, cnt), es₁, [e]))
    (he : ∀ k : Coins Bk, e.start.e + e.count.e ≤ (k.look ch e.owner).1.e) :
    RowBeginsBy Bk ch p n o s₀ cnt e.count.e :=
  rowBeginsBy_one (headStretch_of h).1 (headStretch_of h).2 he

/-- **One call, at a row with one coin more behind the sender's stretch.** -/
theorem maskTieOn_but_last {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {ps : List (Part V W X)} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {N : Nat → Prop}
    {o : Addr} {d : Due} {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt : Nat}
    {slot : A → Nat} {es₁ : List Ahead} {e : Ahead}
    (h2 : SenderLaysOwn rowOf base N) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, N ν → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) N)
    (h1 : LedgerIs At opn slot ν₀)
    (hH : headStretch (rowEntries Bk p ps.length 0) = some ((o, base + ν₀, cnt), es₁, [e]))
    (h1e : e.count.e = 1)
    (he : ∀ k : Coins Bk, e.start.e + e.count.e ≤ (k.look T.chain e.owner).1.e)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j + 1 < len) := by
  have hB := rowBeginsBy_head (ch := T.chain) hH he
  rw [h1e] at hB
  exact maskTieOn_len h2 ho hin h3 h1 hB hF hN

end ProofFile.Honest

#print axioms ProofFile.Honest.rowBeginsBy_head
#print axioms ProofFile.Honest.maskTieOn_but_last
