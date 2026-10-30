-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesFree.lean: THE MASK's TIE WITH ITS FENCE A BOUND. In
`maskTieOn_len`, `maskTieOn_whole` (Law/Rule/TiesLen.lean) and `maskTieOn_but_last`
(Law/Rule/TiesHead.lean) three premises, h2, hin and h3, share a letter N ("at which entries of the
mask row"), and a fourth, hN, asks that the member's slots lie in N. No statement said what N is.
Here N is "below
free", and hN is one bound on numbers: ν₀ + cnt ≤ free.

`free` IS A LETTER OF THE THREE STATEMENTS, TIED TO NO DEFINITION. The callers are meant to put a
message's number of free entries there: the field `MsgAt.free`, which `ownerOf` fills by a call of
the library's `Send.freeMaskEntries` (Honest/BookEntries.lean; OnBytes/Iop/Send.lean). No premise
here asks that. A caller may pay h2, hin, h3 and hfree at free := ν₀ + cnt, the old N at its
narrowest. So the fence has a form here, not an owner.

WHAT THE BOUND IS MEANT TO BE PAID BY: the book's maker's own test `wantsFree`
(Honest/BookEntries.lean), which is evaluated at closed sizes; as a lemma, `wantsFree_below`
(Honest/BookFree.lean).

  1  `SenderLaysOwn.mono`   from more entries to fewer: a sentence that is shown at all entries of
     the row serves below the free ones
  2  `maskTieOn_len_free`, `maskTieOn_whole_free`, `maskTieOn_but_last_free`   the three calls

Limits. As those of Law/Rule/TiesLen.lean and Law/Rule/TiesHead.lean. THAT A MEMBER's STRETCH IS
MADE OF STRETCHES THAT THE MAKER's TEST HAS SEEN IS NOT SHOWN HERE. That `free` is the number in
another author's premise of the like sort is held by nobody. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- From more entries to fewer: a sender's authors may show their sentence at all entries of the
row; the tie spends it below the free ones. -/
theorem SenderLaysOwn.mono {d : Due} {rowOf : Cs d → Nat → E} {base : Nat} {N N' : Nat → Prop}
    (hN : ∀ ν, N' ν → N ν) (h : SenderLaysOwn rowOf base N) : SenderLaysOwn rowOf base N' :=
  fun cs ν hν => h cs ν (hN ν hν)

theorem maskTieOn_len_free {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {ps : List (Part V W X)} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt free : Nat} {slot : A → Nat}
    {r : Nat} (h2 : SenderLaysOwn rowOf base (· < free)) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) (· < free))
    (h1 : LedgerIs At opn slot ν₀)
    (hB : RowBeginsBy Bk T.chain p ps.length o (base + ν₀) cnt r)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hfree : ν₀ + cnt ≤ free) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j + r < len) :=
  maskTieOn_len h2 ho hin h3 h1 hB hF fun j hj => by
    show ν₀ + j < free
    omega

theorem maskTieOn_whole_free {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {ps : List (Part V W X)} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt free : Nat} {slot : A → Nat}
    (h2 : SenderLaysOwn rowOf base (· < free)) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) (· < free))
    (h1 : LedgerIs At opn slot ν₀)
    (hS : oneStretch (rowEntries Bk p ps.length 0) = some (o, base + ν₀, cnt))
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hfree : ν₀ + cnt ≤ free) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j < len) :=
  maskTieOn_whole h2 ho hin h3 h1 hS hF fun j hj => by
    show ν₀ + j < free
    omega

theorem maskTieOn_but_last_free {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {ps : List (Part V W X)} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt free : Nat} {slot : A → Nat}
    {es₁ : List Ahead} {e : Ahead} (h2 : SenderLaysOwn rowOf base (· < free)) (ho : OwnIs Bk T.chain
        o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) (· < free))
    (h1 : LedgerIs At opn slot ν₀)
    (hH : headStretch (rowEntries Bk p ps.length 0) = some ((o, base + ν₀, cnt), es₁, [e]))
    (h1e : e.count.e = 1)
    (he : ∀ k : Coins Bk, e.start.e + e.count.e ≤ (k.look T.chain e.owner).1.e)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hfree : ν₀ + cnt ≤ free) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j + 1 < len) :=
  maskTieOn_but_last h2 ho hin h3 h1 hH h1e he hF fun j hj => by
    show ν₀ + j < free
    omega

end ProofFile.Honest

#print axioms ProofFile.Honest.SenderLaysOwn.mono
#print axioms ProofFile.Honest.maskTieOn_len_free
#print axioms ProofFile.Honest.maskTieOn_whole_free
#print axioms ProofFile.Honest.maskTieOn_but_last_free
