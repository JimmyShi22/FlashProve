-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesLen.lean: THE MASK's TIE IN THE CALLERS' OWN FORM OF "AT
WHICH j". `maskTieOn_all` (Law/Rule/TiesAll.lean) ends at "j below the stretch's length"; kind K5's
field asks "j below the number of the row's coins", kind K4's "j + 1 below that number"; `mono_J`
there asks its premise at every length, so it cannot bridge; and `RowBeginsStretch` does not say
how many coins stand behind the stretch. Here: the count
behind the stretch is a letter r, and the tie ends at "j + r below the number of the row's coins".

  1  `MaskTieOn.mono_at`, `MaskTieBookOn.mono_at`   from one J to another AT THE LENGTH THAT IS
     THERE
  2  `RowBeginsBy`, `RowBeginsBy.begins`, `rowSpent_length`   what the row's parts spend is one
     stretch of one sender's coins and r coins more; its length
  3  `sliceE_length`, `rowBeginsBy_nil`, `rowBeginsBy_one`   paid by the frame's test on the book
     : nothing behind the stretch (r = 0: K5); one entry behind it, which lies inside its
     owner's count (r = that entry's count: K4's last coin)
  4  `maskTieOn_len`   ONE CALL, ending at "j + r below the number of the row's coins"
  5  `maskTieOn_whole`   at r = 0, in K5's letters: "j below the number"

Limits. As Law/Rule/TiesAll.lean's. OF THE r COINS BEHIND THE STRETCH NOTHING IS SAID BUT THEIR
NUMBER: a tie on them (another sender's message) is nobody's yet: NO LEMMA HERE COVERS A WHOLE ROW
THAT SPENDS OF TWO MESSAGES. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

section
variable {T : Thread Bk S Cl V W X Pb} {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place}
  {ps : List (Part V W X)} {n : Nat} {A G : Type} {opn : S → Option A}
  {entry : A → S → W → T.Wt → Nat → G} {val : E → G} {coins : RowCoins ps → List E}
  {J J' : Nat → Nat → Prop}

theorem MaskTieOn.mono_at
    (hJ : ∀ (k : Coins Bk) c, lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) p ps 0 = .ok c →
      ∀ j, J' (coins c).length j → J (coins c).length j)
    (h : MaskTieOn T At p ps opn entry val coins J) :
    MaskTieOn T At p ps opn entry val coins J' :=
  fun k s m En hT a c ha hc ds j hj => h k s m En hT a c ha hc ds j (hJ k c hc j hj)

theorem MaskTieBookOn.mono_at
    (hJ : ∀ (k : Coins Bk) j, J' (rowSpent Bk (k.look T.chain) p n 0).length j →
      J (rowSpent Bk (k.look T.chain) p n 0).length j)
    (h : MaskTieBookOn T At p n opn entry val J) : MaskTieBookOn T At p n opn entry val J' :=
  fun k s m En hT a ha ds j hj => h k s m En hT a ha ds j (hJ k j hj)

end

/-- **What the row's parts spend is one stretch of one sender's coins, and r coins more.** A
    premise's
form. -/
def RowBeginsBy (Bk : ProverCoinCounts) (ch : Nat) (p : Place) (n : Nat) (o : Addr) (s₀ cnt r : Nat) : Prop :=
  ∀ k : Coins Bk, ∃ rest, rest.length = r ∧
    rowSpent Bk (k.look ch) p n 0 = ((coinsE (k.look ch o).2).drop s₀).take cnt ++ rest

theorem RowBeginsBy.begins {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt r : Nat}
    (h : RowBeginsBy Bk ch p n o s₀ cnt r) : RowBeginsStretch Bk ch p n o s₀ cnt := fun k => by
  obtain ⟨rest, -, e⟩ := h k
  exact ⟨rest, e⟩

theorem rowSpent_length {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt r : Nat}
    (h : RowBeginsBy Bk ch p n o s₀ cnt r) (k : Coins Bk) (hF : s₀ + cnt ≤ (k.look ch o).1.e) :
    (rowSpent Bk (k.look ch) p n 0).length = cnt + r := by
  obtain ⟨rest, hr, e⟩ := h k
  rw [e, List.length_append, hr, List.length_take, List.length_drop, coinsE_length]
  omega

theorem sliceE_length (look : Addr → (d : Due) × Cs d) (e : Ahead)
    (h : e.start.e + e.count.e ≤ (look e.owner).1.e) : (sliceE look e).length = e.count.e := by
  unfold sliceE
  rw [List.length_take, List.length_drop, coinsE_length]
  omega

theorem rowBeginsBy_nil {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt : Nat}
    (hS : oneStretch (rowEntries Bk p n 0) = some (o, s₀, cnt)) :
    RowBeginsBy Bk ch p n o s₀ cnt 0 := fun k =>
  ⟨[], rfl, by rw [List.append_nil, rowSpent_entries, oneStretch_slices (k.look ch) hS]⟩

theorem rowBeginsBy_one {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt : Nat}
    {es₁ : List Ahead} {e : Ahead} (hE : rowEntries Bk p n 0 = es₁ ++ [e])
    (hS : oneStretch es₁ = some (o, s₀, cnt))
    (he : ∀ k : Coins Bk, e.start.e + e.count.e ≤ (k.look ch e.owner).1.e) :
    RowBeginsBy Bk ch p n o s₀ cnt e.count.e := fun k =>
  ⟨sliceE (k.look ch) e, sliceE_length _ e (he k), by
    rw [rowSpent_entries, hE, List.flatMap_append, oneStretch_slices (k.look ch) hS]
    show _ ++ (sliceE (k.look ch) e ++ []) = _
    rw [List.append_nil]⟩

/-- **One call, in the callers' form.** r: how many coins the row's parts spend behind the sender's
stretch. -/
theorem maskTieOn_len {T : Thread Bk S Cl V W X Pb} {At : Coins Bk → S → Mid W X → Env → Prop}
    {p : Place} {ps : List (Part V W X)} {A G : Type} {opn : S → Option A}
    {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {N : Nat → Prop} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt r : Nat} {slot : A → Nat}
    (h2 : SenderLaysOwn rowOf base N) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, N ν → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) N)
    (h1 : LedgerIs At opn slot ν₀)
    (hB : RowBeginsBy Bk T.chain p ps.length o (base + ν₀) cnt r)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j + r < len) :=
  maskTieOn_of_book (MaskTieBookOn.mono_at (J := fun _ j => j < cnt)
    (fun k j hj => by
      rw [rowSpent_length hB k (hF k)] at hj
      omega)
    (maskTieBookOn_begins (senderLays_of_own h2 ho hin) h3 h1 hB.begins hF hN))

/-- At r = 0: "j below the number of the row's coins". -/
theorem maskTieOn_whole {T : Thread Bk S Cl V W X Pb} {At : Coins Bk → S → Mid W X → Env → Prop}
    {p : Place} {ps : List (Part V W X)} {A G : Type} {opn : S → Option A}
    {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {N : Nat → Prop} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ cnt : Nat} {slot : A → Nat}
    (h2 : SenderLaysOwn rowOf base N) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, N ν → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) N)
    (h1 : LedgerIs At opn slot ν₀)
    (hS : oneStretch (rowEntries Bk p ps.length 0) = some (o, base + ν₀, cnt))
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun len j => j < len) :=
  MaskTieOn.mono_J (fun _ _ h => h)
    (maskTieOn_len h2 ho hin h3 h1 (rowBeginsBy_nil hS) hF hN)

end ProofFile.Honest

#print axioms ProofFile.Honest.MaskTieOn.mono_at
#print axioms ProofFile.Honest.MaskTieBookOn.mono_at
#print axioms ProofFile.Honest.RowBeginsBy.begins
#print axioms ProofFile.Honest.rowSpent_length
#print axioms ProofFile.Honest.sliceE_length
#print axioms ProofFile.Honest.rowBeginsBy_nil
#print axioms ProofFile.Honest.rowBeginsBy_one
#print axioms ProofFile.Honest.maskTieOn_len
#print axioms ProofFile.Honest.maskTieOn_whole
