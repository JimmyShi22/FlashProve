-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesAll.lean: THE MASK's TIE IN ONE CALL, AND FOR A ROW THAT
SPENDS OF TWO MESSAGES. Over Law/Rule/TiesOn.lean, Law/Rule/TiesFall.lean, Law/Rule/TiesOwn.lean
and the frame's keeper's test on the book (Honest/BookStretch.lean: `rowEntries`, `oneStretch`).

  1  `MaskTieOn.mono_J`, `MaskTieBookOn.mono_J`   a tie at more numbers j gives the tie at fewer
  2  `RowBeginsStretch`, `rowBegins_of`   what the row's parts spend BEGINS with one stretch of
     one sender's coins: paid where the book's entries for the row are a list on which the keeper's
     test says yes, with any entries behind: so a merge's row, whose last coins are another
     message's, is covered up to these
  3  `coinsE_length`, `getD_begins`, `maskTieBookOn_begins`   the four sentences of
     Law/Rule/TiesFall.lean, with 2 in the stead of `RowIsStretch`, and two premises more (`hF`: at
     every run's coins the stretch ends inside the sender's count; `hN`: N holds at the stretch's
     numbers) give the tie at the numbers j below the stretch's length
  4  `maskTieOn_all`   ONE CALL, TEN PREMISES: the sentence of the sender's authors at its own type
     (`h2`), `OwnIs` (`ho`), the reader's sentence (`h3`), the ledger's (`h1`), two sentences on the
     book's entries for the row (`hE`: they are cut in two; `hS`: `oneStretch` returns a stretch at
     the first cut), one equation on closed numbers (`hs`) and three bounds (`hin`, `hF`, `hN`), to
     `MaskTieOn` at `spentOf`

Limits. Premises' forms and joints: THE PREMISES ARE NOT SHOWN TOGETHER AT ANY THREAD. Of the
coins behind the stretch nothing is said. Coins of the extension field alone. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookStretch
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOwn

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

theorem MaskTieOn.mono_J (hJ : ∀ len j, J' len j → J len j)
    (h : MaskTieOn T At p ps opn entry val coins J) :
    MaskTieOn T At p ps opn entry val coins J' :=
  fun k s m En hT a c ha hc ds j hj => h k s m En hT a c ha hc ds j (hJ _ _ hj)

theorem MaskTieBookOn.mono_J (hJ : ∀ len j, J' len j → J len j)
    (h : MaskTieBookOn T At p n opn entry val J) : MaskTieBookOn T At p n opn entry val J' :=
  fun k s m En hT a ha ds j hj => h k s m En hT a ha ds j (hJ _ _ hj)

end

/-- **What the row's parts spend begins with one stretch of one sender's coins.** A premise's form.
-/
def RowBeginsStretch (Bk : ProverCoinCounts) (ch : Nat) (p : Place) (n : Nat) (o : Addr) (s₀ cnt : Nat) : Prop
    :=
  ∀ k : Coins Bk, ∃ rest,
    rowSpent Bk (k.look ch) p n 0 = ((coinsE (k.look ch o).2).drop s₀).take cnt ++ rest

theorem rowBegins_of {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt : Nat}
    {es₁ es₂ : List Ahead} (h : rowEntries Bk p n 0 = es₁ ++ es₂)
    (h1 : oneStretch es₁ = some (o, s₀, cnt)) : RowBeginsStretch Bk ch p n o s₀ cnt := by
  intro k
  refine ⟨es₂.flatMap (sliceE (k.look ch)), ?_⟩
  rw [rowSpent_entries, h, List.flatMap_append, oneStretch_slices (k.look ch) h1]

theorem coinsE_length {d : Due} (c : Cs d) : (coinsE c).length = d.e := by
  unfold coinsE
  exact List.length_ofFn

/-- An entry of a list that begins with a stretch. -/
theorem getD_begins {α : Type} (l rest : List α) (s c j : Nat) (d : α) (h : j < c)
    (hl : s + c ≤ l.length) : (((l.drop s).take c) ++ rest).getD j d = l.getD (s + j) d := by
  have hlen : j < ((l.drop s).take c).length := by
    rw [List.length_take, List.length_drop]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD,
    getD_stretch _ _ _ _ _ h]

theorem maskTieBookOn_begins {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {n : Nat} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G}
    {row : Coins Bk → W → List Fmt.Drawn → Nat → E} {N : Nat → Prop} {o : Addr}
    {base ν₀ cnt : Nat} {slot : A → Nat} (h2 : SenderLays Bk T.chain o base row N)
    (h3 : ReaderReads T At opn maskOf val row N) (h1 : LedgerIs At opn slot ν₀)
    (hB : RowBeginsStretch Bk T.chain p n o (base + ν₀) cnt)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieBookOn T At p n opn (fun a s w v j => maskOf a s w v (slot a + j)) val
      (fun _ j => j < cnt) := by
  intro k s m En hT a ha ds j hj
  obtain ⟨rest, hr⟩ := hB k
  rw [hr]
  show maskOf a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) (slot a + j) = _
  rw [h1 k s m En hT a ha, h3 k s m En hT a ha ds _ (hN j hj), h2 k _ _ _ (hN j hj),
    getD_begins _ _ _ _ _ _ hj (by rw [coinsE_length]; exact hF k), Nat.add_assoc]

/-- **One call.** d: the sender's part's own count. es₁, es₂: the book's entries for the row, cut
where the sender's stretch ends. -/
theorem maskTieOn_all {T : Thread Bk S Cl V W X Pb} {At : Coins Bk → S → Mid W X → Env → Prop}
    {p : Place} {ps : List (Part V W X)} {A G : Type} {opn : S → Option A}
    {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G} {N : Nat → Prop} {o : Addr} {d : Due}
    {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base ν₀ s₀ cnt : Nat} {slot : A → Nat}
    {es₁ es₂ : List Ahead} (h2 : SenderLaysOwn rowOf base N) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, N ν → base + ν < d.e)
    (h3 : ReaderReads T At opn maskOf val (fun k _ _ ν => rowOf (own k) ν) N)
    (h1 : LedgerIs At opn slot ν₀) (hE : rowEntries Bk p ps.length 0 = es₁ ++ es₂)
    (hS : oneStretch es₁ = some (o, s₀, cnt)) (hs : s₀ = base + ν₀)
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieOn T At p ps opn (fun a s w v j => maskOf a s w v (slot a + j)) val (spentOf ps)
      (fun _ j => j < cnt) :=
  maskTieOn_of_book (maskTieBookOn_begins (senderLays_of_own h2 ho hin) h3 h1
    (hs ▸ rowBegins_of hE hS) hF hN)

end ProofFile.Honest

#print axioms ProofFile.Honest.MaskTieOn.mono_J
#print axioms ProofFile.Honest.MaskTieBookOn.mono_J
#print axioms ProofFile.Honest.rowBegins_of
#print axioms ProofFile.Honest.coinsE_length
#print axioms ProofFile.Honest.getD_begins
#print axioms ProofFile.Honest.maskTieBookOn_begins
#print axioms ProofFile.Honest.maskTieOn_all
