-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesFall.lean: WHAT `MaskTieBook` (Law/Rule/Ties.lean; with
the border's sentence a letter: `MaskTieBookOn`, Law/Rule/TiesOn.lean) FALLS INTO: FOUR SENTENCES,
EACH WITH ONE OWNER, AND THE THEOREM THAT JOINS THEM. DEFINITIONS: PREMISES' FORMS. No kind is
named; what a caller's reader reads is a letter.

  1  `SenderLays`   THE SENDER's: the mask row's entry of the number ν, as the sender lays it, is
     the sender's own coin number base + ν. row: the mask row as a function of a run's coins, the
     input and the challenges: the text of the sender's own authors
  2  `ReaderReads`   THE THREAD's, WITH THE SENDER's AUTHORS: what the caller's reader reads off
     the thread's witness under the number ν is that row's entry
  3  `LedgerIs`   OURS, by the project's division of the work; shown at 75 of 76
     borders of the first chain's thread at the library's head (Law/Rule/LedgerCallers.lean;
     Law/Rule/LedgerLookups.lean and Law/Rule/LedgerLeft.lean): where the border's sentence holds in
     front of the member, the slot at which the verifier's ledger stands is the number ν₀ of the
     member's first scalar in the segment
  4  `RowIsStretch`   THE BOOK's MAKER's: what the row's parts spend is one stretch of the
     sender's coins
  5  `getD_stretch`, `maskTieBookOn_of`, `maskTieBook_of`   the four, with N at every ν₀ + j with j
     below cnt (`hN`), give the tie at the reader "under the slot plus j", at every j below the
     number of the row's coins

At: THE BORDER's SENTENCE IS A LETTER in 2 and 3: the thread's (`Thr T b`), the thread's with what
is said (`ThrS T Said b`), or a sentence on reached states: whoever pays picks the weakest debt
that its caller can spend.

Limits. OF THE FOUR, `LedgerIs` ALONE IS SHOWN AT A THREAD; `RowIsStretch` has a payer by a test on
the book (Honest/BookStretch.lean); the other two are not shown. Coins of the extension field
alone. One sender for the whole row: a row that spends of two messages (a merge's end values lie in
the index masks' message) is not covered HERE: up to its first sender's stretch it is in
Law/Rule/TiesAll.lean and Law/Rule/TiesLen.lean. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The sender's.** ch: the chain's number. o: the sender's address. base: where the message's
    mask
entries begin among the sender's coins of the extension field. N: at which numbers. A premise's
    form.
-/
def SenderLays (Bk : ProverCoinCounts) (ch : Nat) (o : Addr) (base : Nat)
    (row : Coins Bk → W → List Fmt.Drawn → Nat → E) (N : Nat → Prop) : Prop :=
  ∀ k w h ν, N ν → row k w h ν = (coinsE (k.look ch o).2).getD (base + ν) zeroE

/-- **The thread's, with the sender's authors.** maskOf: the caller's reader of the mask row's
entry of a number, off what is open, the state, the input and the witness. A premise's form. -/
def ReaderReads (T : Thread Bk S Cl V W X Pb) (At : Coins Bk → S → Mid W X → Env → Prop)
    {A G : Type} (opn : S → Option A)
    (maskOf : A → S → W → T.Wt → Nat → G) (val : E → G)
    (row : Coins Bk → W → List Fmt.Drawn → Nat → E) (N : Nat → Prop) : Prop :=
  ∀ k s m En, At k s m En → ∀ a, opn s = some a → ∀ ds ν, N ν →
    maskOf a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) ν =
      val (row k m.st.input (m.st.heard ++ ds) ν)

/-- **The verifier's ledger against the count of scalars sent.** slot: the ledger's next free slot.
ν₀: the number of the member's first scalar in the segment. A premise's form. -/
def LedgerIs (At : Coins Bk → S → Mid W X → Env → Prop) {A : Type} (opn : S → Option A)
    (slot : A → Nat) (ν₀ : Nat) : Prop :=
  ∀ k s m En, At k s m En → ∀ a, opn s = some a → slot a = ν₀

/-- **The book's maker's.** n: how many parts the row has. s₀, cnt: where the stretch begins among
    the
sender's coins, and how long it is. A premise's form. -/
def RowIsStretch (Bk : ProverCoinCounts) (ch : Nat) (p : Place) (n : Nat) (o : Addr) (s₀ cnt : Nat) : Prop :=
  ∀ k : Coins Bk, rowSpent Bk (k.look ch) p n 0 = ((coinsE (k.look ch o).2).drop s₀).take cnt

/-- An entry of a stretch. -/
theorem getD_stretch {α : Type} (l : List α) (s c j : Nat) (d : α) (h : j < c) :
    ((l.drop s).take c).getD j d = l.getD (s + j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h,
    List.getElem?_drop]

/-- **The four give the tie**, where N holds at every ν₀ + j with j below cnt (`hN`). -/
theorem maskTieBookOn_of {T : Thread Bk S Cl V W X Pb}
    {At : Coins Bk → S → Mid W X → Env → Prop} {p : Place} {n : Nat} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G}
    {row : Coins Bk → W → List Fmt.Drawn → Nat → E} {N : Nat → Prop} {o : Addr}
    {base ν₀ cnt : Nat} {slot : A → Nat} (h2 : SenderLays Bk T.chain o base row N)
    (h3 : ReaderReads T At opn maskOf val row N) (h1 : LedgerIs At opn slot ν₀)
    (hB : RowIsStretch Bk T.chain p n o (base + ν₀) cnt) (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieBookOn T At p n opn (fun a s w v j => maskOf a s w v (slot a + j)) val
      (fun len j => j < len) := by
  intro k s m En hT a ha ds j hj
  rw [hB k] at hj ⊢
  have hc : j < cnt := Nat.lt_of_lt_of_le hj (by
    rw [List.length_take]
    exact Nat.min_le_left _ _)
  show maskOf a s m.st.input (T.wit k m.st.input (m.st.heard ++ ds)) (slot a + j) = _
  rw [h1 k s m En hT a ha, h3 k s m En hT a ha ds _ (hN j hc), h2 k _ _ _ (hN j hc),
    getD_stretch _ _ _ _ _ hc, Nat.add_assoc]

/-- The same at the thread's own sentence: Law/Rule/Ties.lean's form. -/
theorem maskTieBook_of {T : Thread Bk S Cl V W X Pb} {b : Nat} {p : Place} {n : Nat} {A G : Type}
    {opn : S → Option A} {maskOf : A → S → W → T.Wt → Nat → G} {val : E → G}
    {row : Coins Bk → W → List Fmt.Drawn → Nat → E} {N : Nat → Prop} {o : Addr}
    {base ν₀ cnt : Nat} {slot : A → Nat} (h2 : SenderLays Bk T.chain o base row N)
    (h3 : ReaderReads T (Thr T b) opn maskOf val row N) (h1 : LedgerIs (Thr T b) opn slot ν₀)
    (hB : RowIsStretch Bk T.chain p n o (base + ν₀) cnt) (hN : ∀ j, j < cnt → N (ν₀ + j)) :
    MaskTieBook T b p n opn (fun a s w v j => maskOf a s w v (slot a + j)) val
      (fun len j => j < len) :=
  maskTieBookOn_of h2 h3 h1 hB hN

end ProofFile.Honest

#print axioms ProofFile.Honest.getD_stretch
#print axioms ProofFile.Honest.maskTieBookOn_of
#print axioms ProofFile.Honest.maskTieBook_of
