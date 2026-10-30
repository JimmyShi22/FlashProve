-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsAt.lean: THE THREE EQUATIONS THAT THE LAST CHAIN's FIRST ROW ASKS OF THE
READING
OF WORDS THROUGH A RECORD, PROVED OF THE TERM, INSIDE A FENCE. Definitions of Prop, two definitions
and theorems with their proofs.

WHY A FENCE. `Reads p words omW wv` (LastRow0W.lean, not in this library) asks its three equations
at ALL records s, s' with `Says p s s'`. `Says` (Johnson/Desc/Third/Law/Says.lean) reads neither
record's book; the term reads
a message's seat off the book. Two records with one statement and two books both stand in `Says`: so
no term that reads the book meets `Reads` as typed (by reading). And omW,
wv name no record, while Omega's seat lies in the border that the record in front holds.

  `ReadsOn p Ok words omW wv`: `Reads`' three fields to the letter, each with the premise `Ok s s'`.
  `AtStart st₁ book₁ w₁ o s s'`: THE FENCE: `BookedLast o s s'` (WordsAt.lean) and: the record in
    front has the first chain's last statement st₁ and book book₁, W's number is w₁, and it is
    there.
  `omegaWords`, `wWords`: omW and wv: Omega's words off the shared chain's end o, W's off the first
    chain's end: they name no record of the last chain.
  **`readsOn_wordsLast`**: `ReadsOn p (AtStart st₁ book₁ w₁ o) (wordsLast arr t₁ t₂) (omegaWords …)
    (wWords …)`.
  `firstOutFrom_is`, `startIs`: what the start's yes lays (by its text).
  **`atStart_of_yes`**: the fence holds at the start's record and what the block `batchLinearConstraintsSecondPart p` makes
    of it, GIVEN TWO NAMED PREMISES ON THE BOOKS: placed: every place of the first chain's last book
    names a tree that is there · tenant: in the shared chain's book Omega is part 0 of its tree.

Limits. Nothing on soundness or on hiding. The two premises are paid nowhere. t₁, t₂, arr are
letters: that t₁ is the number of the first chain's trees, and that arr is the file's own map from a
seat to a message's number, is said nowhere. NO MEMBER: that the start and the block say yes
anywhere is a run's matter.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄ start₃E start₃ firstOutFrom numbersOk
  rootsB batchLinearConstraintsSecondPart FirstOut)
open VerifiableInference.Desc.Third.Law (Says BookSays Sharp says_k14Second bookSays_k14Second
  sharp_k14Second)

/-- **What is asked of the reading of words through a record, INSIDE A FENCE.** The three fields
are,
to the letter, those of `Reads` (LastRow0W.lean, not in this library), each with one premise more:
`Ok s s'`, the book-keeping of the two records. -/
structure ReadsOn {K W : Type} (p : P₁₄) (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K)
    (omW wv : W → Nat → K) : Prop where
  older : ∀ s s' w, Says p s s' → Ok s s' → ∀ o < s.st.oracles.size, ∀ part i,
    words s' w o part i = words s w o part i
  omega : ∀ s s' w y, Says p s s' → Ok s s' →
    words s' w s.st.oracles.size .main ((linLayOmega s.st.codes p.S).index y) = omW w y
  w : ∀ s s' w c, Says p s s' → Ok s s' →
    words s' w s.loc.w .main ((linLayW s.st.codes p.S).index c) = wv w c

/-- **THE FENCE**: the book-keeping (`BookedLast`), and the record in front is the start's: the
first chain's last statement and book, and W's number there. -/
structure AtStart (st₁ : Statement) (book₁ : TreeBook) (w₁ : ℕ) (o : SharedOut) (s s' : S₃) :
    Prop where
  booked : BookedLast o s s'
  st : s.st = st₁
  book : s.book = book₁
  w : s.loc.w = w₁
  there : w₁ < st₁.oracles.size

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)

/-- Omega's words, off the shared chain's end: they name no record of the last chain. -/
def omegaWords (p : P₁₄) (codes : Codes) (o : SharedOut) (w : Wit Cells Tok MsgT) (y : ℕ) : GE :=
  wordsShared arr t₁ o.st o.book w o.omega .main ((linLayOmega codes p.S).index y)

/-- W's words, off the first chain's end. -/
def wWords (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook) (w₁ : ℕ) (w : Wit Cells Tok MsgT)
    (c : ℕ) : GE :=
  wordsFirst arr st₁ book₁ w w₁ .main ((linLayW st₁.codes p.S).index c)

/-- **THE TERM MEETS THE THREE EQUATIONS, INSIDE THE FENCE.** -/
theorem readsOn_wordsLast (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook) (w₁ : ℕ) (o : SharedOut) :
    ReadsOn p (AtStart st₁ book₁ w₁ o) (wordsLast (Cells := Cells) (Tok := Tok) arr t₁ t₂)
      (omegaWords arr t₁ p st₁.codes o) (wWords arr p st₁ book₁ w₁) where
  older := fun s s' w h hA n hn part i => words_older arr t₁ t₂ p o s s' h hA.booked w n hn part i
  omega := fun s s' w y h hA => by
    rw [words_omega arr t₁ t₂ p o s s' h hA.booked w, hA.st]
    rfl
  w := fun s s' w c h hA => by
    rw [words_older arr t₁ t₂ p o s s' h hA.booked w s.loc.w (by rw [hA.w, hA.st]; exact hA.there),
      words_first arr t₁ t₂ o s s' hA.booked w, hA.w, hA.st, hA.book]
    rfl

end

/-! ## The fence, from the start's yes and the block's yes -/

/-- What `firstOutFrom` returns. -/
theorem firstOutFrom_is (S : Params.LinShape) (st : Statement) (book : TreeBook) (roots : ℕ)
    (w own : ℕ) (mask : Option ℕ) (pending : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pending = some f) :
    f.st = st ∧ f.book = book ∧ f.roots = roots ∧ numbersOk S f = true := by
  unfold firstOutFrom at h
  split at h
  · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨_, hn, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, hn⟩
  · cases h

/-- What the start's yes lays. -/
theorem startIs (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.st = st₁ ∧ s₀.book = book₁ ∧ (∃ g, s₀.loc.border = some ⟨g, o⟩) ∧
      s₀.book.trees.size + 1 = s₀.loc.firstTree ∧ o.st.codes = s₀.st.codes ∧
      s₀.loc.w < st₁.oracles.size := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      obtain ⟨e₁, e₂, _, hn⟩ := firstOutFrom_is S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ f hf
      split at h
      · cases h
      · rename_i s hs
        obtain rfl := Except.ok.inj h
        unfold start₃ at hs
        split at hs
        · rename_i hc
          obtain rfl := Option.some.inj hs
          simp only [Bool.and_eq_true, decide_eq_true_eq, rootsB, beq_iff_eq] at hc
          obtain ⟨⟨c₁, c₂⟩, c₃⟩ := hc
          refine ⟨e₁, e₂, ⟨_, rfl⟩, ?_, c₂.trans c₁.symm, ?_⟩
          · show f.book.trees.size + 1 = f.roots + 1
            rw [c₃]
          · show f.w < st₁.oracles.size
            unfold numbersOk at hn
            split at hn
            · rename_i x G hx hG
              rw [← e₁]
              exact (Array.getElem?_eq_some_iff.1 hx).1
            · cases hn
        · cases hs

/-- **The fence holds at the start's record and what the block makes of it**, given the two named
premises on the books. -/
theorem atStart_of_yes {Cl : Type} (p : P₁₄) (codes : Codes) (S : Params.LinShape)
    (st₁ : Statement) (book₁ : TreeBook) (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ)
    (pile₁ : List TensorRow) (o : SharedOut) (s s' : S₃)
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), book₁.place[i]? = some q → q.1 < book₁.trees.size)
    (tenant : ∀ q : ℕ × ℕ, o.book.place[o.omega]? = some q → q.2 = 0) :
    AtStart st₁ book₁ s.loc.w o s s' := by
  obtain ⟨e₁, e₂, hb, hf, hc, hw⟩ := startIs codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s h₀
  exact ⟨⟨hb, hf, hc, bookSays_k14Second p s s' rs gs h, sharp_k14Second p s s' rs gs h,
    by rw [e₂]; exact placed, tenant⟩, e₁, e₂, rfl, hw⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOn_wordsLast
#print axioms VerifiableInference.Desc.Sound.startIs
#print axioms VerifiableInference.Desc.Sound.atStart_of_yes
