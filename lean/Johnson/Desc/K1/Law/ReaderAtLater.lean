-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ReaderAtLater.lean: the premise "reader" of PileBackAtLater
(Johnson/Desc/K1/Law/PileAtLater.lean) is paid at both blocks of a segment's later places, at the
reader through the state's own book (rwBook, Johnson/Desc/K13/Law/ReaderByBook.lean); so there the
item "pile" goes back.

  k1Quiet_book     the quiet block behind the reads' sending leaves the statement and the book.
  ReaderAtLater, readerAtLater   the statement and its proof: at the digits' block it is
                   readerAtCommit (Johnson/Desc/K13/Law/ReaderAtCommit.lean); at the reads' block
                   that, then rwBook_same over the quiet block.
  pileBack_book    the two together: RowsTrue at rwBook goes back over a yes on two rounds.

What is not claimed. The four premises on the chain's state in front: they are the statement's own.
That the composed meaning's letter rw13 is rwBook. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K13.Law.ReaderAtCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook rwBook_same readerAtCommit)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

theorem k1Quiet_book (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => s'.st = s.st ∧ s'.book = s.book) (k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · have f := K8.ReadsQuiet.layers_frame h
    exact ⟨f.2.2.1, f.2.2.2.1⟩
  · have f := K8.ReadsQuiet.head_frame h
    exact ⟨f.2.2.1, f.2.2.2.1⟩
  · obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
    exact ⟨rfl, rfl⟩

/-- **THE READER's PAYER AT A SEGMENT's LATER PLACES.** x, x': the chain's states in front of and
behind a yes on two rounds. The four premises are had from the promise in front. -/
def ReaderAtLater : Prop :=
  ∀ (B own : Block S Unit), Later B own → ∀ {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (x x' : Pp × S) (w : Desc.Wit Cells Tok MsgT)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    B.decide x.2 [r₁, r₂] gs = .ok x'.2 →
    pileMasksC x.2 = true → x.2.out.indexMasks < x.2.st.oracles.size →
    x.2.book.place.size = x.2.st.oracles.size →
    (∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) →
    RowsTrue (rwBook arr mat x') x'.2 w → RowsTrue (rwBook arr mat x) x'.2 w

theorem readerAtLater : ReaderAtLater := by
  intro B own hB Pp Cells Tok nR k arr mat x x' w r₁ r₂ gs h hOn hlt hsz htree hT
  cases hB with
  | digits q gp l piece digits =>
    exact readerAtCommit arr mat _ l 2 digits x x' w r₁ r₂ gs h hOn hlt hsz htree hT
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide x.2
        ([r₁, r₂].take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          ([r₁, r₂].drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) =
          .ok x'.2 := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    have h1' : (commitAtS (parLater G.first (gpOf Z) l pr 1) l 1 reads : Block S Unit).decide x.2
        [r₁, r₂] _ = .ok s₁ := h1
    obtain ⟨e1, e2⟩ := k1Quiet_book G l X _ _ _ _ h2
    have er : x'.2.rows = s₁.rows := k1Quiet_rows G l X _ _ _ _ h2
    have ew : rwBook arr mat x' w = rwBook arr mat (x.1, s₁) w :=
      rwBook_same arr mat (x.1, s₁) x' e2 (by rw [e1]) (fun o => by rw [e1]) w
    have hT₁ : RowsTrue (rwBook arr mat (x.1, s₁)) s₁ w := fun r hr => by
      rw [← ew]
      exact hT r (by rw [er]; exact hr)
    have hgo := readerAtCommit arr mat _ l 1 reads x (x.1, s₁) w r₁ r₂ _ h1' hOn hlt hsz htree hT₁
    exact fun r hr => hgo r (by rw [← er]; exact hr)

/-- **"Pile" goes back at the reader through the state's own book.** -/
theorem pileBack_book {B own : Block S Unit} (hB : Later B own) {Pp Cells Tok : Type} {nR k : ℕ}
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin k → Bool) → GE) (x x' : Pp × S)
    (w : Desc.Wit Cells Tok MsgT) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : B.decide x.2 [r₁, r₂] gs = .ok x'.2) (hOn : pileMasksC x.2 = true)
    (hlt : x.2.out.indexMasks < x.2.st.oracles.size)
    (hsz : x.2.book.place.size = x.2.st.oracles.size)
    (htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size)
    (hT : RowsTrue (rwBook arr mat x') x'.2 w) : RowsTrue (rwBook arr mat x) x.2 w :=
  pileBackAtLater B own hB (rwBook arr mat) x x' w _ gs h
    (readerAtLater B own hB arr mat x x' w r₁ r₂ gs h hOn hlt hsz htree) hT

end VerifiableInference.Desc.K1
