-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameBook.lean: the link's frame's steps leave the book of trees and the number
of roots: the frame's share of an invariant of the record that is handed on block by block.

  laid_book, openedAtt_book, openedLay_book, openedZero_book, cleared_book, tailHead_book
                  t.book = s.book
  laid_roots, openedAtt_roots, openedLay_roots, openedZero_roots, cleared_roots
                  t.roots = s.roots
  BookSentence, bookSentence   any sentence on the book and the number of roots rides over each

Limits. Who pushes a tree, and under which number, is the sending blocks' laws' to say. No
soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (tailHead)

theorem laid_book {m : Nat} {s t : S} (h : layFront m s = .ok t) : t.book = s.book := by
  rw [(laidAdds m s t h).1]

theorem openedAtt_book {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : t.book = s.book :=
  (openedAttGives P s t h).2.2.1.2.2.2.1

theorem openedLay_book {P : LayPar} {s t : S} (h : openLay P s = .ok t) : t.book = s.book :=
  (openedLayGives P s t h).2.2.1.2.2.2.1

theorem openedZero_book {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : t.book = s.book :=
  (openedZeroGives P fvs kCol s t h).2.2.1.2.2.2.1

theorem cleared_book {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S} (h : clearWith X counts left row s = .ok t) : t.book = s.book :=
  (Law.clear_carries h).2.1

theorem tailHead_book {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : tailHead X lay lin s = .ok t) : t.book = s.book := cleared_book h

theorem laid_roots {m : Nat} {s t : S} (h : layFront m s = .ok t) : t.roots = s.roots := by
  rw [(laidAdds m s t h).1]

theorem openedAtt_roots {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : t.roots = s.roots :=
  (openedAttGives P s t h).2.2.1.2.2.2.2.1

theorem openedLay_roots {P : LayPar} {s t : S} (h : openLay P s = .ok t) : t.roots = s.roots :=
  (openedLayGives P s t h).2.2.1.2.2.2.2.1

theorem openedZero_roots {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) : t.roots = s.roots :=
  (openedZeroGives P fvs kCol s t h).2.2.1.2.2.2.2.1

theorem cleared_roots {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : t.roots = s.roots :=
  (Law.clear_carries h).2.2.1

/-- **Any sentence on the book and the number of roots rides over the frame's steps.** -/
def BookSentence : Prop :=
  ∀ (Q : TreeBook → Nat → Prop) (s t : S), Q s.book s.roots →
    ((∃ m, layFront m s = .ok t) ∨ (∃ P, openAtt P s = .ok t) ∨ (∃ P, openLay P s = .ok t) ∨
      (∃ P fvs kCol, openLayZero P fvs kCol s = .ok t) ∨
      (∃ X counts left row, clearWith X counts left row s = .ok t)) → Q t.book t.roots

theorem bookSentence : BookSentence := by
  intro Q s t hq h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · rwa [laid_book h, laid_roots h]
  · rwa [openedAtt_book h, openedAtt_roots h]
  · rwa [openedLay_book h, openedLay_roots h]
  · rwa [openedZero_book h, openedZero_roots h]
  · rwa [cleared_book h, cleared_roots h]

#print axioms bookSentence
#print axioms tailHead_book

end Johnson.Desc.First.Walk.Tied
