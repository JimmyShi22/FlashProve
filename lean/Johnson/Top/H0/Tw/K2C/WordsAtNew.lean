-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/WordsAtNew.lean: code switching (the kind K2): AT THE NEW SENDING's TYPED
ENTRIES THE TABLE OF JOINTS' READER OF THE WITNESS's WORDS GIVES THE TYPED MESSAGES' ENTRIES. For
the tie between «what a row says of words» and the law's relation behind (the premise hm of
rowsHoldT_of_says, Johnson/Top/H0/K2Caller/RowsSay.lean). NO BLOCK IMPORTS THIS FILE. st, book:
the statement and the book of the verifier's state behind the switch. n0: the number of oracle
messages in front. seat i: the tree (its number through the file) and the part at which the typed
list's member i sits.
  IdxReads cs      THE ARITHMETIC, AS A NAMED PREMISE: at a message of the shape s the words that
                   tables give (wordsOn, Johnson/Desc/Means/ItemsTab.lean), at the table and index
                   of a typed coordinate (coordAt, Johnson/Top/H/SwitchNames.lean), are the
                   table's entry at that coordinate's row and place. It is typed in
                   K2Caller/IdxReadsPaid.lean; here it is spent.
  tab_at_new       the reader's table of message n0 + i (tabAt,
                   Johnson/Desc/Sound/TabAt.lean) is the witness's one accessor Wit.tab at the
                   typed member's shape and seat
  words_at_new     (sigOf cs l).ents (msgsOf cs l seat arr w) n = wordsFirst arr st book w (n0 +
                   (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2
  seat_by_new      the premise on the seats, from what an accept of the switch gives
                   (yes_new_seat, K2C/NewAtYes.lean): seatBy noFirst s'.book (n0 + i) = some
                   (p.firstTree + (s.roots + lay's tree of i), lay's part of i)
PREMISES of words_at_new: st.codes = cs · the book seats message n0 + i at seat i · st has the
typed member's shape at n0 + i · IdxReads cs. No soundness is claimed.
-/
import Johnson.Desc.Sound.WordsAt
import Johnson.Top.H.SwitchNames
import Johnson.Top.H0.Tw.K2C.NewAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT msgsOf tabAt seatBy noFirst wordsFirst wordsBy
    seatBy_some)
open _root_.Tw.K2 (sendByL8 switchNotices)

/-- The arithmetic between a typed coordinate and the index in its table. -/
def IdxReads (cs : Codes) : Prop :=
  ∀ (S : Statement) (T : Nat → Bool → Nat → Nat → GE) (o : Nat) (s : OracleShape),
    (S.oracles[o]?).map (·.shape) = some s →
    ∀ j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell),
      wordsOn S T o (coordAt cs s j).1 (coordAt cs s j).2 =
        Sum.elim (fun q => T o false q.1.val q.2.val) (fun q => T o true q.1.val q.2.val) j

variable {Cells Tok : Type}

theorem tab_at_new (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (st : Statement) (book : TreeBook) (n0 : ℕ)
    (i : Fin l.length) (hseat : seatBy noFirst book (n0 + i.val) = some (seat i))
    (hshape : (st.oracles[n0 + i.val]?).map (·.shape) = some (l.get i).1) :
    tabAt cs arr (seatBy noFirst book) st w (n0 + i.val) =
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 := by
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 hshape
  unfold tabAt
  rw [hseat, hx]
  simp only
  rw [e]

theorem words_at_new (cs : Codes) (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) (st : Statement) (book : TreeBook) (n0 : ℕ)
    (hc : st.codes = cs)
    (hseat : ∀ i : Fin l.length, seatBy noFirst book (n0 + i.val) = some (seat i))
    (hshape : ∀ i : Fin l.length, (st.oracles[n0 + i.val]?).map (·.shape) = some (l.get i).1)
    (hiv : IdxReads cs) (n : (sigOf cs l).Ent) :
    (sigOf cs l).ents (msgsOf cs l seat arr w) n =
      wordsFirst arr st book w (n0 + (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 := by
  obtain ⟨i, j⟩ := n
  show msgsOf cs l seat arr w i j =
    wordsOn st (tabAt st.codes arr (seatBy noFirst book) st w) (n0 + i.val)
      (coordAt cs (l.get i).1 j).1 (coordAt cs (l.get i).1 j).2
  rw [hiv st _ (n0 + i.val) (l.get i).1 (hshape i) j, hc,
    tab_at_new cs l seat arr w st book n0 i (hseat i) (hshape i)]
  change (Fin (l.get i).1.mainRows × Fin (pMain cs (l.get i).1).ell) ⊕
    (Fin (l.get i).1.maskRows × Fin (pMask cs (l.get i).1).ell) at j
  rcases j with q | q <;> rfl

theorem seat_by_new {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay), FrontOf p s x ∧
      layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
      ∀ i, i < (switchNotices x.T x.others).size →
        seatBy noFirst s'.book (x.st.oracles.size + i) =
          some (p.firstTree + (s.roots + lay.tree.getD i 0), lay.part.getD i 0) := by
  obtain ⟨x, lay, hF, hlay, H⟩ := yes_new_seat h
  refine ⟨x, lay, hF, hlay, fun i hi => ?_⟩
  obtain ⟨T, h1, h2, h3⟩ := H i hi
  rw [seatBy_some noFirst s'.book _ _ T h1 h2]
  show some (T.number, _) = _
  rw [h3]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.tab_at_new
#print axioms VerifiableInference.Desc.First.K2.words_at_new
#print axioms VerifiableInference.Desc.First.K2.seat_by_new
