-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/NewAtYes.lean: code switching (the kind K2): WHERE THE NEW MESSAGES OF A
SWITCH's SENDING SIT AND OF WHICH SHAPE THEY ARE, IN THE VERIFIER's STATE BEHIND AN ACCEPT: in the
form in which a reader of the witness's words takes them (the book's place · the tree at that
place · the tree's number through the file · the message's shape). A joining of what lies. NO
BLOCK IMPORTS THIS FILE.
  yes_new_seat    an accept of the decision: there are the front x and the layout lay of what the
                  sending announces, and for every i below the number of the notices: the book
                  behind places message n0 + i at (the trees in front + lay's tree of i, lay's
                  part of i); a tree T stands there; T.number = p.firstTree + (s.roots + lay's
                  tree of i)
  yes_new_shape   at AtYes: message n0 + i of the statement behind has the shape of notice i
For the tie between «what a row says of words» and the law's relation behind (the words are the
typed messages at the typed entries' names). CALLED: yes_seated (K2C/SeatedAt.lean) · AtYes'
fields (K2Hears/Whole.lean). THE TABLE OF CODES: K2.yes_codes (K2C/KeepsWhole.lean) lies:
s'.st.codes = s.st.codes. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SeatedAt
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8 switchNotices)

theorem yes_new_seat {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay), FrontOf p s x ∧
      layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
      ∀ i, i < (switchNotices x.T x.others).size → ∃ T : Tree,
        s'.book.place[x.st.oracles.size + i]? =
          some (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) ∧
        s'.book.trees[s.book.trees.size + lay.tree.getD i 0]? = some T ∧
        T.number = p.firstTree + (s.roots + lay.tree.getD i 0) := by
  obtain ⟨x, lay, hF, hlay, _, St⟩ := yes_seated h
  refine ⟨x, lay, hF, hlay, fun i hi => ?_⟩
  obtain ⟨T, hT, _, hn, _⟩ := St.made (lay.tree.getD i 0) (St.fits i hi).1
  exact ⟨T, St.new i hi, hT, hn⟩

theorem yes_new_shape {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (i : Nat) :
    (s'.st.oracles[x.st.oracles.size + i]?).map (·.shape) =
      ((switchNotices x.T x.others)[i]?).map (·.shape) := by
  rw [A.tables.shape, A.same.shape]
  exact A.sent.shape i

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_new_seat
#print axioms VerifiableInference.Desc.First.K2.yes_new_shape
