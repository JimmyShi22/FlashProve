-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/RoundsJoin.lean: THE SEVEN CLAUSES THAT NAME THE TWO ROUNDS OR THE
COLUMNS, OF THOSE THAT THE LAWS "THE KIND's OWN DECISION SAYS YES" ASK (fits₁ · vals · answers · loc
· readsOpens · noneLeft · groups: Returns/LeftAtReached.lean), IN THESE LAWS' OWN LETTERS, AT ANY
FRONT, AT THE GROUPS AS `Block.step` LAYS THEM: FROM THE TWO TESTS THAT `Block.step` RUNS IN FRONT
OF EVERY DECISION, THREE TIES OF THE PLACE's NUMBERS AND THE NAMED PREMISE `AllTied`. A short name
and three statements with their proofs: two unfoldings; calls.

  `laidGroups`      the groups as `Block.step` lays the columns: a short name
  `trees_free`      the list of opened trees hangs on the front's carried rows and the book's places
                    alone
  `tied_free`       `AllTied` reads of the positions their range alone: not the draws
  `call_seven`      THE JOIN, general in the front x, the book B and the number of roots: so it
                    serves a segment's first place, the output head's and the place behind the last
                    segment alike

By: `items_give`, `range_give`, `answers_tied`, `loc_tied`, `groups_give` (Returns/ItemsFit.lean) ·
`reads_give` (Returns/ColsFit.lean).

Limits. A JOIN: NOTHING IS PAID HERE THAT THESE TWO FILES DO NOT PAY. THE THREE TIES AND `AllTied`
ARE PREMISES: `AllTied` holds four facts on each opened tree that are the verifier's state's alone,
and three equations against the plan's list. THE SEVEN ARE NOT ON THE ROUNDS AND THE COLUMNS ALONE:
readsOpens asks these four facts; answers and loc hold the three ties. One premise more, hp: the
decision is shown the second round's positions as `Block.step` reads them. The two tests are
premises too: of a half that has played and whose columns are laid they are the frame's law
(`fits_played`, Johnson/Desc/ProofFile/Honest/Law/Cut.lean), not called here. This file's imports
are heavy (Returns/CallJoin.lean). Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.CallJoin
import Johnson.Desc.K2.Honest.Returns.ItemsFit
import Johnson.Desc.K2.Honest.Returns.ColsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit regroup groupsOf)
open VerifiableInference.Desc.First.K2 (P2 rounds par9 flat locOk behindArgs)
open _root_.Tw.K2 (Front Col)

/-- The groups as `Block.step` lays the columns. -/
abbrev laidGroups (p : P2) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn) :
    List (List (Nat × List UInt64)) :=
  regroup ((groupsOf ft (rounds p) [d₁, d₂]).map (·.length)) cols

/-- The opened trees hang on the front's carried rows and the book's places alone: not on the
place's numbers, on what the sending returns, on a round or on a column. -/
theorem trees_free (P P' : _root_.Tw.K2.Par9) (x : Front) (B : TreeBook)
    (y y' : _root_.Tw.K2.Sent) (rL rL' : Fmt.RoundView) (cols cols' : List OpenedColumn) :
    treesOf (inFront P x B y rL cols) = treesOf (inFront P' x B y' rL' cols') := rfl

/-- The named premise reads of the positions their range alone: not the draws. -/
theorem tied_free (S : Statement) (ft logN : Nat) (d d' : List Nat) (B0 : TreeBook) :
    ∀ (ts : List Nat) (rd : List (Nat × Nat × Nat)),
      AllTied S ft (Positions.ofDraws logN d) B0 ts rd →
      AllTied S ft (Positions.ofDraws logN d') B0 ts rd
  | [], [], h => h
  | [], _ :: _, h => h
  | _ :: _, [], h => h
  | _ :: ts, _ :: rd, h => ⟨h.1, tied_free S ft logN d d' B0 ts rd h.2⟩

/-- **THE JOIN.** d₁, d₂: the two challenges as `Block.step` reads them; r₁, r₂: the rounds as the
decision is shown them. c: the old main code. -/
theorem call_seven (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView) (c : Code)
    (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn) (hp : d₂.poss = r₂.drawn.poss)
    (hrf : roundsFit (rounds p) [r₁, r₂] = true)
    (hc : cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf ft (rounds p) [d₁, d₂]).flatMap id)
    (t1 : (sendingAt p x).answers = p.answers) (t2 : p.logN = c.logN) (t3 : 0 < p.positions)
    (hT : AllTied x.st p.firstTree (Positions.ofDraws c.logN r₂.drawn.poss) B
      (treesOf (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols)))) p.read) :
    _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true ∧ r₁.vals = [] ∧
      (K1.answersIn (K1.cutTo (sendingAt p x) r₂)).length = (sendingAt p x).answers ∧
      locOk (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂
        (flat p (laidGroups p ft d₁ d₂ cols))) c.logN = true ∧
      AllOpen (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))).st
        (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))).firstTree
        (Positions.ofDraws c.logN r₂.drawn.poss)
        (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))).book
        (treesOf (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))))
        (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))).opened ∧
      leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) B
        (treesOf (callIn p x B roots r₁ r₂ (flat p (laidGroups p ft d₁ d₂ cols))))
        (flat p (laidGroups p ft d₁ d₂ cols)) = [] ∧
      (laidGroups p ft d₁ d₂ cols).length = p.read.length := by
  obtain ⟨f1, v1, -⟩ := items_give p r₁ r₂ hrf
  have hin : ∀ q ∈ d₂.poss, q < 2 ^ c.logN := by
    rw [hp, ← t2]
    exact range_give p r₁ r₂ hrf
  rw [← hp] at hT ⊢
  obtain ⟨R1, R2⟩ := reads_give x.st p ft c.logN d₁ d₂ hin B _ cols hT hc
  exact ⟨f1, v1, answers_tied p _ r₁ r₂ t1 hrf, loc_tied p x _ r₁ r₂ _ c.logN t1 t2 t3 hrf, R1, R2,
    groups_give p ft d₁ d₂ cols⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.trees_free
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tied_free
#print axioms VerifiableInference.Desc.K2.Honest.Returns.call_seven
