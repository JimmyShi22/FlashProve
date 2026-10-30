-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/LongSym.lean: the code switch: THE LONG SYMBOL THAT IS HEARD AT A
DRAWN POSITION IS, COORDINATE BY COORDINATE, THE SYMBOL THAT STANDS AS A GENERATOR ROW's TARGET.

Long.lean's yes_long gives the long symbol at a drawn position as a slice of an array Y that stands
under "there is". HeardRows.lean's yes_rows names the array out of which the rows are made. The
library's symAtB (OnBytes/Slice/BlkCsRows.lean) is what RowsOrder.lean's switchRows_iff hands the
generator rows as their targets. Here the three are one, at one yes of the text's decide:
  YesLongSym, yes_long_sym  there are the front x, the step's result w, what the sending returned, a
                 statement S3, THE ONE ARRAY Y and the rows, with all that yes_rows says of them,
                 and at every drawn position q longAt coord … q = some fun α => readE (symAtB
                 x.f.rows (the positions) Y q (coord α)).
At coord := coordOf (Johnson/Top/H0/K2Hands/DrawJoin.lean) the right side is what RowsJoin.lean's
TieX asks of the typed statement's long symbols (its clause «symbol»). No new reasoning: yes_rows
and yes_long, joined at oldRead's one value. The sending snd and coord are letters. No soundness is
claimed.
-/
import Johnson.Top.H0.K2Hears.HeardRows
import OnBytes.Slice.BlkCsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwOut addRowsG firstBehind)

/-- **A yes of decide: what is heard is what stands as the rows' targets.** -/
def YesLongSym : Prop := ∀ (Aa : Type) (coord : Aa → Nat) snd p s r₁ r₂ gs s',
  decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (w : SwOut) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row),
    frontAt p s = some x ∧
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
    Y.size = (Positions.ofDraws p.logN r₂.drawn.poss).all.size * x.f.rows.rows ∧
    switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows ∧
    addRowsG S3 x.f.group rows = .ok w.st ∧
    ((p.stands = .link ∧ ∃ f mine, firstBehind w.st x w.out [] = .ok (s'.st, f, mine)) ∨
      (p.stands ≠ .link ∧ s'.st = w.st)) ∧
    ∀ q ∈ r₂.drawn.poss, longAt coord snd p s r₁ r₂ gs q =
      some fun α => OnBytes.Slice.readE
        (OnBytes.Slice.symAtB x.f.rows (Positions.ofDraws p.logN r₂.drawn.poss) Y q (coord α))

theorem yes_long_sym : YesLongSym := fun Aa coord snd p s r₁ r₂ gs s' h => by
  obtain ⟨x, w, y, S3, Y, rows, hx, ho, hz, hm, hl, hb⟩ := yes_rows snd p s r₁ r₂ gs s' h
  refine ⟨x, w, y, S3, Y, rows, hx, ho, hz, hm, hl, hb, fun q hq => ?_⟩
  obtain ⟨old, Y', i, ho', hi, hlong, -⟩ := yes_long Aa coord snd p s r₁ r₂ gs s' h q hq
  rw [ho] at ho'
  obtain ⟨rfl, -, rfl⟩ : x.f.rows = old ∧ True ∧ Y = Y' := by
    have e := Option.some.inj ho'
    exact ⟨congrArg (·.1) e, trivial, congrArg (·.2.2) e⟩
  rw [hlong]
  unfold OnBytes.Slice.symAtB
  rw [hi]
  rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_long_sym
