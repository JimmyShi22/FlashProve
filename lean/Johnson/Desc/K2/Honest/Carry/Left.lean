-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/Left.lean: WHAT THE FOLD THAT CLOSED A GROUP LEFT, OF WORDS: AT THE
CARRIED ROWS' OWN LAYOUT. The term of which `carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean)
is made, in a file of its own: none of its Lean terms is a state, a way in, a front or a witness;
the letter w stands for whatever words a caller hands, a witness's among them. Definitions; one
equation by unfolding; and what the claim reads.

  `rowsOfWords` a message in full, as far as words have it: read in the extension field; THE TAILS
                    ARE 0: NOT A PROVER's ROWS: for texts that read no tail
  `membersAt` the closed group's members, as the carried rows' layout names them, in the order of
                    sending: each with its shape, read in the extension field, and its flag "kept"
  `foldEnd_eq_at` `foldEnd` is `foldEndAt` at the layout that it makes (both:
                    Johnson/Desc/K2/Honest/FoldEnd.lean): by its definition
  `leftAt` what the fold that closed the group left, of the words: `foldEndAt` AT THE CARRIED ROWS'
                    OWN LAYOUT: the layout at which the carried rows' claim was made
  `claimTrue_congr` `ClaimTrue` (Johnson/Desc/K2/Honest/Inner/Statement.lean) reads of what a fold
                    left the main row below the code's length, the two mask rows below the mask
                    code's, and each kept member's table: NO TAIL

NEAR, NOT CALLED: the library's `TieLeft` (Johnson/Prover/Link/CarryingTie.lean): a premise there:
what a fold leaves is the folded full message, entry by entry: at a switch inside a proximity test,
with no kept member.

Limits. An honest prover's closing folds by `foldEnd`, which makes the layout anew: THAT THE TWO
LAYOUTS ARE ONE IS NOT PROVED HERE. That the layout's lists are as long as its members' list, and
that it fits the members' shapes, is not asked. `rowsOfWords` HAS NO GUARD AT ROWS BEYOND A
MESSAGE's REAL ONES: the members are read at real rows alone; THE MASK SENT AHEAD IS READ AT EVERY
ROW BELOW 2 ^ h: that `leftAt` is the fold of the words' rows is safe where that mask has at least 2
^ h mask rows (enough; whether it is needed is not settled); the program's test on it asks just 2 ^
h (`foldMaskOk`, OnBytes/Iop/Fold.lean). Tails are laid 0, and `foldEndAt` folds these zeros into
the tails of what it leaves: so `leftAt`'s tails are no prover's. `ClaimTrue` reads no tail. That
`foldMsg` is the program's fold is not proved here. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.FoldEnd
import Johnson.Desc.K2.Honest.Inner.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt)
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows)

/-- A message in full, as far as words have it: read in E; no tail. The tails are 0 here: not a
prover's rows: for texts that read no tail. -/
def rowsOfWords (w : Words GE) (o : Nat) (s : OracleShape) : Rows where
  mainE := fun r j => w o .main (r + j * 2 ^ ceilLog2 s.mainRows)
  mainF := fun _ _ => 0
  mainTlE := fun _ _ => 0
  mainTlF := fun _ _ => 0
  mask := fun r j => w o .mask (r + j * 2 ^ ceilLog2 s.maskRows)
  maskTl := fun _ _ => 0

/-- The closed group's members, as the carried rows' layout names them, in the order of sending:
each with its shape at S, READ IN E, and its flag "kept". -/
def membersAt (S : Statement) (old : SingleRows) : List GroupMember :=
  (old.layout.members.zip old.layout.kept).toList.map fun p =>
    ⟨{ (S.oracles.getD p.1 default).shape with mainDeg := 3 }, p.2⟩

/-- `foldEnd` is `foldEndAt` at the layout that it makes: by its definition. -/
theorem foldEnd_eq_at (codes : Codes) (code maskCode : Nat) (ms : List GroupMember)
    (M : Nat → Rows) (fresh : Rows) (γ : List Cb.Gl.E) :
    foldEnd codes code maskCode ms M fresh γ =
      foldEndAt (groupLayout codes code maskCode ms) codes code maskCode ms M fresh γ := rfl

/-- **What the fold that closed the group left, of the words w**: AT THE CARRIED ROWS' OWN
LAYOUT. -/
def leftAt (S : Statement) (old : SingleRows) (w : Words GE) : Left :=
  foldEndAt old.layout S.codes old.code old.maskCode (membersAt S old)
    (fun i => rowsOfWords w (old.layout.members.getD i noId)
      (S.oracles.getD (old.layout.members.getD i noId) default).shape)
    (rowsOfWords w old.fresh (S.oracles.getD old.fresh default).shape)
    (old.gamma.map readE)

/-- **What the claim reads of what a fold left.** -/
theorem claimTrue_congr (Z : Sizes) (old : SingleRows) (W W' : Left)
    (h1 : ∀ j, j < (Z.codes.base.getD Z.code default).ell → W.main j = W'.main j)
    (h2 : ∀ a i, (W.kept a).entryIn (Z.kept.getD a {}) i = (W'.kept a).entryIn (Z.kept.getD a {}) i)
    (h3 : ∀ r i, r < 2 → i < (Z.codes.mask.getD Z.maskCode default).ell →
      W.mask r i = W'.mask r i) :
    ClaimTrue Z old W ↔ ClaimTrue Z old W' := by
  have e1 : (∑ j ∈ Finset.range (Z.codes.base.getD Z.code default).ell,
      formAt old.c j * W.main j) =
      ∑ j ∈ Finset.range (Z.codes.base.getD Z.code default).ell, formAt old.c j * W'.main j :=
    Finset.sum_congr rfl fun j hj => by rw [h1 j (Finset.mem_range.1 hj)]
  have e3 : (∑ r ∈ Finset.range 2,
      ∑ i ∈ Finset.range (Z.codes.mask.getD Z.maskCode default).ell,
        readE ((old.d.getD r #[]).getD i zeroE) * W.mask r i) =
      ∑ r ∈ Finset.range 2, ∑ i ∈ Finset.range (Z.codes.mask.getD Z.maskCode default).ell,
        readE ((old.d.getD r #[]).getD i zeroE) * W'.mask r i :=
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun i hi => by
      rw [h3 r i (Finset.mem_range.1 hr) (Finset.mem_range.1 hi)]
  unfold ClaimTrue
  simp only [e1, e3, h2]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.rowsOfWords
#print axioms VerifiableInference.Desc.K2.Honest.membersAt
#print axioms VerifiableInference.Desc.K2.Honest.foldEnd_eq_at
#print axioms VerifiableInference.Desc.K2.Honest.leftAt
#print axioms VerifiableInference.Desc.K2.Honest.claimTrue_congr
