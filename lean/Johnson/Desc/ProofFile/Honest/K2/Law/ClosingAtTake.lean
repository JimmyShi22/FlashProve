-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingAtTake.lean: the kind "the code switch" (K2): WHERE THE
CLOSING's WALK OVER THE FIRST m + 1 OF A LIST OF SEGMENTS RETURNS, ITS LAST STEP IS TAKEN AT THE
SEGMENT NUMBER m, WITH A FOLD IN FRONT JUST WHERE m IS NOT 0. One statement with its proof: calls;
no definition.

  `closingFrom_take` `segs[m]? = some Sg` · `closingFrom table own heard k (segs.take (m + 1)) 0 0
                    none = .ok x` ⊢ there are y, W, kept and R with: the walk over `segs.take m`
                    from the start returns y · x hands (W, kept) on · `y.1.isSome = (m != 0)` · AT
                    prev := `y.1.map (·.1)`, prevKept := `(y.1.map (·.2)).getD []`, base := `y.2`:
                    `segmentLeft table Sg prev prevKept (own (0 + m)) heard k base = .ok (W, kept)`
                    · `segmentGroupRows table Sg prev prevKept (own (0 + m)) k base true = .ok R`

What it is for. The laws `link_members_front`, `head_members_front`, `fin_members_front`
(Law/MembersJoin.lean) ask that Sg is the written segment of a number and that a fold stands in
front just where the number is not 0. A switch's place calls the walk at `segs.take p.link`: at
p.link = m + 1 this law hands both over, with the return of `segmentLeft` of which
`claimTrue_at_segmentLeft` (Law/ClaimAtClosing.lean) speaks.

By: `closingFrom_last` (Law/ClosingLast.lean) · `segmentLeft_inv` (Law/SegmentLeftInv.lean). NEAR,
NOT CALLED: `closing_lays_at` (Law/ClosingPasses.lean) at the two lengths m and m + 1 ends in this
law's last clause alone.

Limits. The join with these laws is not typed here; nor which p.link stands at which number of the
chain. Where the walk refuses nothing is said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingLast
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentLeftInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left foldEnd)

/-- **WHERE THE WALK OVER THE FIRST m + 1 SEGMENTS RETURNS**: the walk over the first m returns some
y; the last step is `segmentLeft` at the segment number m, at what y hands on: a fold just where m
is not 0; and that step's rows were made. -/
theorem closingFrom_take {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {segs : List SegmentPub} {m : Nat}
    {Sg : SegmentPub} (hSg : segs[m]? = some Sg)
    {x : Option (Left × List OnBytes.OracleShape) × Nat}
    (h : closingFrom table own heard k (segs.take (m + 1)) 0 0 none = .ok x) :
    ∃ (y : Option (Left × List OnBytes.OracleShape) × Nat) (W : Left)
      (kept : List OnBytes.OracleShape) (R : GroupRows),
      closingFrom table own heard k (segs.take m) 0 0 none = .ok y ∧
      x.1 = some (W, kept) ∧ y.1.isSome = (m != 0) ∧
      segmentLeft table Sg (y.1.map (·.1)) ((y.1.map (·.2)).getD []) (own (0 + m)) heard k y.2 =
        .ok (W, kept) ∧
      segmentGroupRows table Sg (y.1.map (·.1)) ((y.1.map (·.2)).getD []) (own (0 + m)) k y.2 true =
        .ok R := by
  have hlt : m < segs.length := (List.getElem?_eq_some_iff.1 hSg).1
  have e : segs.take (m + 1) = segs.take m ++ [Sg] := by
    rw [List.take_add_one, hSg]
    rfl
  rw [e] at h
  obtain ⟨y, W, hA, hW, hx, hy⟩ := closingFrom_last h
  have hl : (segs.take m).length = m := by
    rw [List.length_take]
    omega
  rw [hl] at hW
  obtain ⟨R, hR, -, -⟩ := segmentLeft_inv (W := W.1) (kept := W.2) hW
  refine ⟨y, W.1, W.2, R, hA, hx, ?_, hW, hR⟩
  rw [hy]
  cases m with
  | zero => rfl
  | succ n =>
    cases segs with
    | nil => exact absurd hlt (by simp)
    | cons a l => rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingFrom_take
