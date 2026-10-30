-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptAtClosing.lean: the kind "the code switch" (K2): WHAT THE
CLOSING's KEPT MEMBER IS: where the closing as the kind's lot lays it (`lotClosingAt`,
Honest/K2/Exact.lean) returns W, and the segments in front of the place are A and then Sg: the main
entries of W's kept member number a, inside its rows and the code's length, are those of the rows
that the closing has laid anew of Sg's group, at the kept member's number in that group. Two
statements with their proofs; no definition.

  `foldEnd_kept_main`  the fold's end hands a kept member's main entries on as they are
  `kept_at_closing`    THE END

By, each called once: `lotClosingAt_inv` (Honest/K2/Law/CopyAtClosing.lean): the return comes of the
walk over the segments · `closingFrom_last` (Honest/K2/Law/ClosingLast.lean): the walk's last step
is `segmentLeft` at Sg · `segmentLeft_inv` (Honest/K2/Law/SegmentLeftInv.lean): what that returns ·
`frozen_kept` (Honest/K2/Law/ClaimFrozen.lean): what is kept in arrays is what the fold left, in
range. `keptNo`, `shapeOf`: abbreviations of Johnson/Desc/K2/Honest/Carry/OfRows.lean.

Limits. A SECOND LINK OF A LONGER CHAIN, behind Honest/K2/Law/CopyTxt.lean. ROWS AGAINST A TABLE: it
names the rows R that the closing laid anew: NOT the sender's own rows: that these are one is
`copy_at_closing`'s end (CopyAtClosing.lean), under premises on the book, the data and the
challenges. hW IS A PREMISE: where the closing does not return nothing is said. hA: the last segment
in front is named; a place with no segment in front is not spoken of. TWO DEFAULTS STAND IN THE END:
`R.rows.getD` reads a message of zeros beyond the list, and `shapeOf` an empty shape beyond the
members: that the kept member's number lies inside both is not said here. In range alone: a below
the number of kept members, b below the member's main rows, j below the code's length. k: the
carried stretches, a letter. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingLast
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentLeftInv
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimFrozen
import Johnson.Desc.K2.Honest.Carry.OfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left GroupMember foldEnd)

/-- **The fold's end hands a kept member's main entries on as they are.** -/
theorem foldEnd_kept_main (codes : OnBytes.Codes) (code maskCode : Nat) (ms : List GroupMember)
    (M : Nat → Johnson.Prover.Send.Rows) (fresh : Johnson.Prover.Send.Rows)
    (γ : List Cb.Gl.E) (a : Nat) :
    ((foldEnd codes code maskCode ms M fresh γ).kept a).main =
      (M (VerifiableInference.Desc.K2.Honest.keptNo ms a)).main
        ((VerifiableInference.Desc.K2.Honest.shapeOf ms
          (VerifiableInference.Desc.K2.Honest.keptNo ms a)).mainDeg == 3) :=
  rfl

/-- **WHAT THE CLOSING's KEPT MEMBER IS.** y: what the walk over A returns. R: the rows that the
closing has laid anew of Sg's group. kept: the shapes of that group's kept members. -/
theorem kept_at_closing {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (hW : lotClosingAt lay segs p D Rd heard k = .ok W) {A : List SegmentPub} {Sg : SegmentPub}
    (hA : segs.take p.link = A ++ [Sg]) :
    ∃ (y : Option (Left × List OnBytes.OracleShape) × Nat) (R : GroupRows)
      (kept : List OnBytes.OracleShape),
      closingFrom freshTable (lotOwn segs p D Rd heard) heard k A 0 0 none = .ok y ∧
      segmentGroupRows freshTable Sg (y.1.map (·.1)) ((y.1.map (·.2)).getD [])
        (lotOwn segs p D Rd heard (0 + A.length)) k y.2 true = .ok R ∧
      kept = (R.members.filter (·.kept)).map (·.shape) ∧
      ∀ a b j, a < kept.length → b < (kept.getD a {}).mainRows →
        j < (Sg.sizes.codes.base.getD Sg.sizes.code default).ell →
        (W.kept a).main b j =
          (R.rows.getD (VerifiableInference.Desc.K2.Honest.keptNo R.members a) zeroMessage).main
            ((VerifiableInference.Desc.K2.Honest.shapeOf R.members
              (VerifiableInference.Desc.K2.Honest.keptNo R.members a)).mainDeg == 3) b j := by
  obtain ⟨x, kept, hx, ex⟩ := lotClosingAt_inv hW
  rw [hA] at hx
  obtain ⟨y, Wk, hy, hs, e2, -⟩ := closingFrom_last hx
  obtain rfl : Wk = (W, kept) := Option.some.inj (e2.symm.trans ex)
  obtain ⟨R, hR, hk, hWe⟩ := segmentLeft_inv hs
  refine ⟨y, R, kept, hy, hR, hk, fun a b j ha hb hj => ?_⟩
  rw [hWe, frozen_kept _ _ _ _ a b j ha hb hj, foldEnd_kept_main]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.foldEnd_kept_main
#print axioms ProofFile.Honest.K2.Law.kept_at_closing
