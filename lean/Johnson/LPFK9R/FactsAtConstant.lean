-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/FactsAtConstant.lean: FOUR OF THE FACTS ON THE PLAN THAT THE LIST OF WHAT IS LEFT OF
A LINK's LAW ASKS (Johnson/Desc/First/Link/Law/LinkList.lean: hn · hdue · hrw · hpc), AT THE
CLOSED CONSTANT
(`P5J.AtMgA`), IN THE FIELDS' VERY FORMS: so that the ties t3_eq_all | t3_eq_rows
and
the law's premises hR1, hR2, hR3 are not idle there for a false number. Theorems.

What is said.
  `listed_full`: a closed fact on the table and the written list, BY THE KERNEL: behind the one
    equation's sub-protocol of link m < 25 the open classes of rows of segment m that lie in the
    group's list are "carried", "position", "equation", in this order; at m = 0 "equation" alone.
  `due_of_plan`: for numbers whose rowsAt is the plan's (rowsAtPlan, Johnson/Desc/First/
    RowsAtPlan.lean) at 25 segments: the count of rows due there is the equation's place and one.
  `hn_at`: **hn**: the class "equation" of segment m has a row (just one).
  `hdue_at`: **hdue**, at k := batchAt fullLinks At.ps m.
  `hrw_at`: **hrw**: the constant's letter rw at m IS the test K9.rowsFit at the rows of the numbers
    p that kind K9's lot reads off the plan (IM.k9At Zp m = some p): rwAt_of_rows.

  `hpc_at`: **hpc**: 7 + shift (subAt m) is the piece of the lookup on the digits at link m: in
    scope the head's link is number 24 (headLink_scope, at the head's own fields).

Limits. AT THE CONSTANT's OWN NUMBERS (At.N Zp cF), whatever Zp and cF are; hpc alone spends the
scope. They
say that the NUMBERS fit each other and the table; nothing on any state. Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.IMR.LinkSeat
import Johnson.Desc.First.Link.Law.EqNumbersOf
import Johnson.Desc.First.Link.Law.K9KindTiedR
import Johnson.Desc.First.Look.K03PlanOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S ModelPart Item RowClass Numbers start openSets rowsDue rowsAtPlan
  carriedRows)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (batchAt listedOf rowsDue_listed)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open P5J (AtMgA fullLinks)

set_option maxRecDepth 1000000 in
/-- Which classes of rows of segment m are open behind its one equation. -/
theorem listed_full : ∀ m < 25,
    listedOf ((openSets fullLinks P5J.At.ps (start fullLinks))[batchAt fullLinks P5J.At.ps m + 1 +
      1 + 1]?.getD []) m =
      if m = 0 then [.equation] else [.carried, .position, .equation] := by decide +kernel

/-- The count of rows due there, for numbers whose rowsAt is the plan's. -/
theorem due_of_plan (N N₀ : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ)
    (hN : N.rowsAt = rowsAtPlan s t N₀ 25) (m : ℕ) (hm : m < 25) :
    rowsDue N ((openSets fullLinks P5J.At.ps (start fullLinks))[batchAt fullLinks P5J.At.ps m + 1 +
      1 + 1]?.getD []) m = (N.rowsAt m .equation).1 + 1 := by
  have hne : (m == 25) = false := by simpa using Nat.ne_of_lt hm
  rw [rowsDue_listed, listed_full m hm, hN]
  by_cases h0 : m = 0
  · subst h0
    simp [rowsAtPlan, carriedRows]
  · have hz : (m == 0) = false := by simpa using h0
    rw [if_neg h0]
    simp [rowsAtPlan, hne, hz]
    omega

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The constant's numbers' rowsAt is the plan's, at 25 segments. -/
theorem rowsAt_const (h : AtMgA o Z D r Zp Np cF x) :
    h.𝔇.N.rowsAt = rowsAtPlan (P5J.At.shape Zp)
      (VerifiableInference.Desc.First.possAt cF.blocksInOrder 25) (P5T.numbersOf (P5J.At.pseats Zp)) 25 :=
  rfl

/-- **hn.** -/
theorem hn_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    0 < (h.𝔇.N.rowsAt m .equation).2 := by
  have hne : (m == 25) = false := by simpa using Nat.ne_of_lt hm
  rw [rowsAt_const h]
  simp [rowsAtPlan, hne]

/-- **hdue.** -/
theorem hdue_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    rowsDue h.𝔇.N ((openSets fullLinks P5J.At.ps (start fullLinks))[batchAt fullLinks P5J.At.ps m +
      1 + 1 + 1]?.getD []) m = (h.𝔇.N.rowsAt m .equation).1 + 1 :=
  due_of_plan h.𝔇.N _ _ _ (rowsAt_const h) m hm

/-- **hrw.** -/
theorem hrw_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) (p : Where) (hp : IM.k9At Zp m = some p) :
    ∀ s, h.𝔇.rw m s = VerifiableInference.Desc.K9.rowsFit p.rows s := by
  intro s
  show P5T.rwAt Zp m s = _
  refine P5T.rwAt_of_rows Zp m p.rows ?_ s
  show (ProofFile.k9Where (ProofFile.k9Stretches Zp) m).map (·.rows) = some p.rows
  have hp' : ProofFile.k9Where (ProofFile.k9Stretches Zp) m = some p := hp
  rw [hp']
  rfl

/-- **hpc**: the lookup on the digits stands at piece 7, at the head's link at piece 8. -/
theorem hpc_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) :
    7 + VerifiableInference.Desc.First.shift (IM.subAt m) =
      VerifiableInference.Desc.K3.pieceAt (P5J.At.X Zp) m true := by
  have h24 : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 :=
    VerifiableInference.OnPublicFiles.headLink_scope h.scope h.reads h.pubOne
  have e : VerifiableInference.Desc.K3.isHead (P5J.At.X Zp) m = (m == 24) := by
    unfold VerifiableInference.OnPublicFiles.headLink at h24
    unfold VerifiableInference.Desc.K3.isHead
    rw [h24]
  unfold VerifiableInference.Desc.K3.pieceAt
  rw [e]
  by_cases h0 : m = 24
  · subst h0
    rfl
  · have hz : (m == 24) = false := by simpa using h0
    rw [hz]
    unfold IM.subAt VerifiableInference.Desc.First.shift
    rw [if_neg h0]
    split <;> rfl

end LPFK9

#print axioms LPFK9.hpc_at
#print axioms LPFK9.listed_full
#print axioms LPFK9.due_of_plan
#print axioms LPFK9.hn_at
#print axioms LPFK9.hdue_at
#print axioms LPFK9.hrw_at
