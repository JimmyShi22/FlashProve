-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InAtIs.lean: kind K5: WHAT THE CLAIMS' SEAT READS AND GATHERS AT A LEDGER IS WHAT A LAW HOLDS AS RETURNS: from premises in the form of the fields left · geo · zkI · points · tables · first · second of a
law's record of returns, AND u3 : i.iU3 = A.iU3: inAt (Claims/InAt.lean) returns the law's own record i and width Kc; firstAt returns l₁; secondAt returns l₂.

u3 IS NO ORNAMENT: the runs write i.iU3 into every entry that their forms name (Att/RunsP.lean: uEnt h.iU3 …), and nothing else in these premises pins it: WITHOUT IT THE LAW's i NEED NOT BE THE SEAT's RECORD.

Main names: inAt_is · firstAt_is · secondAt_is. Over Claims/FunsAt.lean (inAt_of_is) alone.
PREMISES BESIDE THE FIELDS: the array of the reads is in the ledger, at the law's width (hT · hK).
IS IT EMPTY HERE? Equations under returns that are shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.FunsAt

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard Left)

variable (A : Attention.Plan) {gL : Forest.Heard} {h : Heard} {G : Fork} {l : Left} {i : P.Runs.In} {Kc : ℕ} {T : HTree}

section
variable (left : P.LeftIs (P.geoOf A.S) gL.zk h G l) (geo : i.g = P.geoOf A.S) (zkI : i.zk = gL.zk) (u3 : i.iU3 = A.iU3)
  (points : P.pointsOf i.g gL.zk h l = some i.p)
  (tables : P.tablesP i.g (matsOf A.seam.tl.mats) A.nW (P.lookOfO (P.parCOf A).geo.lmb gL) i.p = some i.t)
  (hT : G.trees[A.iU3]? = some T) (hK : T.K = Kc)
include left geo zkI u3 points tables hT hK

/-- **What the seat's reading returns at the ledger is the law's record, and the law's width.** -/
theorem inAt_is : inAt (P.parCOf A) gL h G = some (i, Kc) := by
  rw [geo] at points tables
  rw [inAt_of_is (c := P.parCOf A) left points tables (T := T) hT, hK]
  congr 2
  cases i
  simp only at geo zkI u3
  subst geo zkI u3
  rfl

theorem firstAt_is {l₁ : List Aff} {jn : P.Runs.JoinsP} (first : P.Runs.firstRun i Kc = some (l₁, jn)) :
    firstAt (P.parCOf A) gL h G = some l₁ := by
  unfold firstAt
  rw [inAt_is A left geo zkI u3 points tables hT hK]
  show (P.Runs.firstRun i Kc).map (·.1) = some l₁
  rw [first]
  rfl

theorem secondAt_is {l₂ : List Aff} (second : P.Runs.secondRun i Kc = some l₂) :
    secondAt (P.parCOf A) gL h G = some l₂ := by
  unfold secondAt
  rw [inAt_is A left geo zkI u3 points tables hT hK]
  exact second

end

end K5Law

#print axioms K5Law.inAt_is
#print axioms K5Law.firstAt_is
#print axioms K5Law.secondAt_is
