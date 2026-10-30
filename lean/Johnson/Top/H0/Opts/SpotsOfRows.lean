-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SpotsOfRows.lean: THE BODY OF THE NAMED TEST «spotsB» (in
Johnson/P5J/OptsOk.lean) ACCEPTS, AT FILES IN THE GOALS' SCOPE, UNDER ONE NAMED RESIDUE: «THE SECOND
READING OF THE THREE PUBLIC FILES RETURNS» (hrows), and where the places' numbers answer at the 25
code switches. In this file's own terms: OptsOk.lean is not imported here. A law file; no running
text imports it.

  planned_of_rows  where Johnson.G.sendRowsOf returns, the planner of verify-on-bytes has
                   returned: its first call (sendsOf) begins there.
  tableOf_ok       where both return, the code switch's typed table is made.
  spots_core       InScope Z · hrows : ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R · the
                   public part Zp holds Z's policy.txt and KL.bin · ProofFile.pAtK2? Zp m answers at
                   every m < 25 ⟹ the test's body at (Zp, Z.lay) is true. The table has at most
                   25 rows by TableRows.lean's tableOf_rows and PlannerRequestHas25Links.lean's older_links.
hrows IS NOT PAID: no theorem says that sendRowsOf (sendsOf and packListOf) returns at any file,
and no test of the verifier on the plan holds its value. It is a condition on the public files
alone.
Spent by: SpotsAtName.lean's spotsB_at_name.
Limits. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.Opts.TableRows
import Johnson.Top.H0.Opts.PlannerRequestHas25Links
import Johnson.Desc.ProofFile.CarryAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

theorem planned_of_rows {pol lay KL : ByteArray}
    (h : ∃ R, Johnson.G.sendRowsOf pol lay KL = .ok R) :
    ∃ p, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p := by
  obtain ⟨R, h⟩ := h
  unfold Johnson.G.sendRowsOf at h
  obtain ⟨sends, hs, -⟩ := exc_bind h
  unfold Johnson.G.sendsOf at hs
  obtain ⟨p, hp, -⟩ := exc_bind hs
  exact ⟨p, hp⟩

theorem tableOf_ok {pol lay KL : ByteArray} {p : OnBytes.Model.Verify.Planned}
    {R : List Johnson.G.SendRow} (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hR : Johnson.G.sendRowsOf pol lay KL = .ok R) : ∃ t, tableOf pol lay KL = .ok t := by
  unfold tableOf placesOf
  rw [hp, hR]
  exact ⟨_, rfl⟩

/-- **The test's body, under the one residue.** -/
theorem spots_core {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (hrows : ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) {Zp : ProofFile.Pub}
    (e1 : Zp.pol = Z.pol) (e2 : Zp.KL = Z.KL)
    (hA : ∀ m, m < 25 → (ProofFile.pAtK2? Zp m).isSome = true) :
    (match (tableOf Zp.pol Z.lay Zp.KL).toOption with
      | some t => (List.range t.length).all fun m => (ProofFile.pAtK2? Zp m).isSome
      | none => false) = true := by
  rw [e1, e2]
  obtain ⟨p, hp⟩ := planned_of_rows hrows
  obtain ⟨R, hR⟩ := hrows
  obtain ⟨t, ht⟩ := tableOf_ok hp hR
  obtain ⟨p', hp', hle⟩ := tableOf_rows ht
  have h25 := older_links hZ hp'
  rw [ht]
  show ((List.range t.length).all fun m => (ProofFile.pAtK2? Zp m).isSome) = true
  refine List.all_eq_true.2 fun m hm => hA m ?_
  have := List.mem_range.1 hm
  omega

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.spots_core
