-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5SameCallsAt.lean

At the plan of group g in the record that the verifier's publicOf returns: "SameCalls", and the
clause "ForInA" is the library's clause on looked-up values at the sizes, tables and shift that
these files make from the shape Ag.S.

"forInA_iff_keys_of_usual" (Johnson/Road/Lane5SameCalls.lean) stands at what shapeHid returns on a
configuration that is a letter, under six premises. Here all six are drawn from publicOf's line,
"Hd.PublicAt X.P" and the test "attUsualK X" (Johnson/Road/Lane5AttSeamAt.lean), by the road of
"seam_of_true_publicAt" (Johnson/Road/Lane5AttSeamTrueAt.lean).

Main theorem:
* "forInA_iff_keys_publicAt": for every g below 12 the plan Ag, fixed by X.A[g]? = some Ag, has
  "SameCalls Ag.S Ag.fs", and for every reading cell of the names: "ForInA Ag.S Ag.fs cell" if and
  only if "KeysC Ag.S cell".

Limits. The test "attUsualK" is no test of the verifier: a parameter file that it admits may have
another list of calls, and then nothing is said. The key vectors in "ForInA" are kvA
(OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library over the verifier's records; the
verifier holds no key vector. That a caller of the lookup has these key vectors is said nowhere
here. That publicOf returns and that "Hd.PublicAt" and "attUsualK" hold of any parameter file is a
run's matter (Johnson/Road/Lane5AttSeamRun.lean), no theorem; the run is made with no layout file.
The readings nF, kN and tauF in "ForInA" are typed with the bodies that the lookup's readings have,
by a reading; nothing compiles the two together (Johnson/Road/Lane5ForIn.lean; at the head they are
the lookup's own: Johnson/Road/Ends/HeadForIn.lean). That the sizes, tables and shift made from Ag.S
are the reference's is not in the statement.

-/
import Johnson.Road.Lane5SameCalls
import Johnson.Road.Lane5AttSeamAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **At the record's own plan: SameCalls, and the clause ForInA is the library's clause at the
letters made from the shape.** -/
theorem forInA_iff_keys_publicAt (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (A : Hd.PublicAt X.P) (U : attUsualK X = true) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧ SameCalls Ag.S Ag.fs ∧
      ∀ cell : NameA → Cb.Gl.E, ForInA Ag.S Ag.fs cell ↔ KeysC Ag.S cell := by
  have H := Hd.public_of_publicOf h A
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, -⟩ :=
    hid_of_public h H.p4 (g := g) (by rw [H.groups]; exact hg)
  obtain ⟨hc, h12, h8, -⟩ := cfRef_of_fill hf (Hd.fillRef_of_at A H)
  have ec : (Hd.shapeA X g).cf = cf := by rw [← eS]; exact (shaped_of_hid hh).cfg
  have hU := (attUsualK_at U hg).1
  have hk := (attUsualK_at U hg).2
  rw [ec] at hU hk
  exact ⟨Ag, hA, eS, sameCalls_of_usual hh (usual_of_test hU), fun cell =>
    forInA_iff_keys_of_usual hh hc hk h12 h8 (usual_of_test hU) cell⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.forInA_iff_keys_publicAt
