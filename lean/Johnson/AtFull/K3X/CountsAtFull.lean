-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/CountsAtFull.lean: the sixteen counts of padding keys of a layer sub-proof's
lookup on the calls (Johnson/AtFull/K3X/CountsLaw.lean), at the Lean library's written copy of the
full-size public files (VerifierAndGoals.storedPublicFiles), and against the written values of the lot of the kind
"lookup" (Johnson/AtFull/Desc/Lots/K3Written.lean). Joinings, and four light closed facts.

  `counts_written`: the lot's written list pubW at the two sorts of a layers' segment (0: segment
    0; 2: the others), at the lookup on the calls, is countsW: by definition.
  `switches_W`, `sized_W`, `cap_W`, `floor_W`: at the written shape hW
    (Johnson/AtFull/Public/Values.lean) the eleven switches are set, the nine sizes are the
    library's reference sizes, and two numbers are the library's: by evaluation in Lean's kernel.
    `switches_no`, `sized_no`: negative tests of the first two.
  `counts_yFull`: **the layout yFull (the same file) has fo.pub = pubW 0 false**: the law at that
    file's layout_W.
  `counts_at`: **wherever the public part's maker returns X at VerifierAndGoals.storedPublicFiles, whatever the layout
    file, X.layers.y.fo.pub = pubW 0 false.**

Limits. As in CountsLaw.lean: the numbers are the verifier's own count. No Lean ties VerifierAndGoals.storedPublicFiles to
any file outside the library. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.K3X.CountsLaw
import Johnson.AtFull.Desc.Lots.K3Written
import Johnson.AtFull.Public.Values
import Johnson.Road.Ends.AlgBridgeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model
open Johnson.AtFull.Lots.K3 (pubW)
open OnBytes.Road.K4.Trial.Values (yFull hW layout_W)

theorem counts_written : pubW 0 false = countsW ∧ pubW 2 false = countsW := ⟨rfl, rfl⟩

/-- **At every value that the public part's maker returns at the written full-size files.** -/
theorem counts_at {lay : Option ByteArray} {X : Verify.Public}
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      lay = .ok X) : X.layers.y.fo.pub = pubW 0 false := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  exact counts_in_scope_o hZ hR h

/-! Four light closed facts on the written shape hW, by evaluation in Lean's kernel. -/

/-- The eleven switches are set. -/
theorem switches_W : OnBytes.Road.Alg.switchesB hW = true := by decide +kernel

/-- A negative test: with one digit form changed the test on the switches rejects. -/
theorem switches_no : OnBytes.Road.Alg.switchesB { hW with hq := hW.hq + 1 } = false := by
  decide +kernel

/-- The nine sizes are the library's reference sizes. -/
theorem sized_W : OnBytes.Road.Alg.sizedB hW Inst.Model.All.DF = true := by decide +kernel

/-- A negative test: with the stream one wider the test on the sizes rejects. -/
theorem sized_no : OnBytes.Road.Alg.sizedB { hW with d := hW.d + 1 } Inst.Model.All.DF = false := by
  decide +kernel

/-- The limit on a tree's depth is the library's. -/
theorem cap_W : Inst.Model.All.DF.cap = hW.lidb := by decide +kernel

/-- The least number of columns of a call. -/
theorem floor_W : hW.nmin - hW.ll - hW.lt = 20 - 2 - 10 := by decide +kernel

/-- **At the layout that stands by name.** -/
theorem counts_yFull : yFull.fo.pub = pubW 0 false := by
  have S : OnBytes.Road.Switches hW := OnBytes.Road.Alg.switches_of_B switches_W
  have Zs : OnBytes.Road.Sized hW Inst.Model.All.DF := OnBytes.Road.Alg.sized_of_B sized_W
  have hc := cap_W
  have e := floor_W
  have hN : OnBytes.Road.LinesAre yFull := by
    unfold OnBytes.Road.LinesAre
    rw [Meaning.P34.lines_of_layout layout_W rfl]
    exact Meaning.P34.callsRef_lines
  exact counts_of_layout
    (v := { y := yFull, sc := default, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] })
    layout_W S Zs hc hN (fun k => by rw [e]; exact Meaning.P34.floor_ref k)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.counts_written
#print axioms Johnson.AtFull.K3X.counts_at
#print axioms Johnson.AtFull.K3X.switches_W
#print axioms Johnson.AtFull.K3X.switches_no
#print axioms Johnson.AtFull.K3X.sized_W
#print axioms Johnson.AtFull.K3X.sized_no
#print axioms Johnson.AtFull.K3X.cap_W
#print axioms Johnson.AtFull.K3X.floor_W
#print axioms Johnson.AtFull.K3X.counts_yFull
