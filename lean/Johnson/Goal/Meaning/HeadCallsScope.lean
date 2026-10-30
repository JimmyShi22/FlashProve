-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadCallsScope.lean: at all public files in the goals' scope the two lookup
calls whose key points the output head's own rounds read are call number 0.

What the file holds. X: what publicOf returns on public files in scope.
  lines_in_scope    the head's list of calls in use is the stored example's six lines.
  callNo_in_scope   **Head.callNo X.HLy "NF" = some 0 and Head.callNo X.HLy "HD0" = some 0.**
Why. The program `verify-on-bytes` takes these two numbers by name off the head's layout
(OnBytes/Model/HeadHeard.lean: hear: qN, qH). The head's seat lays both 0
(Johnson/Stored/HeadSeat.lean: heardOf), and the quiet step that makes the tables of reads reads
them (Johnson/Desc/K8/ReadsQuiet.lean: tables). So in scope the seat's two numbers are that
program's.

On what it rests. Johnson/Desc/Kinds/Law/FirstCall.lean (callNo_first);
Johnson/Goal/Meaning/ScopeScanTies.lean (calls_of_scope: the parameter file's lines callH in scope);
Johnson/Road/HeadLaid.lean (admittedH_of_layout: the layout's calls are what callsOf returns).

What it does not give. Nothing on soundness. Outside the scope a parameter file may name the two
segments in another line than the first: there the seat's 0 and `verify-on-bytes`'s number part,
and nothing here says what follows. That any files meet the premises: see the head of
HeadCondScope.lean.

-/
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Desc.Kinds.Law.FirstCall

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

theorem lines_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    OnBytes.Model.Head.callLines X.hS = VerifierAndGoals.Lines.callsHRef := by
  have e : X.hS.polCallsH = VerifierAndGoals.Lines.callsHRef := by
    rw [Meaning.HeadS.headShape_of_public h]
    exact (OnBytes.Road.Hd.calls_of_scope hZ hR h).2.2
  unfold OnBytes.Model.Head.callLines
  rw [e]
  rfl

/-- **The two calls are call number 0.** -/
theorem callNo_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    OnBytes.Model.Head.callNo X.HLy "NF" = some 0 ∧
      OnBytes.Model.Head.callNo X.HLy "HD0" = some 0 := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  obtain ⟨cs, hc, -, hL⟩ := (OnBytes.Road.Hd.admittedH_of_layout B.head).calls
  have hl := lines_in_scope hZ hR h
  unfold VerifierAndGoals.Lines.callsHRef at hl
  exact ⟨FirstCall.callNo_first hc hL hl (by decide), FirstCall.callNo_first hc hL hl (by decide)⟩

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.lines_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.callNo_in_scope
