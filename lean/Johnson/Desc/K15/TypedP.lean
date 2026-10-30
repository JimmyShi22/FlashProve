-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/TypedP.lean: THE CLOSED CALLER, FIRST HALF: the link's parameters P AS TYPED VALUES
at the two sizes of the setting "record with work".
  frP | srP   the shape and the codes are the library's typed recordRead's | smallRecordRead's; the
  setting and the stages' sizes are typed here: COPIED BY PROGRAM out of a print of p15Of c at
  one set of full-size | small
              public files (PRINT.L16.print-P15: Lean's own Repr of the planner's record: numbers of
              the plan). That p15Of c IS frP is A LAW AT EVERY THREE PUBLIC FILES IN SCOPE
              (Johnson/Goal/Conditions/LinkTypedAtLines.lean: inScope_typed); that it is srP at the
              small example's files is evaluated; no theorem.
  sameP P Q   A TEST WITH CODE: the two records of parameters are one, field by field (the setting ·
  the codes · the shape · the stages' sizes) · sameP_eq: its yes gives P = Q: FOR A GATE IN FRONT OF
  THE DECISION: where the
              gate b := sameP (p15Of c) frP is open, the description that runs IS the one at the
              typed parameters (linkDesc_frP | linkDesc_srP).
              NO SUCH GATE STANDS IN THE SEATED TEXT (the fact is a law in
              scope, not a second gate). The typed values were copied at those files; by
              report, not checked here, the full-size parameter file of another set
              is the same to the byte; that set's layout and scale files were not seen;
              the test itself has been evaluated at no file of that other set.

-/
import Johnson.Desc.Link.LinkDescWithGroundSend
import OnBytes.Params.EntryDryRecord
import OnBytes.Params.EntryDryRecordSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params
open OnBytes.Params (recordRead smallRecordRead)

def frP : P15 :=
  { set :=
      { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false,
        instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8,
        positionBytes := 0, workField := { request := 0, shared := 0, once := 0 },
        workSample := { request := 0, shared := 0, once := 0 },
        workCloseness := { request := 0, shared := 0, once := 0 },
        workQuery := { request := 20, shared := 28, once := 32 },
        workSmall := { request := 0, shared := 0, once := 0 } }
    codes := recordRead.codes, S := recordRead.link
    stages :=
        [{ g :=
           { main := { logN := 24, ell := 4194304, r := 97, overE := true }, mask :=
             { logN := 13, ell := 64, r := 97, overE := true }, k := 8, h := 0, slots := 1,
             rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 97, rOod := 0 },
      { g :=
          { main := { logN := 21, ell := 131072, r := 49, overE := true }, mask :=
            { logN := 12, ell := 128, r := 49, overE := true }, k := 5, h := 2, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 49, rOod := 93 },
      { g :=
          { main := { logN := 17, ell := 8192, r := 49, overE := true }, mask :=
            { logN := 12, ell := 128, r := 49, overE := true }, k := 4, h := 2, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 318 }, t := 49, rOod := 109 },
      { g :=
          { main := { logN := 13, ell := 512, r := 50, overE := true }, mask :=
            { logN := 12, ell := 128, r := 50, overE := true }, k := 4, h := 2, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 570 }, t := 50, rOod := 109 },
      { g :=
          { main := { logN := 14, ell := 512, r := 40, overE := true }, mask :=
            { logN := 14, ell := 512, r := 40, overE := true }, k := 0, h := 0, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 348 }, t := 40, rOod := 106 }] }

def srP : P15 :=
  { set :=
      { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false,
        instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8,
        positionBytes := 0, workField := { request := 0, shared := 0, once := 0 },
        workSample := { request := 0, shared := 0, once := 0 },
        workCloseness := { request := 0, shared := 0, once := 0 },
        workQuery := { request := 20, shared := 28, once := 32 },
        workSmall := { request := 0, shared := 0, once := 0 } }
    codes := smallRecordRead.codes, S := smallRecordRead.link
    stages :=
        [{ g :=
           { main := { logN := 17, ell := 32768, r := 97, overE := true }, mask :=
             { logN := 13, ell := 64, r := 97, overE := true }, k := 6, h := 0, slots := 1,
             rule := OnBytes.Params.Radius.johnson, m := 483 }, t := 97, rOod := 0 },
      { g :=
          { main := { logN := 14, ell := 2048, r := 66, overE := true }, mask :=
            { logN := 12, ell := 128, r := 66, overE := true }, k := 4, h := 2, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 600 }, t := 66, rOod := 93 },
      { g :=
          { main := { logN := 14, ell := 2048, r := 66, overE := true }, mask :=
            { logN := 14, ell := 512, r := 66, overE := true }, k := 0, h := 0, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 600 }, t := 66, rOod := 58 }] }

def sameP (P Q : P15) : Bool :=
  decide (P.set = Q.set) && decide (P.codes = Q.codes) && decide (P.S = Q.S) && decide
      (P.stages = Q.stages)

theorem sameP_eq {P Q : P15} (h : sameP P Q = true) : P = Q := by
  unfold sameP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases P
  cases Q
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem linkDesc_frP (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : sameP (p15Of c) frP = true) :
    linkDesc c plan = descOf frP plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan) :=
        by
  unfold linkDesc
  rw [sameP_eq h]

theorem linkDesc_srP (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : sameP (p15Of c) srP = true) :
    linkDesc c plan = descOf srP plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan) :=
        by
  unfold linkDesc
  rw [sameP_eq h]

end Desc.K15

#print axioms Desc.K15.sameP_eq
#print axioms Desc.K15.linkDesc_frP
