-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttSeam.lean

THE SEAM BEFORE THE LOOKUP OF ATTENTION, FROM THE VERIFIER's OWN CALL AND NUMBERS OF THE
CONFIGURATION ALONE. linkOK_of_attCalls (Johnson/Road/Lane5BridgeA.lean) has six public premises on
the shape: AttSized, hsh, hE, NumsA, LaidA, TabsA. Here five of the six hold at one record, the
one that shapeHid returns, as theorems; the sixth, hsh, stays a premise, now on cf. No test is
run, and no public premise speaks of the shape. The two premises with content stay as they are:
AttR0 S Z (the link's meaning without its lookup clause) and (callsA S fs Z).InTables (every
call's keys lie in its table). AttR0 is the light part: cells small, bits, the row's maximum and
denominator. The scores and the accumulators stand in "InTables".

What is left as public premises: g < 12, and, on the configuration cf that shapeHid is given:
* CfRef cf: ten numbers are the reference numbers (Lane5AttShape.lean); kFD = 16, S = 12, rx = 8;
* UsualCalls cf: the usual call list, and one shift in the group (Lane5AttLaid.lean);
* hsh: in the table of scales s the first layer of group g has the configuration's first shift. It
  ties the first layer's shift alone: the link's segment reads no other (Lane5AttDef.lean's head);
  that s has that shift at the group's other layers is a clause of Cm.Scales.Lawful, not asked here.

UsualCalls is no test of the verifier: the verifier takes other call lists, and groups with two
shifts (there it makes a call of kinds KR and KFD for each shift); at these this file says
nothing. So whoever calls these theorems from "a verifier accepts" must bring UsualCalls as a
public premise of the end statement. It is a test that a program can run on the configuration
(usualB, usual_of_test).

Main theorems: "tabsA_of_usual", "attBridge_of_usual", **"linkOK_of_usual"**, "splitA_of_usual".
Not claimed: that a parameter file gives such a configuration. From the verifier's own fill,
CfRef, S = 12 and rx = 8 (cfRef_of_fill, Lane5AttPub.lean) and hsh (hsh_of_fill, Lane5AttScl.lean)
are theorems; Lane5AttSeamPub.lean joins them to this file's. kFD = 16 does not follow so: it is
not among the fourteen numbers of FillRef (fill sets kFD to the parameter file's number). Not
claimed either: "InTables" for a proof that a verifier accepts; all that Lane5BridgeA.lean does
not claim.
The key vectors in "InTables" are kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library
over the verifier's records, at the cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The
verifier holds no key vector. That its key forms evaluate kvA is shown elsewhere under a premise
(rule, OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean); that addrA is the program's rule is shown nowhere.
"The verifier's own" is said here of shapeHid's record alone: sizes, pieces, tables.
-/
import Johnson.Road.Lane5AttHid
import Johnson.Road.Lane5AttLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy tbRef)
open Attention (ACall Cfg Shape shapeHid)

variable {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}

/-- **The premise on the tables, with nothing left on the shape.** -/
theorem tabsA_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) : TabsA S fs := by
  have Fo := four_of_hid h U
  have P := shaped_of_hid h
  exact tabsA_of_hid h (fit_hid h hc.ldh U.one) hkF h12 h8 (laidA_of_hid h U).isCall
    (kinds_of_four Fo) (room_of_four P (tests_of_hid h).1 Fo)

/-- **The bridge at attention, from the verifier's own call.** -/
theorem attBridge_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) (Z : Zs) :
    AttBridge S Z (callsA S fs Z) :=
  attBridge (numsA_of_hid h hc.ldh) (laidA_of_hid h U) (tabsA_of_usual h hc hkF h12 h8 U) Z

/-- **The seam before the lookup of attention of group g, from the verifier's own call.** -/
theorem linkOK_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) {g : ℕ}
    (hg : g < 12) {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) {Z : Zs} (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) (R : AttR0 S Z) (I : (callsA S fs Z).InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g + 1) (attMx S g Z) :=
  linkOK_of_attSplit hg (attSized_hid h hc h12 h8)
    (by rw [(shaped_of_hid h).cfg]; exact hsh) (exp_of_hid h h12 h8) pol Wz x
    (attBridge_of_usual h hc hkF h12 h8 U Z) R I

/-- **So, under AttR0 S Z, the seam of Lane5Split.lean holds there.** AttR0 is a hypothesis of this
theorem; SplitA's own premise LinkR0 is not used. -/
theorem splitA_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) {g : ℕ}
    (hg : g < 12) {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) {Z : Zs} (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) (R : AttR0 S Z) (A : ℕ → Mx)
    (hA : A (2 * g + 1) = attMx S g Z) : SplitA s pol Wz x A g (callsA S fs Z) :=
  splitA_of_att hg (attSized_hid h hc h12 h8)
    (by rw [(shaped_of_hid h).cfg]; exact hsh) (exp_of_hid h h12 h8) pol Wz x
    (attBridge_of_usual h hc hkF h12 h8 U Z) R A hA

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.tabsA_of_usual
#print axioms OnBytes.Road.L5.attBridge_of_usual
#print axioms OnBytes.Road.L5.linkOK_of_usual
#print axioms OnBytes.Road.L5.splitA_of_usual
