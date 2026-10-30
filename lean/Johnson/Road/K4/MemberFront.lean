-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberFront.lean: THE PUBLIC SIDE OF THREE PREMISES OF `Plan4L.k04LawAt_K2`
(Johnson/Road/K4/CloseK2.lean: `ValueMore`, `FrontIs`, the field ns of `Owes2`) AT THE VALUE AT THE
REFERENCE SIZES (`refL`, Johnson/Road/K4/RefValue.lean) and the record that the verifier's own
`publicOf` returns. No premise here says whether the group is the first. Five statements. Nothing
new is argued: lemmas of the library and of this folder. The file that lays them into the record
`FrontIs`, Johnson/Road/K4/MemberFrontIs.lean, is not in this library.

  `ref_valueMore`: the record `Plan4L.ValueMore` (Johnson/Road/K4/CloseRows.lean) holds of the
    value, whatever its free letters.
  `ref_ns_le`: the value's ns is at least the free letter R.ns. So `Owes2.ns` ("the ledger's number
    of slots is at most the value's ns + 1") follows wherever the ledger's number is at most
    R.ns + 1. By a search of this folder (no proof), no statement bounds the value's ns from above.
  `ref_lines_pub`: ONE s0 serves the field lines of `Owes2` and the line pub of `FrontIs`: the
    plan's shape of the lookup is s0 with another field pub.
  `ref_ok`: the plan's shape of the lookup passes the lookup's test on numbers `FoNums.ok` (the
    library's `Fo.layout_shape`, OnBytes/Tie/Pv/Lookup/Ends/FoPublicShape.lean, and
    `Fo.Pay.shapeOf_ok`, OnBytes/Tie/Pv/Lookup/Peel/FoPayCaller.lean): the line ok of `FrontIs`.
  `ref_planned`: the state that the group's plan lays for its sub-proof, with its slots set up, has
    taken no slot and has the plan's number of slots (`Fo.Next0.planned_door0`,
    OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean). It bears on the letter first and on R.ns; that the
    ledger in front of the lookup's block IS that state is not said here.

WHAT IS A THEOREM, WHAT A RUN, WHAT A PREMISE. Theorems, from the premises below: all five. Runs, no
theorems (Johnson/Road/K4/GuardMemberFront.lean [not in this library; so here read: not tested in
this library], at linesKF and scalesKF): the lookup hears 1930 elements; the plans' numbers of
slots. Premises that stay, in `ref_lines_pub`: hcap (the reference cap is the shape's lidb: in
neither test; a run: Johnson/Road/K4/GuardMember.lean [not in this library; so here read: not tested
in this library]); the place holds the record's layers and the group's plan; g is below 12. That the
two tests `recordB` and `tablesB` say true is a run (Johnson/Road/Ends/GuardRec.lean).

Limits. THE PUBLIC SIDE ALONE. That the ledger in front of the lookup has a given next free slot,
and that the ledger's number of slots is the plan's, is said of no hearing here. No soundness is
concluded.
-/
import Johnson.Road.K4.MemberOwes
import Johnson.Road.K4.CloseRows
import Johnson.Road.FormsKeysShape
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicShape
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Road.Alg (recordB tablesB returns_of_record)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par)

variable [scl : Scl] {M Xs : Type} {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
  {p : Par} {tk : Array Nat}

/-- **`ValueMore` holds of it.** -/
theorem ref_valueMore (R : RefLetters M Xs) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    Plan4L.ValueMore (refL R g hg nT nI) where
  numI := rfl
  n4 := fun _ => rfl
  room7 := (ref_room R g hg nT nI).2

/-- The value's ns is at least the free letter. -/
theorem ref_ns_le (R : RefLetters M Xs) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    R.ns ≤ (refL R g hg nT nI).ns :=
  Nat.le_max_left _ _

/-- **One s0 serves the public lines and the line pub.** -/
theorem ref_lines_pub (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (tt : tablesB X.layers.y = true) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hcap : Dim.ref.cap = (layerShape X.P).lidb) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refL R p.g hg nT nI).plan.full.D (refL R p.g hg nT nI).plan.full.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∃ pb, p.P.y.fo = { s0 with pub := pb } := by
  obtain ⟨s0, H⟩ := ref_lines R hg nT nI h t tt hP hG hcap
  refine ⟨s0, H, ?_⟩
  obtain ⟨s1, pb, hs, e⟩ := shape_of_layout (returns_of_record h t).1
  have h0 : Forest.shape X.layers.y.cl X.layers.y.h.lidb = .ok s0 := by
    have h1 := (H tk).hs0
    rw [hP] at h1
    exact h1
  obtain rfl : s1 = s0 := Except.ok.inj (hs.symm.trans h0)
  rw [hP]
  exact ⟨pb, e⟩

omit scl in
/-- **The plan's shape of the lookup passes the lookup's test on numbers**, wherever `publicOf`
returns and the test `recordB` says true at some group. -/
theorem ref_ok {g : ℕ} (h : publicOf pol KL lay = .ok X) (t : recordB X g = true) :
    FoNums.ok X.layers.y.fo = true :=
  _root_.Fo.Pay.shapeOf_ok (_root_.Fo.layout_shape (returns_of_record h t).1)

omit scl in
/-- **The planned state has taken no slot, and has the plan's number of slots**, wherever `publicOf`
returns, at the plan of any group. -/
theorem ref_planned (h : publicOf pol KL lay = .ok X) (hG : X.G[p.g]? = some p.hp) :
    (p.hp.Fp.fillL.slots p.hp.ns).next = 0 ∧ (p.hp.Fp.fillL.slots p.hp.ns).ns = p.hp.ns :=
  ⟨(_root_.Fo.Next0.planned_door0 h).1 p.g p.hp hG, rfl⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_valueMore
#print axioms OnBytes.Road.K4.ref_ns_le
#print axioms OnBytes.Road.K4.ref_lines_pub
#print axioms OnBytes.Road.K4.ref_ok
#print axioms OnBytes.Road.K4.ref_planned
