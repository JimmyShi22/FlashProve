-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/ProofRows/K3CallsOkHead.lean: THE KIND's OWN TEST ON A CALL (`callOk`,
Johnson/Desc/First/Look/ShapeOwn.lean) SAYS YES AT EVERY CALL OF THE OUTPUT HEAD's LOOKUP WHEREVER
THE PROGRAM `verify-on-bytes`'s READER OF THE PUBLIC FILES RETURNS: A LAW BY THE MAKE: NO TABLE IS
EVALUATED HERE. It pays the premise hOk of `headRow_full` and `headEntry_full`
(Johnson/AtFull/ProofRows/K3HeadRow.lean, K3Rows.lean). Six theorems.
Why it holds. The reader (`Verify.publicOf`) makes the head's layout by `Head.layout`
(OnBytes/Model/HeadLayout.lean), which runs the library's `Forest.shape` on the very calls, with
their tables, and refuses where it refuses; `Forest.shape` asks `Forest.callAsk` of each call; and
the kind's own `shapeOwn` and `callOk` are these two, by `shapeOwn_eq`
(Johnson/Desc/First/Look/ShapeOwnAgrees2.lean). Behind that call the layout lays each call's field
iota anew, which `callOk` does not read.
  `all_of_shapeOwn`: where `shapeOwn` answers, every call passes `callOk`. `all_of_shape`: so
    where `Forest.shape` returns.
  `callOk_iota`: the test does not read iota. `layout_calls_ok`: where `Head.layout` returns L:
    `L.cl.all callOk = true`.
  `public_calls_ok`: where `publicOf` returns X: `X.HLy.cl.all callOk = true` (by another author's
    `public_parts`, Johnson/Road/HeadPub.lean). `place_calls_ok`: so at the place that `lookAt X
    24 false` gives, at p4 and twelve groups.
Limits. WHAT IT IS WORTH: THE LAW PAYS NOTHING OF ITSELF: THAT `publicOf` RETURNS IS ITS PREMISE,
AND THE READER RETURNS ONLY BEHIND ITS OWN WALK OVER THE TABLES: whoever shows that return walks
them there, or needs a law on them: their cost stands once, in the return. The head's place alone.
How many calls there are is not said here. No soundness is claimed.

-/
import Johnson.Desc.First.Look.ShapeOwnAgrees2
import Johnson.Desc.First.Look.LookAt
import Johnson.Road.HeadPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place lookAt shapeOwn callOk shapeOwn_eq)
open OnBytes.Road.Hd (ok_of_needed public_parts)
open OnBytes.Road (ok_of_bind)

/-- Where the kind's own maker of the numbers answers, every call passes its test. -/
theorem all_of_shapeOwn {calls : Array Call} {lid : Nat} {h : Forest.Shape}
    (e : shapeOwn calls lid = some h) : calls.all callOk = true := by
  unfold shapeOwn at e
  cases hc : calls.all callOk with
  | true => rfl
  | false =>
    rw [hc] at e
    cases e

/-- So where the library's returns. -/
theorem all_of_shape {calls : Array Call} {lid : Nat} {h : Forest.Shape}
    (e : Forest.shape calls lid = .ok h) : calls.all callOk = true :=
  all_of_shapeOwn (h := h) (by rw [shapeOwn_eq, e]; rfl)

/-- The test does not read iota. -/
theorem callOk_iota (c : Call) (n : Nat) : callOk { c with iota := n } = callOk c := rfl

/-- **Where the head's layout returns, its calls pass.** -/
theorem layout_calls_ok {h : Head.Shape} {tauFC : Array F} {L : Head.HL}
    (hy : Head.layout h tauFC = .ok L) : L.cl.all callOk = true := by
  unfold Head.layout at hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨u, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, hfs, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  have h0 := all_of_shape hfs
  rw [Array.all_eq_true] at h0 ⊢
  intro i hi
  rw [Array.getElem_mapIdx, callOk_iota]
  exact h0 i (by simpa using hi)

/-- **Where the reader of the public files returns, the head's calls pass.** -/
theorem public_calls_ok {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) : X.HLy.cl.all callOk = true := by
  obtain ⟨P, y, -, -, -, -, -, hl, -⟩ := public_parts h
  exact layout_calls_ok hl

/-- **hOk**: at the place of the lookup on the head's calls. -/
theorem place_calls_ok {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) (h4 : X.p4 = true) (hN : X.NGr = 12) {x : Place}
    (hx : lookAt X 24 false = some x) : x.calls.all callOk = true := by
  unfold lookAt at hx
  rw [h4, hN] at hx
  have e : x.calls = X.HLy.cl := by
    have e0 := Option.some.inj hx
    rw [← e0]
  rw [e]
  exact public_calls_ok h

end Johnson.AtFull.ProofRows.K3

#print axioms Johnson.AtFull.ProofRows.K3.all_of_shapeOwn
#print axioms Johnson.AtFull.ProofRows.K3.all_of_shape
#print axioms Johnson.AtFull.ProofRows.K3.callOk_iota
#print axioms Johnson.AtFull.ProofRows.K3.layout_calls_ok
#print axioms Johnson.AtFull.ProofRows.K3.public_calls_ok
#print axioms Johnson.AtFull.ProofRows.K3.place_calls_ok
