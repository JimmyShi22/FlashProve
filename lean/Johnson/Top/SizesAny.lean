-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SizesAny.lean: the ten sizes off a parameter file, whatever its acceptance policy, and
the test "they are the reference's" without the clause on the policy: the laws. The two definitions
sizesAny and sizesAnyRefB, with sizesAny_scan: Johnson/Top/SizesAnyDef.lean.

sizesAt (Johnson/Flat/Instance.lean) refuses every parameter file whose acceptance policy is not
exact match, and so does the test sizesRefB (Johnson/Top/SizesRef.lean). By reading, and by no
theorem: what is proved from that test on the way from a verifier's yes to an instance spends two
equations, on the window and on the vocabulary (portYes_gives_request,
Johnson/Top/SpineRequest.lean [not in this library], and Flat.insReq_of_read,
Johnson/Top/InsReqCore.lean [not in this library], take the first two parts of Flat.sizesAt_publicOf
alone); on that way no proof spends the clause on the policy.
In SizesAnyDef.lean the scan and the test stand without that clause; here are the laws that are
spent, and a control that ties the two to sizesAt and sizesRefB.

Theorems.
  sizesAny_of_sizesAt: where sizesAt returns, sizesAny returns the same.
  sizesAny_of_test: sizesAnyRefB policy = true → sizesAny policy = .ok ppref.
  sizesOf_of_test: so, where sizesAnyRefB says true, the sizes of the file's own scan are ppref.
  sizesAny_publicOf: where sizesAny returns P and publicOf returns X at one parameter file, P's
    window and vocabulary are X's: the two equations of Flat.sizesAt_publicOf
    (Johnson/Top/InsReqCore.lean [not in this library]), not its two bounds.
  sizesRefB_iff: THE CONTROL: sizesRefB says true exactly if sizesAnyRefB does and the scanned
    file's policy is exact match. So at exact match nothing is weakened.

Limits: nothing on a file is evaluated here (runs: Johnson/Top/SizesAnyRun.lean). The test compares
ten sizes and the value of no other line of the parameter file. THAT A FILE PASSES IT SAYS NOTHING
OF WHAT A PROOF UNDER THE FILE's POLICY MEANS: the claims of Johnson/Flat/Claims.lean and
Johnson/Flat/LedgerClaim.lean are those of exact match alone.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.SizesAnyDef
import Johnson.Top.SizesRef
import Johnson.Flat.SizesPlanned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model OnBytes OnBytes.Flat OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- Where sizesAt returns, sizesAny returns the same. -/
theorem sizesAny_of_sizesAt {policy : ByteArray} {P : Params} (h : sizesAt policy = .ok P) :
    sizesAny policy = .ok P := by
  unfold sizesAt at h
  obtain ⟨S, h0, h⟩ := exc_bind h
  split at h
  · cases h
    unfold sizesAny
    rw [h0]
    rfl
  · cases h

/-- **If the test says true, sizesAny returns the reference parameters.** -/
theorem sizesAny_of_test {policy : ByteArray} (t : sizesAnyRefB policy = true) :
    sizesAny policy = .ok ppref := by
  unfold sizesAnyRefB at t
  cases hs : sizesAny policy with
  | error e =>
    rw [hs] at t
    cases t
  | ok P =>
    rw [hs] at t
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩,
      t8⟩, t9⟩, t10⟩ := t
    unfold sizesAny at hs
    obtain ⟨S, _, hs⟩ := exc_bind hs
    have e : sizesOf S.h = P := Except.ok.inj hs
    subst e
    exact congrArg Except.ok (sizesOf_ppref t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)

/-- If sizesAnyRefB says true, the sizes of the file's own scan are the reference parameters: all
ten equations, at the scan. -/
theorem sizesOf_of_test {policy : ByteArray} {S : Model.PolScan} (t : sizesAnyRefB policy = true)
    (h : Model.polScan policy = .ok S) : sizesOf S.h = ppref :=
  Except.ok.inj ((sizesAny_scan h).symm.trans (sizesAny_of_test t))

/-- Where sizesAny and publicOf return at one parameter file, the window and the vocabulary
agree. -/
theorem sizesAny_publicOf {policy KL : ByteArray} {layout : Option ByteArray} {P : Params}
    {X : Public} (hP : sizesAny policy = .ok P) (hX : publicOf policy KL layout = .ok X) :
    P.T = X.T ∧ P.V = X.P.h.V := by
  obtain ⟨hT, -, -⟩ := publicOf_window hX
  have hs := publicOf_scan hX
  unfold sizesAny at hP
  obtain ⟨S, h0, hP⟩ := exc_bind hP
  have e0 : S = X.P := Except.ok.inj (h0.symm.trans hs)
  subst e0
  cases hP
  exact ⟨hT.symm, rfl⟩

/-- **The control**: sizesRefB is sizesAnyRefB and "the scanned file's policy is exact match". -/
theorem sizesRefB_iff (policy : ByteArray) :
    sizesRefB policy = true ↔
      sizesAnyRefB policy = true ∧ ∃ S, Model.polScan policy = .ok S ∧ exactPolicy S.h = true := by
  constructor
  · intro t
    have h := sizesAt_of_test t
    refine ⟨?_, ?_⟩
    · unfold sizesAnyRefB
      rw [sizesAny_of_sizesAt h]
      rfl
    · unfold sizesAt at h
      obtain ⟨S, h0, h⟩ := exc_bind h
      split at h
      · rename_i hx
        exact ⟨S, h0, hx⟩
      · cases h
  · rintro ⟨t, S, h0, hx⟩
    have h := sizesAny_of_test t
    have e : sizesAt policy = .ok ppref := by
      unfold sizesAny at h
      rw [h0] at h
      unfold sizesAt
      rw [h0]
      show (if exactPolicy S.h = true then (pure (sizesOf S.h) : Except String Params)
        else throw "policy-not-exact-match") = _
      rw [if_pos hx]
      exact h
    unfold sizesRefB
    rw [e]
    rfl

end VerifiableInference.OnPublicFiles.Flat
