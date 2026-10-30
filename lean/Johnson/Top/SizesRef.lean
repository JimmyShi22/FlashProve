-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SizesRef.lean: the premise "sizesAt reads the reference sizes off the parameter file"
(Johnson/Top/InsReqWords.lean) as a test that a program can run, with its
theorem.

sizesAt (Johnson/Flat/Instance.lean) returns the reference parameters with ten numbers put to the
parameter file's. So it returns the reference parameters themselves where these ten are the
reference's.

One definition and three theorems.
  sizesRefB policy: sizesAt returns, and the ten numbers (window, vocabulary, layers, width, query
    heads, key heads, a head's width, the two inner widths, experts) are the reference's.
  sizesOf_ppref: the ten equations give sizesOf h = ppref.
  sizesAt_of_test: sizesRefB policy = true → sizesAt policy = .ok ppref.
  sizesAt_of_served: at a statement x that is served at three public files Z (servedAt,
    OnBytes/K/Served.lean: x's parameter file is Z's, byte for byte), one evaluation of the test at
    Z's parameter file pays the premise at x.

Limits: nothing on a file is evaluated here (runs: Johnson/Top/SizesRefRun.lean
[not in this library]). sizesAt refuses every parameter file whose acceptance policy is not exact
match: so does the test. Z is a letter.
The test compares ten sizes and the policy's five lines, no other line of the parameter file and
neither of the other two files.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.K.Served
import Johnson.Flat.Instance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model OnBytes OnBytes.Flat

/-- The ten equations give the reference parameters. -/
theorem sizesOf_ppref {h : Model.Hdr} (h1 : 2 ^ h.lt = ppref.T) (h2 : h.V = ppref.V)
    (h3 : h.L = ppref.layers) (h4 : h.d = ppref.d) (h5 : h.H = ppref.nq) (h6 : h.Gk = ppref.nkv)
    (h7 : h.dh = ppref.ch) (h8 : h.f = ppref.f) (h9 : h.fe = ppref.fe)
    (h10 : h.NE = ppref.nexp) : sizesOf h = ppref := by
  unfold sizesOf
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-- The premise as a test. -/
def sizesRefB (policy : ByteArray) : Bool :=
  match sizesAt policy with
  | .ok P => P.T == ppref.T && P.V == ppref.V && P.layers == ppref.layers && P.d == ppref.d &&
      P.nq == ppref.nq && P.nkv == ppref.nkv && P.ch == ppref.ch && P.f == ppref.f &&
      P.fe == ppref.fe && P.nexp == ppref.nexp
  | .error _ => false

/-- **If the test says true, sizesAt returns the reference parameters.** -/
theorem sizesAt_of_test {policy : ByteArray} (t : sizesRefB policy = true) :
    sizesAt policy = .ok ppref := by
  unfold sizesRefB at t
  cases hs : sizesAt policy with
  | error e =>
    rw [hs] at t
    cases t
  | ok P =>
    rw [hs] at t
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩,
      t8⟩, t9⟩, t10⟩ := t
    unfold sizesAt at hs
    obtain ⟨S, _, hs⟩ := Params.exc_bind hs
    split at hs
    · have e : sizesOf S.h = P := Except.ok.inj hs
      subst e
      exact congrArg Except.ok (sizesOf_ppref t1 t2 t3 t4 t5 t6 t7 t8 t9 t10)
    · cases hs

/-- **At a served statement one evaluation at Z's parameter file pays the premise.** -/
theorem sizesAt_of_served {Z : K.Pub} {x : K.UserStm} (h : K.servedAt Z x = true)
    (t : sizesRefB Z.pol = true) : sizesAt x.pol = .ok ppref := by
  have e : x.pol = Z.pol := by
    unfold K.servedAt at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1
  rw [e]
  exact sizesAt_of_test t

end VerifiableInference.OnPublicFiles.Flat
