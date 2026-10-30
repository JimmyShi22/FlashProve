-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TopServed.lean: the top statement of the tie (OnBytes/K/Top.lean, `top`), drawn from the
law on the exit code that also pays the test `servedAt` (OnBytes/K/Served.lean). For proofs only;
the program does not import this file.

  `top_both`: if verify-on-bytes returns 0, then the call was a whole call on the bytes F with the
    options a, and two things hold of the same F and a. If the user's statement is served
    (`T.Served`), the theorem's verifier accepts, at that statement, the typed value that the one
    fixed reading of F gives: this is `top`'s own last clause. And if a names neither -policy nor
    -no-proof-of-work, the statement passes `servedAt` at F's own three public files.
  `top_served`: so, for a target T that serves every statement which passes `servedAt Z`: if F's
    three public files are Z's, byte for byte, and a names neither option, the verifier accepts.
  `top_own`: and for a target that serves every statement which passes `servedAt` at its own three
    files, the two options are asked and no pin: as above, the three public files are a part of the
    statement at which the verifier accepts, with the bytes with which the reads were answered.
All under the four named hypotheses (`Holes`); `top_served` and `top_own` have beside them the
premise on the target that their lines above name.
What is not claimed: all that the heads of OnBytes/K/Top.lean and OnBytes/K/Served.lean do not
claim. `Served` still stands in three of the holes. A call that ends within limits has named
-policy: of it nothing is said. What is left without -policy is narrow: the parameter file's own
policy is the exact match, or the call is about the reply alone (r + 1 = e = T). The pins speak of
the bytes with which the reads were answered. Z is a letter. Whether `servedAt` gives what a
description needs is open until a hole is proved from it.

-/
import OnBytes.K.Top
import OnBytes.K.ExitServed

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)

variable {T : Target}

/-- The top statement's clauses, and beside its last the test `servedAt`, of the same F and a. -/
theorem top_both (R : Reading T) (H : Holes T R) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (T.Served (stmOf F a.options) →
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧ T.verify (stmOf F a.options) v = true) ∧
      (a.options.policy = none → a.options.noProofOfWork = false →
        servedAt ⟨F.pol, F.lay, F.KL⟩ (stmOf F a.options) = true) := by
  obtain ⟨config, ivk, request, y, proof, a, r, lay, ent, t, p, C, table, further, id, pre, post, e,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, ⟨ac, w, h17⟩, h18, h19,
    hsv⟩ := main_zero_served h
  refine ⟨config, ivk, request, y, proof, a,
    ⟨r.pol, lay, r.KL, r.key, ent, r.request, r.y, r.proof, r.entry⟩, t, id, pre, post, e, h1, h2,
    h12, h14, ?_, ?_⟩
  · exact tie R H _ a.options id h12 h14
      ⟨table, further, r, p, C, rfl, rfl, h3, rfl, rfl, rfl, rfl, rfl, h4, h5, h6, h7, h8, h9, h10,
        h11, h13, h15, h16, ⟨a.options, ac, w, h12, h14, h17⟩, h18, h19⟩
  · intro o1 o2
    apply hsv
    unfold optionsServed
    simp [h12, h14, o1, o2]

/-- For a target that serves every statement which passes `servedAt Z`: three pins and two options.
-/
theorem top_served (Z : Pub) (hT : ∀ x, servedAt Z x = true → T.Served x) (R : Reading T)
    (H : Holes T R) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
        a.options.noProofOfWork = false →
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧ T.verify (stmOf F a.options) v = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, h5, h6⟩ :=
    top_both R H h
  exact ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4,
    fun z1 z2 z3 o1 o2 => h5 (hT _ ((servedAt_pins Z _).2 ⟨z1, z2, z3, h6 o1 o2⟩))⟩

/-- For a target that serves every statement which passes `servedAt` at its own three files: two
options and no pin. -/
theorem top_own (hT : ∀ x : UserStm, servedAt ⟨x.pol, x.lay, x.KL⟩ x = true → T.Served x)
    (R : Reading T) (H : Holes T R) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (a.options.policy = none → a.options.noProofOfWork = false →
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧ T.verify (stmOf F a.options) v = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, h5, h6⟩ :=
    top_both R H h
  exact ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4,
    fun o1 o2 => h5 (hT _ (h6 o1 o2))⟩

end OnBytes.K

#print axioms OnBytes.K.top_both
#print axioms OnBytes.K.top_served
#print axioms OnBytes.K.top_own
