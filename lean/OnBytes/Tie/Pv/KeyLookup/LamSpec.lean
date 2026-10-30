-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/LamSpec.lean: ties between the list Λ of a lookup with parts and the
descriptions of rounds by which the planner's routine is reasoned about: which columns of a row its
description fixes; that the planner's routine, wherever it ends well, adds the rounds of these
descriptions; and the lookup's own shape held against the list of descriptions without Λ in the
statement.

`Lam q S` (Cb/Pv/KeyLookup/Lam.lean) lists a lookup's rounds; a row has a kind, the number `sent` of
scalars that the prover sends, the number n of values of the verifier's draw and a count c of bad
values. `specOf s S r` (OnBytes/Tie/Pv/KeyLookup/LamList.lean) is the description (`RoundSpec`,
OnBytes/Params/PlanningLaws.lean) of the round of a row r, and `lam_list` says that Λ, mapped by
`specOf`, is the list `lookupList` (OnBytes/Params/PlanListsSum.lean). Descriptions and that list
are for proofs only: the program does not import them. `runs_lookup` there ties the list to the
planner's routine `planLookup`: wherever the routine ends well from a state in which nothing is
open, it adds exactly the rounds of that list. BUT `specOf` READS FEW COLUMNS OF A ROW: n nowhere, c
at two kinds, `sent` at two; so `lam_list` alone fixes Λ's length, order and kinds, and not these
columns. This file ties `sent` and n to the description outright, and the column c through the
description's bound, as a ratio against n: c · b = a · n.

  `lam_forall`     what holds of the eight kinds of row holds of every row of Λ.
  `bytesOf`, `valuesOf q`   of a description: the bytes that the prover has sent; the number of
                   values of its draws (drawNZ elements other than 0, the other drawE − drawNZ
                   free), in a field of q elements.
  `spec_msg`       for every row of Λ: the round's bytes are 24 times `sent` IN SHORT FORM
                   (`LRow.short`).
  `spec_vals`      for every row of Λ: the round's draws have n values.
  `BoundIs y c n`, `spec_err`   for every row of Λ at the setting's number of elements: the round's
                   bound is the ratio a / b of two numbers with c · b = a · n; a silent round has c
                   = 0 and n = 1.
  `lam_runs`       the planner's routine `planLookup`, at the sizes of S, wherever it ends well,
                   adds exactly the rounds of `(Lam q S).map (specOf s S)`.
  `sizeOfPort`, `lookupList_port`, `lam_runs_port`   the same at the record that the planner's own
                   caller makes of a lookup's public inputs, in which «all planes are live» is
                   written 0; under mu ≤ 6. (That `sizeOfPort` is the caller's own function is not
                   shown in this file.)
  `round_once`     what the plan holds of a round under the scope `.once`: the bound's error, bytes,
                   draws, work.
  `lamS_vals`, `lamS_msgs`   WITHOUT Λ: round by round, the lookup's verifier's message has as many
                   values as the draws of the description, and the prover's message as many as (the
                   description's bytes / 24) scalars.
  `lamS_errs`      WITHOUT Λ: round by round, the lookup's own error and number of values are in the
                   ratio that the description's bound names: UNDER the premise that the field has as
                   many elements as the setting says.
Under: `lam_runs`: at least one live plane and one part. `lamS_vals`, `lamS_msgs`, `lamS_errs`:
`Pub.Adm` (public numbers and shapes).
What is not claimed: that `planLookup` ends well (`Runs` speaks of the runs that do); that a bound
is right, or that `Bound.ratio a b` is at least a / b; that a round's bound determines the pair (a,
b), so that the round would determine c (`BoundIs` says that there ARE such a and b; different pairs
may give one bound), or that b is not 0; that the number of elements of the field is the setting's
(a premise where it is used); what a plan holds of a round under another scope than `.once`; that a
plan's number, a rounded binary, is at least c / n; a lookup with a shift; anything on the C++
planner. Nor the join with the rounds that the routine itself adds to a plan.
For proofs only. It imports files of both sides.

-/
import OnBytes.Tie.Pv.KeyLookup.LamList
import OnBytes.Tie.Pv.KeyLookup.PubOf
import Cb.Pv.KeyLookup.Lam1Short

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open OnBytes OnBytes.Params

/-- What holds of the eight kinds of row holds of every row of the list. -/
theorem lam_forall (q : ℕ) (S : Pub) (Pr : LRow → Prop)
    (hlkp : Pr ⟨.lkp, 0, q, S.allKeys - 1⟩) (heps : Pr ⟨.eps, 1, q, 1⟩)
    (hvar : ∀ g, Pr ⟨.var, g, q, g - 1⟩) (hy : ∀ dY, Pr ⟨.y, dY + 1, q - 1, dY⟩)
    (hvals : ∀ v, Pr ⟨.vals, v, 1, 0⟩)
    (hjoin : Pr ⟨.join, 0, q ^ S.mu, S.mu * q ^ (S.mu - 1)⟩) (hline : Pr ⟨.line, 0, q, 1⟩)
    (hzero : Pr ⟨.zero, 0, q ^ (S.mu + S.d), (S.mu + S.d) * q ^ (S.mu + S.d - 1)⟩) :
    ∀ r ∈ Lam q S, Pr r := by
  have hpsc : ∀ deg y, ∀ r ∈ psc q deg y, Pr r := by
    intro deg y r hr
    unfold psc at hr
    rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact heps
      · obtain ⟨g, _, rfl⟩ := List.mem_map.1 hr
        exact hvar g
    · rcases y with _ | ⟨dY, vals⟩
      · simp at hr
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact hy dY
        · exact hvals vals
  have htree : ∀ more levels, ∀ r ∈ tree q more levels, Pr r := by
    intro more levels r hr
    obtain ⟨l, _, hr⟩ := List.mem_flatMap.1 hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hpsc _ _ r hr
    · rw [List.mem_singleton.1 hr]
      exact hline
  intro r hr
  simp only [Lam, lamHead, lamParts, lamJoin, lamKeys, lamTable, lamClo, lamZero, lamBits,
    List.mem_append, List.mem_flatMap, List.mem_singleton] at hr
  rcases hr with
    ((((((((rfl | hr) | ⟨_, _, hr⟩) | ⟨_, _, hr⟩) | rfl) | ⟨_, _, hr⟩) | hr) | hr) | rfl) | hr
  · exact hlkp
  · exact hpsc _ _ r hr
  · exact hpsc _ _ r hr
  · exact hpsc _ _ r hr
  · exact hjoin
  · exact htree _ _ r hr
  · exact htree _ _ r hr
  · exact hpsc _ _ r hr
  · exact hzero
  · exact hpsc _ _ r hr

/-- The bytes that the prover has sent in a round. -/
def bytesOf : RoundSpec → ℕ
  | .said _ _ _ _ b _ _ => b
  | .silent _ b _ => b
  | .record _ _ _ => 0

/-- The number of values of a round's draws, in a field of q elements. -/
def valuesOf (q : ℕ) : RoundSpec → ℕ
  | .said _ _ _ d _ _ _ => (q - 1) ^ d.drawNZ * q ^ (d.drawE - d.drawNZ)
  | _ => 1

/-- The description fixes the column `sent`, in short form: 24 bytes a scalar. -/
theorem spec_msg (s : Setting) (S : Pub) (q : ℕ) :
    ∀ r ∈ Lam q S, bytesOf (specOf s S r) = 24 * r.short.sent :=
  lam_forall q S _ (by simp [specOf, bytesOf, LRow.short])
    (by simp [specOf, bytesOf, LRow.short, pscEpsilon])
    (fun g => by simp [specOf, bytesOf, LRow.short, pscVariable])
    (fun dY => by simp [specOf, bytesOf, LRow.short, pscY])
    (fun v => by simp [specOf, bytesOf, LRow.short]) (by simp [specOf, bytesOf, LRow.short])
    (by simp [specOf, bytesOf, LRow.short, lineRound]) (by simp [specOf, bytesOf, LRow.short])

/-- The description fixes the column n. -/
theorem spec_vals (s : Setting) (S : Pub) (q : ℕ) :
    ∀ r ∈ Lam q S, valuesOf q (specOf s S r) = r.n :=
  lam_forall q S _ (by simp [specOf, valuesOf]) (by simp [specOf, valuesOf, pscEpsilon])
    (fun g => by simp [specOf, valuesOf, pscVariable]) (fun dY => by simp [specOf, valuesOf, pscY])
    (fun v => by simp [specOf, valuesOf]) (by simp [specOf, valuesOf])
    (by simp [specOf, valuesOf, lineRound]) (by simp [specOf, valuesOf])

/-- What a description says of a count c of bad values among n values: a round with a verifier's
message: its bound is the ratio a / b of two numbers with c · b = a · n; a silent round: there is no
draw (n = 1) and no bad value. -/
def BoundIs (y : RoundSpec) (c n : ℕ) : Prop :=
  match y with
  | .said _ _ e _ _ _ _ => ∃ a b, e = Bound.ratio a b ∧ c * b = a * n
  | .silent _ _ _ => c = 0 ∧ n = 1
  | .record _ _ _ => False

theorem mul_pow_pred (k q : ℕ) : k * q ^ (k - 1) * q = k * q ^ k := by
  cases k with
  | zero => simp
  | succ k => rw [Nat.add_sub_cancel, Nat.mul_assoc, ← pow_succ]

/-- The description fixes the column c against the column n, at the setting's number of elements. -/
theorem spec_err (s : Setting) (S : Pub) : ∀ r ∈ Lam s.cardE S, BoundIs (specOf s S r) r.c r.n :=
  lam_forall s.cardE S _
    (show ∃ a b, Bound.ratio (S.allKeys - 1) s.cardE = Bound.ratio a b ∧
        (S.allKeys - 1) * b = a * s.cardE
      from ⟨_, _, rfl, rfl⟩)
    (show ∃ a b, fieldError s 1 = Bound.ratio a b ∧ 1 * b = a * s.cardE from ⟨1, s.cardE, rfl, rfl⟩)
    (fun g => show ∃ a b, fieldError s (g - 1) = Bound.ratio a b ∧ (g - 1) * b = a * s.cardE
      from ⟨g - 1, s.cardE, rfl, rfl⟩)
    (fun dY => show ∃ a b, fieldErrorNonzero s dY = Bound.ratio a b ∧ dY * b = a * (s.cardE - 1)
      from ⟨dY, s.cardE - 1, rfl, rfl⟩)
    (fun _ => show (0 : ℕ) = 0 ∧ (1 : ℕ) = 1 from ⟨rfl, rfl⟩)
    (show ∃ a b, fieldError s S.mu = Bound.ratio a b ∧
        S.mu * s.cardE ^ (S.mu - 1) * b = a * s.cardE ^ S.mu
      from ⟨S.mu, s.cardE, rfl, mul_pow_pred _ _⟩)
    (show ∃ a b, fieldError s 1 = Bound.ratio a b ∧ 1 * b = a * s.cardE from ⟨1, s.cardE, rfl, rfl⟩)
    (show ∃ a b, fieldError s (S.mu + S.d) = Bound.ratio a b ∧
        (S.mu + S.d) * s.cardE ^ (S.mu + S.d - 1) * b = a * s.cardE ^ (S.mu + S.d)
      from ⟨S.mu + S.d, s.cardE, rfl, mul_pow_pred _ _⟩)

/-- The planner's routine, wherever it ends well, adds the rounds of the descriptions of the list's
rows. -/
theorem lam_runs (s : Setting) (c : Scope) (S : Pub) (q : ℕ) (hp : S.pl ≠ 0) (hm : S.parts ≠ []) :
    Runs s c 0 0 0 (planLookup (sizeOfPub S)) () ((Lam q S).map (specOf s S)) 0 0 0 := by
  rw [lam_list s S q hp hm]
  exact runs_lookup (sizeOfPub S)

/-- The sizes that the planner's own caller makes of a lookup's public inputs
(OnBytes/Plan/Ranges.lean, `lookupSizes`). -/
def sizeOfPort (p : Lkp.Public) : LookupSize :=
  { d := p.d, mu := p.mu, live := p.live, parts := p.parts }

theorem lookupList_port (s : Setting) (p : Lkp.Public) (hmu : p.mu ≤ 6) :
    lookupList s (sizeOfPort p) = lookupList s (sizeOfPub (pubOf p)) := by
  have e : lookupLive (sizeOfPort p) = lookupLive (sizeOfPub (pubOf p)) := by
    by_cases h : p.live = 0 <;>
      simp [lookupLive, sizeOfPort, sizeOfPub, pubOf, Lkp.Public.planes, h, Nat.min_eq_left hmu]
  unfold lookupList
  rw [e]
  rfl

theorem lam_runs_port (s : Setting) (c : Scope) (p : Lkp.Public) (q : ℕ) (hmu : p.mu ≤ 6)
    (hp : p.planes ≠ 0) (hm : p.parts ≠ []) :
    Runs s c 0 0 0 (planLookup (sizeOfPort p)) () ((Lam q (pubOf p)).map (specOf s (pubOf p)))
      0 0 0 := by
  rw [lam_list s (pubOf p) q hp hm, ← lookupList_port s p hmu]
  exact runs_lookup (sizeOfPort p)

/-- What the plan holds of a round under the scope `.once`. -/
theorem round_once (s : Setting) (n : String) (w : ErrorKind) (e : Bound) (d : Draws) (b r a : ℕ) :
    ((RoundSpec.said n w e d b r a).round s .once).error = e.error ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.msg = b ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.drawE = d.drawE ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.drawNZ = d.drawNZ ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.work = s.workOf w .once := by
  simp [RoundSpec.round, RoundSpec.bound]

section
variable {E : Type} [Field E] [Fintype E] (p : ℕ) (A : Dat E) (P : Pl A) (Ex : Iop.ExtSpec)
  (s : Setting)

theorem adm_pl {S : Pub} {p : ℕ} (h : S.Adm p) : S.pl ≠ 0 := by
  have := h.planes
  omega

theorem adm_parts {S : Pub} {p : ℕ} (h : S.Adm p) : S.parts ≠ [] := by
  intro e
  have := h.some
  simp [Pub.m, e] at this

/-- Round by round the lookup's verifier's message has as many values as the draws of the
description. -/
theorem lamS_vals (hA : A.toPub.Adm p) :
    (A.lamS P Ex).R.shape.chalList =
      (lookupList s (sizeOfPub A.toPub)).map (valuesOf (Fintype.card E)) := by
  rw [(lamS_isL_adm p A P Ex hA).2,
    ← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA), List.map_map]
  exact List.map_congr_left fun r hr => (spec_vals s A.toPub _ r hr).symm

/-- Round by round the prover's message in the clear has as many values as (the description's bytes
/ 24) scalars. -/
theorem lamS_msgs (hA : A.toPub.Adm p) :
    plainList (A.lamS P Ex).R.shape =
      (lookupList s (sizeOfPub A.toPub)).map fun y => Fintype.card E ^ (bytesOf y / 24) := by
  have h := lamS_isS A P Ex hA.planes hA.some (fun i hi => (hA.bits i hi).1) hA.tabs
  unfold IsS at h
  rw [h, ← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA), List.map_map,
    List.map_map]
  refine List.map_congr_left fun r hr => ?_
  show Fintype.card E ^ r.short.sent = Fintype.card E ^ (bytesOf (specOf s A.toPub r) / 24)
  rw [spec_msg s A.toPub _ r hr, Nat.mul_div_cancel_left _ (by decide)]

/-- Round by round the lookup's own error, among the values of its verifier's message, is what the
description's bound says: if the field has as many elements as the setting says. -/
theorem lamS_errs (hA : A.toPub.Adm p) (hq : s.cardE = Fintype.card E) :
    List.Forall₂ (fun (cn : ℕ × ℕ) (y : RoundSpec) => BoundIs y cn.1 cn.2)
      ((A.lamS P Ex).e.toList.zip (A.lamS P Ex).R.shape.chalList)
      (lookupList s (sizeOfPub A.toPub)) := by
  obtain ⟨h1, h2⟩ := lamS_isL_adm p A P Ex hA
  rw [h1, h2, ← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA), List.zip_map',
    List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro r hr
  rw [← hq] at hr
  exact spec_err s A.toPub r hr

end
end Lk6

#print axioms Lk6.spec_err
#print axioms Lk6.lamS_errs
#print axioms Lk6.lam_forall
#print axioms Lk6.spec_msg
#print axioms Lk6.spec_vals
#print axioms Lk6.lam_runs
#print axioms Lk6.lookupList_port
#print axioms Lk6.lam_runs_port
#print axioms Lk6.round_once
#print axioms Lk6.lamS_vals
#print axioms Lk6.lamS_msgs
