-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/TowerOf.lean: a proximity test behind its first stage as a function of the list of
its stages: a maker by recursion, and the conditions of all its blocks from a test on numbers and
one condition on counts.

A stage is given in numbers, with its radius (`Sg`, OnBytes/Slice/Stage.lean; from the planner's
records by `stageOf` and `radiusOf`, Johnson/Top/H/StageJ.lean). The data of a test are `TowR`
(Cb/Pv/Tower/Test.lean), a family over the joint at which a test begins and the further oracle in
its input. That oracle hangs on what the first block is. So the maker returns the test together
with the code of that oracle (`TowB`). Where the sizes of two neighbouring stages do not fit it
returns nothing. The blocks are those of Johnson/Top/H/StageValues.lean. Definitions, statements
and proofs.
Main names:
  `jAt s e sl`: the joint at which the stage s begins, at the radius e and the form sl.
  `TowB a`: a test from the joint a, with the code of the further oracle in its input and that
    code's leaves.
  `towOf bC bZ l s e sl`: the test whose first stage is s and whose later stages are l; the last
    of all stages is the last step.
  `goodL l s e`: the test on numbers: neighbours fit (`CsFit`), every stage has its sizes in order
    and its radius below the Johnson radius.
  `CntL bC bZ l s e`: the one condition that is asked: `CountsAt` at every stage.
  `towOf_some`: under `goodL` the maker returns a test.
  `towOf_hypK`, `towOf_reads`, `towOf_know`: under `goodL` and `CntL` what it returns meets the
    conditions of all its blocks; what locality asks holds; it is knowledge sound.
Limits: the first stage of a test on a group of sent messages is not treated here. `CntL` is not
proved here. The limits of Johnson/Top/H/StageValues.lean hold here.

-/
import Johnson.Top.H.StageValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Cb.Pv.Tower

/-- The joint at which a stage begins. -/
abbrev jAt (s : Sg) (e : ℕ) {St : Type} (sl : Slf GE St s.cIn.J) : LdJoint GE :=
  wholeJ (s.par s.Z.l) sl e

/-- A test from the joint a, with the code of the further oracle in its input. -/
structure TowB (a : LdJoint GE) : Type 1 where
  Pw : Type
  Cw : LdCode GE Pw
  /-- the leaf of a native position of that code -/
  lfW : Cw.NP → a.P
  T : TowR a Cw.nat

variable (bC bZ : Sg → ℕ → ℕ)

/-- The test whose first stage is s and whose later stages are l. -/
noncomputable def towOf : (l : List (Sg × ℕ)) → (s : Sg) → (e : ℕ) → {St : Type} →
    (sl : Slf GE St s.cIn.J) → Option (TowB (jAt s e sl))
  | [], s, e, _, sl =>
    some ⟨s.Ps, s.cIn, Sum.elim id id,
      TowR.base (jAt s e sl) s.t (Sum.elim id id) s.d (bC s e + bZ s e) (lstJ s e)⟩
  | x :: l, s, e, _, sl =>
    if hf : CsFit s x.1 then
      (towOf l x.1 x.2 ((swOf hf sl).D e).sl').map fun r =>
        ⟨s.Ps, (s.par s.Z.l).Cw, id,
          TowR.step (s.par s.Z.l) sl e (1, 1) (swOf hf sl) r.Cw x.1.Ps (Sum.elim id id) r.lfW s.d
            (fun _ => lstJ s e) (fun _ => bC s e) (fun _ => bZ s e) (fun _ => bZ s e) x.2
            (lstJ x.1 x.2) r.T⟩
    else none

/-- The test on numbers. -/
def goodL : List (Sg × ℕ) → Sg → ℕ → Bool
  | [], s, e => sizedB s && inJB s e
  | x :: l, s, e => decide (CsFit s x.1) && (sizedB s && inJB s e) && goodL l x.1 x.2

/-- The condition on counts, at every stage. -/
def CntL : List (Sg × ℕ) → Sg → ℕ → Prop
  | [], s, e => CountsAt s e (bC s e) (bZ s e)
  | x :: l, s, e => CountsAt s e (bC s e) (bZ s e) ∧ CntL l x.1 x.2

theorem good_head : ∀ {l : List (Sg × ℕ)} {s : Sg} {e : ℕ}, goodL l s e = true →
    s.Sized ∧ InJ s e
  | [], _, _, h => by
    simp only [goodL, Bool.and_eq_true] at h
    exact ⟨sized_of h.1, inJ_of h.2⟩
  | _ :: _, _, _, h => by
    simp only [goodL, Bool.and_eq_true] at h
    exact ⟨sized_of h.1.2.1, inJ_of h.1.2.2⟩

theorem towOf_some : ∀ (l : List (Sg × ℕ)) (s : Sg) (e : ℕ) {St : Type}
    (sl : Slf GE St s.cIn.J), goodL l s e = true → (towOf bC bZ l s e sl).isSome = true
  | [], _, _, _, _, _ => rfl
  | x :: l, s, e, _, sl, h => by
    simp only [goodL, Bool.and_eq_true, decide_eq_true_eq] at h
    unfold towOf
    rw [dif_pos h.1.1, Option.isSome_map]
    exact towOf_some l x.1 x.2 _ h.2

theorem towOf_hypK : ∀ (l : List (Sg × ℕ)) (s : Sg) (e : ℕ) {St : Type}
    (sl : Slf GE St s.cIn.J), goodL l s e = true → CntL bC bZ l s e →
    ∀ r, towOf bC bZ l s e sl = some r → r.T.HypK
  | [], s, e, _, sl, h, hc, r, hr => by
    obtain ⟨hs, hj⟩ := good_head h
    obtain rfl := Option.some.inj hr
    have k := baseCodes_joh hs hj hc
    exact LdJoint.BaseHypK.mk k.laws hj.1 k.mca k.list
  | x :: l, s, e, _, sl, h, hc, r, hr => by
    obtain ⟨hs, hj⟩ := good_head h
    simp only [goodL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs', hj'⟩ := good_head h.2
    unfold towOf at hr
    rw [dif_pos h.1.1] at hr
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    exact And.intro (reform_hypK sl hs hj hc.1)
      (And.intro (swOf_hypK h.1.1 sl e hs hs' hj') (towOf_hypK l x.1 x.2 _ h.2 hc.2 r' hr'))

theorem towOf_reads : ∀ (l : List (Sg × ℕ)) (s : Sg) (e : ℕ) {St : Type}
    (sl : Slf GE St s.cIn.J), goodL l s e = true →
    ∀ r, towOf bC bZ l s e sl = some r → r.T.Reads
  | [], _, _, _, _, _, r, hr => by
    obtain rfl := Option.some.inj hr
    exact trivial
  | x :: l, s, e, _, sl, h, r, hr => by
    simp only [goodL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs', _⟩ := good_head h.2
    unfold towOf at hr
    rw [dif_pos h.1.1] at hr
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    exact And.intro (swOf_reads h.1.1 sl e hs') (towOf_reads l x.1 x.2 _ h.2 r' hr')

/-- What the maker returns is knowledge sound. -/
theorem towOf_know (l : List (Sg × ℕ)) (s : Sg) (e : ℕ) {St : Type} (sl : Slf GE St s.cIn.J)
    (h : goodL l s e = true) (hc : CntL bC bZ l s e) (r : TowB (jAt s e sl))
    (hr : towOf bC bZ l s e sl = some r) : r.T.toEnd.Know :=
  r.T.know (towOf_hypK bC bZ l s e sl h hc r hr)

end Johnson.Top.H

#print axioms Johnson.Top.H.towOf_some
#print axioms Johnson.Top.H.towOf_hypK
#print axioms Johnson.Top.H.towOf_know
