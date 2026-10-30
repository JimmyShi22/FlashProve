-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Lift.lean: from "the two fillings yield the same lists" to
"the two fillings agree at the run" (`AgreeAt`, Honest/K3/Law/Statements.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `real_agree` (Honest/K3/FastLaw/Real.lean) speaks of an
input, a structure of points and lists of challenges as letters, under hypotheses on sizes, lengths
and the shift's words. `AgreeAt R B` speaks of one course R, that is, one run of a lookup's stages:
of the input, the points in front of each stage, the run's own challenges and mask entries. This
file shows the hypotheses of the first at a course that passes `Fit` (the tests on the lookup's
numbers; as many challenges in front as the place says; challenges that the rounds can sample).

What is shown, by the file's sections.
  1. `ok_ofTriple`, `fit_ok`, `elemAt_ok`, `theta_ok`: the shift's words are below the prime.
  2. `take_len`: at a stage with end values the run has a challenge for every variable.
  3. `ptsSized`: the points in front of a stage have their sizes.
  4. `agreeAt_of`: the step from equal lists to `AgreeAt`, for any two fillings that are written at
     `Hidden` (Honest/K3/Stages.lean).
  5. `agreeAt_real`: conditional on `FoNums.ok h` and `Fit R`: at a proof file's lookup of shape h
     the filling that folds tables agrees, at the run, with a course whose summands are the
     specification's.

Hypotheses that remain, in `agreeAt_real`.
  `hok`: `FoNums.ok h`, the library's test on the shape.
  `F`: `Fit R`.
  `hf`, `hJ`: the course's face is `faceOf h`, and its summands are `(specJobsF h lm jLK).asked`.
In the theorems on the way. `H`: (in `agreeAt_of`, beside `hJ` and `F`) the two fillings yield the
same lists at the points in front of every stage. `hs`, `hk`, `he`: (in `take_len`, beside `F`) the
stage is one of the row's; its call is k; the call has end values. `hi`, `hD`: (in `elemAt_ok`) the
round lies behind the first list; the elements of the second list's rounds have words below the
prime. `h`: (in `ok_ofTriple`) the three words are below the prime. `fit_ok` has a hypothesis
without a name, in front of an arrow (`drawsFit L ds = true`).

Users. `site_agree` (Honest/K3/FastLaw/Sites.lean).

Limits. `AgreeAt` asks equality as read; more is shown on the way (equal lists of words) and is not
stated. That the course's face is `faceOf h` and its summands are `(specJobsF h lm jLK).asked` is
assumed. No statement of this file says that either filling is right.
An instance of the hypotheses of `agreeAt_real`: the course `Rr` of
Honest/K3/Law/SpecRealMember.lean [not in this library] (by evaluation): its face and its summands
are these by definition, and two tests there evaluate `FoNums.ok` and `Fit`.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Real
import Johnson.Desc.ProofFile.Honest.K3.Law.StageFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E zeroE okE)
open VerifiableInference.Desc (fieldPrimeWord)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.Part.MaskedSum (Call Ends)
open ProofFile.Honest.K3.Law

/-! ## 1 The shift's words -/

theorem ok_ofTriple (x : UInt64 × UInt64 × UInt64)
    (h : (decide (x.1 < fieldPrimeWord) && decide (x.2.1 < fieldPrimeWord) && decide (x.2.2 < fieldPrimeWord)) = true) :
    okE (E.ofTriple x) = true := h

/-- Challenges that the rounds can sample have their elements' words below the prime. -/
theorem fit_ok : ∀ (L : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit L ds = true →
    ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true
  | [], [], _, d, hd, _, _ => by simp at hd
  | [], _ :: _, h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _, _, _ => by simp [drawsFit] at h
  | c :: L, R :: Rs, h, d, hd, x, hx => by
    simp only [drawsFit, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd'
    · have h1 := h.1
      simp only [drawFit, Bool.and_eq_true] at h1
      exact ok_ofTriple x (by simpa using List.all_eq_true.1 h1.1.2 x hx)
    · exact fit_ok L Rs h.2 d hd' x hx

/-- The first element of a round that lies behind the first list has words below the prime, where
all elements of the second list's rounds have. -/
theorem elemAt_ok (T D : List Fmt.Drawn) (i : Nat) (hi : T.length ≤ i)
    (hD : ∀ d ∈ D, ∀ x ∈ d.elems, okE (E.ofTriple x) = true) : okE (elemAt (T ++ D) i) = true := by
  unfold elemAt elemsAt
  rw [List.getElem?_append_right hi]
  cases hd : D[i - T.length]? with
  | none => rfl
  | some d =>
    have hm : d ∈ D := List.mem_of_getElem? hd
    show okE ((d.elems.map E.ofTriple).headD zeroE) = true
    cases he : d.elems with
    | nil => rfl
    | cons x l => exact hD d hm x (by rw [he]; exact List.mem_cons_self)

variable {W : Type}

theorem theta_ok (R : Course W) (F : Fit R) (s : Stage) :
    okE (ptsOf R.f R.a.base (R.front s).heard).theta = true := by
  show okE (if R.f.shifted then
    elemAt (R.t.heard ++ R.ds.take (firstRound R.f s)) (roundAt R.f R.a.base .shift) else zeroE) =
      true
  split
  · refine elemAt_ok _ _ _ ?_ fun d hd x hx =>
      fit_ok _ _ F.draws d (List.mem_of_mem_take hd) x hx
    unfold roundAt
    rw [F.base]
    omega
  · rfl

/-! ## 2 A challenge for every variable -/

theorem take_len (R : Course W) (F : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call} {e : Ends}
    (hk : s.call R.f = some k) (he : k.ends = some e) :
    ((R.r s).take k.vs.length).length = k.vs.length := by
  have hce : (R.call s).ends = some e := by rw [call_ends, shapeAt_of hk, he]
  have hcv : (R.call s).vs.length = k.vs.length := by
    have := congrArg List.length (call_vs_d R s)
    rw [shapeAt_of hk] at this
    simpa using this
  have hlen : (R.draws s).length = k.vs.length + 3 := by
    have h1 := drawsOk_stage F hs hk
    unfold ProofFile.Honest.SumLaw.drawsOk at h1
    have h2 := congrArg List.length (eq_of_beq h1)
    rw [entries_drawE, hce] at h2
    simp at h2
    omega
  have hall : (R.call s).all.length = k.vs.length + 1 := by
    unfold Call.all
    rw [hce]
    simp [hcv]
  have hr : (R.r s).length = k.vs.length + 1 := by
    show (((ProofFile.Honest.drawnE (R.draws s)).drop 1).take (R.call s).all.length).length = _
    rw [List.length_take, List.length_drop, hall]
    unfold ProofFile.Honest.drawnE
    rw [List.length_map, hlen]
    omega
  rw [List.length_take, hr]
  omega

/-! ## 3 The points' sizes -/

theorem ptsSized (f : LFace) (v base : Nat) (heard : List Fmt.Drawn) :
    PtsSized f v (ptsOf f base heard) :=
  ⟨fun m _ => Spec.size_keyPt f base heard 0 m, fun l _ => Spec.size_tabPt f base heard l,
    Spec.size_zeroPt f base heard⟩

/-! ## 4 From equal lists to agreement at the run -/

/-- **Conditional on `Fit R`, and on H: two fillings that yield the same lists at the points in
front of every stage agree at the run.** A: the course's; B: the other. Instances of `Fit`:
Honest/K3/Law/Members.lean (by evaluation). No instance of H is exhibited beside this theorem;
`agreeAt_real` shows H for its two fillings. -/
theorem agreeAt_of (R : Course Ask) (A B : LookJobs Hidden) (hJ : R.J = A.asked) (F : Fit R)
    (H : ∀ s ∈ stages R.f, ∀ k, s.call R.f = some k → ∀ w : Hidden,
      (∀ rs : List E, rs.length < k.vs.length →
        (A.job s).round w (ptsOf R.f R.a.base (R.front s).heard) rs =
          (B.job s).round w (ptsOf R.f R.a.base (R.front s).heard) rs) ∧
      (∀ rs mk : List E, rs.length = k.vs.length →
        (A.job s).inY w (ptsOf R.f R.a.base (R.front s).heard) rs mk =
            (B.job s).inY w (ptsOf R.f R.a.base (R.front s).heard) rs mk ∧
          (A.job s).ends w (ptsOf R.f R.a.base (R.front s).heard) rs =
            (B.job s).ends w (ptsOf R.f R.a.base (R.front s).heard) rs)) :
    AgreeAt R B.asked := by
  intro s hs k hk
  obtain ⟨h1, h2⟩ := H s hs k hk (R.t.input (R.front s).heard)
  refine ⟨fun n hn => ?_, fun e he => ?_⟩
  · have hl : ((R.r s).take n).length < k.vs.length :=
      Nat.lt_of_le_of_lt (List.length_take_le _ _) hn
    have e1 : (R.job s).round R.t.input (R.front s) ((R.r s).take n) =
        (A.job s).round (R.t.input (R.front s).heard) (ptsOf R.f R.a.base (R.front s).heard)
          ((R.r s).take n) := by
      show (R.J.job s).round _ _ _ = _
      rw [hJ]
      rfl
    rw [e1, h1 _ hl]
    rfl
  · have hl := take_len R F hs hk he
    obtain ⟨i1, i2⟩ := h2 ((R.r s).take k.vs.length) (R.masks s) hl
    have e1 : (R.job s).inY R.t.input (R.front s) ((R.r s).take k.vs.length) (R.masks s) =
        (A.job s).inY (R.t.input (R.front s).heard) (ptsOf R.f R.a.base (R.front s).heard)
          ((R.r s).take k.vs.length) (R.masks s) := by
      show (R.J.job s).inY _ _ _ _ = _
      rw [hJ]
      rfl
    have e2 : (R.job s).ends R.t.input (R.front s) ((R.r s).take k.vs.length) =
        (A.job s).ends (R.t.input (R.front s).heard) (ptsOf R.f R.a.base (R.front s).heard)
          ((R.r s).take k.vs.length) := by
      show (R.J.job s).ends _ _ _ = _
      rw [hJ]
      rfl
    rw [e1, e2, i1, i2]
    exact ⟨rfl, rfl⟩

/-! ## 5 At a proof file's lookup -/

/-- **Conditional on `FoNums.ok h` and `Fit R`: at a course whose face is that of a proof file's
lookup of shape h and whose summands are the specification's at the library's own numbers, the
filling that folds tables, with its table read off the face, agrees at the run.** An instance: the
course `Rr` of Honest/K3/Law/SpecRealMember.lean [not in this library] (by evaluation). The two
hypotheses also have instances apart (Honest/K3/FastLaw/RealMember.lean [not in this library];
Honest/K3/Law/Members.lean). -/
theorem agreeAt_real (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (lm jLK : Nat)
    (R : Course Ask) (hf : R.a.face = faceOf h) (hJ : R.J = (specJobsF h lm jLK).asked)
    (F : Fit R) : AgreeAt R (fastJobs (faceOf h) (Fast.rowOfFace (faceOf h))).asked := by
  refine agreeAt_of R _ _ hJ F fun s hs k hk w => ?_
  have hf' : R.f = faceOf h := hf
  have ht := theta_ok R F s
  rw [hf'] at hs hk ht ⊢
  obtain ⟨a1, a2⟩ := real_agree h hok lm jLK w _ ht (ptsSized (faceOf h) h.v R.a.base _) s hs k hk
  exact ⟨fun rs hl => (a1 rs hl).symm, fun rs mk hl =>
    ⟨((a2 rs mk hl).1).symm, ((a2 rs mk hl).2).symm⟩⟩

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.fit_ok
#print axioms ProofFile.Honest.K3.FastLaw.elemAt_ok
#print axioms ProofFile.Honest.K3.FastLaw.theta_ok
#print axioms ProofFile.Honest.K3.FastLaw.take_len
#print axioms ProofFile.Honest.K3.FastLaw.ptsSized
#print axioms ProofFile.Honest.K3.FastLaw.agreeAt_of
#print axioms ProofFile.Honest.K3.FastLaw.agreeAt_real
#print axioms ProofFile.Honest.K3.FastLaw.ok_ofTriple
