-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontAtShape.lean

What it proves. FrontAsks (ShapeAll.lean), what is asked of the verifier's state in front of a
proximity test whose first fold's mask has come, follows from one Bool on the shape of that state
(frontFiveB, on TestSh) and the three tests that read the rows (stTidyB, stPlainB, claimsB). So
where the shape of a job's state on entry is one term N at every input and whatever precedes the
test, one evaluation of frontFiveB at N, with the three tests, gives FrontAsks at every input and
whatever precedes the test.

Names.
  frontPlainB₀, frontPlain₀_of_B   the clause plain as a test on the thin shape: frontPlainB of
      FrontPlainB.lean (not in the library; see FrontThin.lean's head) without its last conjunct
      oneFitsB, which is on a job of one sending.
  frontFiveB   five of FrontAsks' eight clauses as one Bool on the shape: the codes; doorB; the mask
      has come; plain; pub.
  frontAsks_of_five   the theorem.
  frontAsks_all   at a job whose state on entry has one shape.

By what. thin_batT, frontPubB, frontPub_of_B (FrontThin.lean); thinOf_eq, gpOfS_eq, gpLS_eq
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean). frontPlain₀_of_B's proof follows that of
frontPlain_of_B (FrontPlainB.lean), less the one conjunct.

Limits.
- The case in which the first fold's mask has come, alone: frontFiveB asks it. At a test whose first
  fold sends its own mask frontFiveB is false.
- The plain data Dp are given by the state: they hold the statement whole. The theorem says that
  there are such data; it does not say that they are a function of the shape.
- p.early is a premise.
- frontFiveB is evaluated at no plan here.
- It stands over files that are not in the library yet (ShapeAll.lean and what lies beneath it).
- FrontAsks is on the verifier's state alone: nothing on the prover's data (DataFront), nothing on
  the test's own challenges (FormAsks).
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontThin
import Johnson.Desc.K12.Honest.Shape.TestDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.K12.Thin (thin_batT frontPubB frontPub_of_B)
open ProofFile.Honest.Sh (ThinSh thinSh batThin PlainS plainSh gpOfS gpOfS_eq gpLS gpLS_eq TestSh testSh
  thinOf thinOf_eq claimsB)

variable {W X : Type}

/-- The clause plain as a test on the thin shape. -/
def frontPlainB₀ (p : P12) (a₀ : ThinSh) : Bool :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS p aB (stA p) L with
      | some D =>
        ok (gpLS p (stA p) 0 D) && decide (2 ^ L.logEll = (stA p).C.l) &&
          decide (2 ^ L.logEllZk = (stA p).Z.l)
      | none => false
    | _ => false
  | none => false

/-- **The test's "true" gives the plain data and what is asked of them.** -/
theorem frontPlain₀_of_B (p : P12) (t : T12) (hp : t.pass = .nothing) (he : p.early = true)
    (h : frontPlainB₀ p (thinSh t) = true) :
    ∃ Dp : Plain, ∀ G, t.st.groups[t.g]? = some G →
      gpOf p (batT t G {}) (stA p) (layoutOf t.st G) = some Dp ∧
        ok (gpL p (stA p) {} Dp) = true ∧ 2 ^ (layoutOf t.st G).logEll = (stA p).C.l ∧
        2 ^ (layoutOf t.st G).logEllZk = (stA p).Z.l := by
  unfold frontPlainB₀ at h
  split at h
  · rename_i aB hB
    split at h
    · rename_i L hL
      split at h
      · rename_i D hD
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        cases hg : t.st.groups[t.g]? with
        | none =>
          exfalso
          unfold batThin at hB
          have e0 : (thinSh t).pass = .nothing := by
            show ProofFile.Honest.Sh.thinPass t.pass = _
            rw [hp]
            rfl
          rw [e0] at hB
          split at hB
          · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hB
            have hy' : beginRunS (shD (H2K.Out.dT t [])) t.g = some y := hy
            obtain ⟨x, hx⟩ := beginRun_returns (H2K.Out.dT t []) t.g y hy'
            unfold VerifiableInference.Desc.Ground.beginRunP at hx
            split at hx
            · have hg' : (H2K.Out.dT t []).st.groups[t.g]? = none := hg
              rw [hg'] at hx
              cases hx
            · cases hx
          · cases hB
        | some G =>
          have eT := thin_batT p t G {} aB hp he hg hB
          have eL : L = layoutOf t.st G := by
            have k : (thinSh (batT t G {})).pass = .claim (layoutOf t.st G) := rfl
            rw [eT, hL] at k
            injection k
          subst eL
          have k := gpOfS_eq p (batT t G {}) (stA p) (layoutOf t.st G)
          rw [eT, hD] at k
          obtain ⟨Dp, hDp, eD⟩ := Option.map_eq_some_iff.1 k.symm
          subst eD
          refine ⟨Dp, fun G' hG' => ?_⟩
          obtain rfl : G = G' := Option.some.inj hG'
          refine ⟨hDp, ?_, h2, h3⟩
          rw [← gpLS_eq]
          exact h1
      · cases h
    · cases h
  · cases h

/-- **Five of FrontAsks' eight clauses as one Bool on the shape.** -/
def frontFiveB (p : P12) (K : Codes) (N : TestSh) : Bool :=
  decide (N.core.st.codes = K) &&
  Sh.doorB p (stA p) (stN p) (((laidOf p).take 1).map (·.1)) (lettersOf p (stA p) (stN p)).i
    ((lettersOf p (stA p) (stN p)).n.code, (lettersOf p (stA p) (stN p)).n.maskCode) N &&
  N.mask.isSome &&
  (match N.pass with
    | .nothing => true
    | _ => false) &&
  frontPlainB₀ p (thinOf N) && frontPubB p (thinOf N)

/-- **FrontAsks from the Bool on the shape and the three tests that read the rows.** -/
theorem frontAsks_of_five (J : TestJob W X) (w : W) (fr : Front X) (K : Codes)
    (he : J.p.early = true) (h : frontFiveB J.p K (testSh (J.rec₀ w fr)) = true)
    (ht : stTidyB (J.rec₀ w fr).st = true) (hpl : stPlainB (J.rec₀ w fr).st = true)
    (hc : claimsB (J.rec₀ w fr) = true) : ∃ Dp : Plain, FrontAsks J w fr K Dp := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [thinOf_eq] at h5 h6
  have hp : (J.rec₀ w fr).pass = .nothing := by
    have h4' : (match ProofFile.Honest.Sh.passSh (J.rec₀ w fr).pass with
      | .nothing => true
      | _ => false) = true := h4
    cases hq : (J.rec₀ w fr).pass with
    | nothing => rfl
    | claim _ _ => rw [hq] at h4'; cases h4'
    | single _ _ => rw [hq] at h4'; cases h4'
    | switched _ _ _ => rw [hq] at h4'; cases h4'
  obtain ⟨Dp, hD⟩ := frontPlain₀_of_B J.p _ hp he h5
  exact ⟨Dp, ⟨h1, h2, h3, ht, hpl, hc, hD,
    fun G id hG hm => frontPub_of_B J.p _ hp he h6 G id hG hm⟩⟩

/-- **At a job whose state on entry has one shape**: one evaluation at that shape. -/
theorem frontAsks_all (J : TestJob W X) (K : Codes) (N : TestSh) (he : J.p.early = true)
    (hN : ∀ w fr, testSh (J.rec₀ w fr) = N) (h : frontFiveB J.p K N = true)
    (h3 : ∀ w fr, stTidyB (J.rec₀ w fr).st = true ∧ stPlainB (J.rec₀ w fr).st = true ∧
      claimsB (J.rec₀ w fr) = true) (w : W) (fr : Front X) :
    ∃ Dp : Plain, FrontAsks J w fr K Dp :=
  frontAsks_of_five J w fr K he (by rw [hN]; exact h) (h3 w fr).1 (h3 w fr).2.1 (h3 w fr).2.2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.frontPlainB₀
#print axioms ProofFile.Honest.K12.frontPlain₀_of_B
#print axioms ProofFile.Honest.K12.frontFiveB
#print axioms ProofFile.Honest.K12.frontAsks_of_five
#print axioms ProofFile.Honest.K12.frontAsks_all
