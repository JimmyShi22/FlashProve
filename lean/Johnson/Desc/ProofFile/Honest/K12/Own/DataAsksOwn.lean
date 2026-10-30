-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/DataAsksOwn.lean

`DataAsks` FROM `DataFront`, WHERE THE FIRST FOLD SENDS ITS OWN TABLE: the twin of `dataAsks_of_one`
(AsksWhole.lean in the folder above).

  `door_facts_own`       what the door's tests give where no mask has come: the twin of `door_facts`
  `dataAsks_of_one_own`  the statement

Of `FrontAsks` the law spends door, tidy, plainRows alone, and of `planB` batCut: so it takes these by name, with hm
in `came`'s stead, and asks neither `claims`, `pub` nor `plain`.

HOW EACH PREMISE WOULD BE PAID AT jobKO. hD: `door_O` (KeyTenLinesKernel.lean) with `shape_doorOmegaF`. hm: by text.
ht, hp: `three_O` and `three_doorOmegaF`. hB: a closed line, not typed. f1: from `drawsFit`. Dt: cols, state,
trees OPEN: a twin of `dataThree_of_front`; allSay OPEN.

Limits. Conditional. `DataFront` is what stays. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.K12.Honest.OwnFoldDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.Sh (doorB claimsB testSh runRows_plain testFrontOwn_of batOwes_of cameB tBat)

variable {W X : Type}

/-- **What the door's tests give where no mask has come.** G: the group under test. row: the batched
row. -/
theorem door_facts_own {p : P12} {a next : Fmt.M1.Stage} {t₀ : T12} {i nn : ℕ × ℕ} {dB : Fmt.Drawn}
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i nn (testSh t₀) = true)
    (hm : t₀.mask = none) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true) :
    ∃ G row, t₀.st.groups[t₀.g]? = some G ∧ tBat p t₀ dB = batT t₀ G row := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := h
  have h4' : (match t₀.mask with
    | some id => cameB a (testSh t₀).core t₀.g i id
    | none => (testSh t₀).core.st.oracles.length == (testSh t₀).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFrontOwn_of h1 hm (by simpa using h4') ht hpl
  obtain ⟨row, -, hb⟩ := bat5_yes_own H _ (batOwes_of h2 H.group) hB [⟨[], dB⟩] fB
  exact ⟨G, row, H.group, getD_of_ok hb⟩

/-- **`DataAsks` at the challenges, where the first fold sends its own table.** -/
theorem dataAsks_of_one_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hD : doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
      (lettersOf J.p (stA J.p) (stN J.p)).i
      ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = none) (ht : stTidyB (J.rec₀ w fr).st = true)
    (hp : stPlainB (J.rec₀ w fr).st = true)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (f1 : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (Dt : DataFront J w fr C Dp c R) : DataAsks J w fr C D Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun row' L' h G' hG' => ?_⟩
  obtain ⟨G, row, hG, eB⟩ := door_facts_own hD hm ht (fun G hG => runRows_plain hp hG) hB f1
  have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  rw [eR] at h ⊢
  have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
  injection h' with h1 h2
  subst h1 h2
  exact Dt.allSay G hG'

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.door_facts_own
#print axioms ProofFile.Honest.K12.Own.dataAsks_of_one_own
