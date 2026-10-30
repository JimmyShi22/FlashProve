-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Readers.lean: What the prover's text of a proximity test
(`stagesAll`, Johnson/Desc/K12/Honest/Stages.lean) reads of the record inside the test besides
running the description's parts on it: three readers. Each is one at two records that agree but for
targets (`Agree`, Wipe.lean). No premise but that.

  `codes_agree`  the codes: the answer at a switch reads these alone (`aAns`)
  `rowOf_agree`, `vecG_wipe`   the claim's coefficients: the fold's rounds read these alone
                 (`aFold`)
  `claimAt_wipe`, `claim_cd`, `lastOut_agree`   the claim in front of the base case, but for its
                 third field: the last stage's rounds read its first two alone (`lastOut`,
                 Johnson/Prover/Link/BodyAll.lean)

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. On these three readers alone: nothing on a part of the description. Nothing on completeness,
soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Wipe
import Johnson.Desc.K12.Honest.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open OnBytes (Statement GroupRow SingleRows Codes)
open OnBytes.Params (IoppStage)
open OnBytes.Slice (vecG)
open VerifiableInference.Desc.K12 (T12 Passing P12 claimAt stageAt)
open Johnson.Prover.Link (PS rowOf lastOut)
open ProofFile.Honest.K10 (wipeSt wipeG)

/-! ## The three readers -/

/-- The codes. -/
theorem codes_agree {t t' : T12} (h : Agree t t') : t.st.codes = t'.st.codes := by
  have h0 : wipeT t = wipeT t' := h
  have h1 := congrArg (fun x : T12 => x.st.codes) h0
  exact h1

/-- The row of the claim that a record passes on. -/
theorem rowOf_agree {t t' : T12} (h : Agree t t') : wipeG (rowOf t) = wipeG (rowOf t') := by
  have hp : wipeP t.pass = wipeP t'.pass := congrArg (·.pass) h
  unfold rowOf
  rcases pass_cases _ _ hp with ⟨a, b⟩ | ⟨r, r', L, a, b, c⟩ | ⟨R, R', n, a, b, -⟩ |
    ⟨out, theta, n, a, b⟩
  · rw [a, b]
  · rw [a, b]
    exact c
  · rw [a, b]
  · rw [a, b]

/-- The fold's rounds read of the claim its coefficients alone. -/
theorem vecG_wipe (s : OnBytes.Slice.Sg) (r r' : GroupRow) (h : wipeG r = wipeG r') :
    vecG s r = vecG s r' := by
  have hc : r.c = r'.c := congrArg (·.c) h
  have hd : r.d = r'.d := congrArg (·.d) h
  funext x
  cases x with
  | inl x => simp only [vecG, hc]
  | inr x => simp only [vecG, hd]

/-- The claim in front of the base case, but for its third field. -/
theorem claimAt_wipe (K : Codes) (c : IoppStage) (r r' : GroupRow) (h : wipeG r = wipeG r') :
    (claimAt K c r).map (fun x => (x.c, x.d)) = (claimAt K c r').map fun x => (x.c, x.d) := by
  have hc : r.c = r'.c := congrArg (·.c) h
  have hd : r.d = r'.d := congrArg (·.d) h
  have hk : r.kept = r'.kept := congrArg (·.kept) h
  unfold claimAt
  rw [hc, hd, hk]
  cases K.base[c.code]? with
  | none => rfl
  | some c₀ =>
    by_cases hb : (c.k != 0 || !r'.kept.isEmpty) = true
    · simp [hb]
    · simp [hb]

/-- The two fields that the last stage's rounds read, at the claim or at the default. -/
theorem claim_cd (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) {t t' : T12} (h : Agree t t') :
    (fun x : VerifiableInference.Desc.Prox.BaseClaim => (x.c, x.d))
        (((stageAt p j cur).bind fun c => claimAt t.st.codes c (rowOf t)).getD
          ⟨#[], #[], (0, 0, 0)⟩) =
      (fun x : VerifiableInference.Desc.Prox.BaseClaim => (x.c, x.d))
        (((stageAt p j cur).bind fun c => claimAt t'.st.codes c (rowOf t')).getD
          ⟨#[], #[], (0, 0, 0)⟩) := by
  rw [codes_agree h]
  cases stageAt p j cur with
  | none => rfl
  | some c =>
    have e := claimAt_wipe t'.st.codes c (rowOf t) (rowOf t') (rowOf_agree h)
    show (fun x : VerifiableInference.Desc.Prox.BaseClaim => (x.c, x.d))
        ((claimAt t'.st.codes c (rowOf t)).getD ⟨#[], #[], (0, 0, 0)⟩) =
      (fun x : VerifiableInference.Desc.Prox.BaseClaim => (x.c, x.d))
        ((claimAt t'.st.codes c (rowOf t')).getD ⟨#[], #[], (0, 0, 0)⟩)
    cases e1 : claimAt t'.st.codes c (rowOf t) with
    | none =>
      cases e2 : claimAt t'.st.codes c (rowOf t') with
      | none => rfl
      | some y => rw [e1, e2] at e; cases e
    | some x =>
      cases e2 : claimAt t'.st.codes c (rowOf t') with
      | none => rw [e1, e2] at e; cases e
      | some y =>
        rw [e1, e2] at e
        exact Option.some.inj e

/-- The last stage's rounds. -/
theorem lastOut_agree (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) {t t' : T12}
    (h : Agree t t') (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) :
    lastOut p j cur o t P col (rowOf t) D = lastOut p j cur o t' P col (rowOf t') D := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj (claim_cd p j cur h)
  unfold lastOut
  simp only [h1, h2]

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.codes_agree
#print axioms ProofFile.Honest.K12.Blind.rowOf_agree
#print axioms ProofFile.Honest.K12.Blind.vecG_wipe
#print axioms ProofFile.Honest.K12.Blind.claimAt_wipe
#print axioms ProofFile.Honest.K12.Blind.claim_cd
#print axioms ProofFile.Honest.K12.Blind.lastOut_agree
