-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqParts.lean: THE SMALLNESS TEST: parts of three of the library's texts BY
NAME (four definitions), so that statements and proofs can speak of them: `powersF` and `foldSums`
(OnBytes/Model/Tail.lean) and `eqWeights` (Johnson/Desc/First/TailClaims/Equations.lean).
Definitions, and small lemmas. Lemmas; none of the library's goals.

  `powers_size`      the n powers are n
  `laidP x tl`       what `powersF` lays at the batching element x; `powersF_eq`
  `sumsAt tl mu v`   the sums over the columns of matrix mu under the weights v; `sumsAt_size`
  `laidS tl mu`      what `foldSums` lays for matrix mu; `foldSums_eq`
  `startS tl`        the data with no sum laid yet; `eqWeights_eq`
  `lessBeta_ents`, `lessBeta_slots`   the constant form has no entry and no slot
`powersF_eq`, `foldSums_eq` and `eqWeights_eq` say that the library's text IS the named parts: each
is proved by unfolding alone (`rfl`). With `oneRow`, `firstsOf`, `takenOf` of
Johnson/Desc/K8/Honest/EqReturns.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims

theorem powersLoop_size (x : E) : ∀ (n : Nat) (c : E) (a : Array E),
    (powersLoop x n c a).size = a.size + n
  | 0, _, _ => rfl
  | n + 1, c, a => by
    unfold powersLoop
    rw [powersLoop_size x n, Array.size_push]
    omega

/-- The n powers are n. -/
theorem powers_size (x : E) (n : Nat) : (powers x n).size = n := by
  unfold powers
  rw [powersLoop_size]
  simp

/-- What `powersF` lays at the batching element x. -/
def laidP (x : E) (tl : HTailF2) : HTailF2 :=
  { tl with
    vt := powers x tl.tau, vp := powers x tl.tau
    eqFirst := firstsOf tl
    rowX := tl.shp.map fun s => powers (powE x tl.stepF) s.mS
    loX := tl.shp.map fun _ => #[oneE] }

theorem powersF_eq (tl : HTailF2) (F : Fork) :
    tl.powersF F =
      if !F.thetaDrawnF || F.planClaimsF == 0 || !oneRow tl then none
      else some (laidP F.theta tl) := rfl

/-- The sums over the columns of matrix mu under the weights v. -/
def sumsAt (tl : HTailF2) (mu : Nat) (v : Array E) : Array E :=
  (Array.range (tl.mats.getD mu {}).k).map fun c =>
    foldColumn tl.cfF ((tl.cfFirst.getD mu 0 + c) * tl.tau) tl.tau v

theorem sumsAt_size (tl : HTailF2) (mu : Nat) (v : Array E) :
    (sumsAt tl mu v).size = (tl.mats.getD mu {}).k := by
  unfold sumsAt
  simp

/-- What `foldSums` lays for matrix mu. -/
def laidS (tl : HTailF2) (mu : Nat) : HTailF2 :=
  { tl with
    foldTakenF := (takenOf tl).set! mu true
    gamX := tl.gamX.set! mu (sumsAt tl mu tl.vp)
    gamV := tl.gamV.set! mu (if tl.vt == tl.vp then sumsAt tl mu tl.vp else sumsAt tl mu tl.vt) }

theorem foldSums_eq (tl : HTailF2) (mu : Nat) :
    tl.foldSums mu =
      if decide (mu ≥ tl.NM) || (takenOf tl).getD mu true then none else some (laidS tl mu) := rfl

/-- The data with no sum laid yet. -/
def startS (tl : HTailF2) : HTailF2 :=
  { tl with gamX := Array.replicate tl.NM #[], gamV := Array.replicate tl.NM #[] }

theorem eqWeights_eq (tl : HTailF2) :
    eqWeights tl = (EqM.ask "weightsF:1030" fun F => tl.powersF F) >>= fun tl =>
      EqM.get "weightsF:1031"
        ((List.range tl.NM).foldlM (fun (x : HTailF2) mu => x.foldSums mu) (startS tl)) := rfl

theorem lessBeta_ents (x : E) : (lessBeta x).ents = #[] := by
  unfold HTailF2.lessBeta Aff.ofConst
  rfl

theorem lessBeta_slots (x : E) : (lessBeta x).slots = #[] := by
  unfold HTailF2.lessBeta Aff.ofConst
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.powers_size
#print axioms VerifiableInference.Desc.First.K8.Honest.powersF_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.sumsAt_size
#print axioms VerifiableInference.Desc.First.K8.Honest.foldSums_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.eqWeights_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.lessBeta_ents
#print axioms VerifiableInference.Desc.First.K8.Honest.lessBeta_slots
