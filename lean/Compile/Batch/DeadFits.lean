-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadFits.lean: for a well-formed wire record, the relation `agF W` says at every
search over nonces what `FitsSh` (Compile/Batch/DeadProver.lean) requires.

`FitsSh`: two answers that the relation relates at the query of an attempt both fail that search's
check, and the attempt is not the last; where a round has no proof-of-work record, it relates no two
answers at its query. `agF W` (Compile/Batch/SpecOneCall.lean) relates two answers that are both
failed proof-of-work attempts, and not the last; it reads the check, and whether the attempt is the
last, off the plain part of a Fiat-Shamir query (`tryInfo`). The search of round i writes the nonce
for the number m into that plain part (g.put m α). The two agree by g.get (g.put m α) = m for m ≤
g.more (`GrW.OK.get_put`).

  `failsAt_some`, `failsAt_none`  `failsAt`, where `tryInfoT` is known.
  `fitsSh_agF`  For the rounds that are left of a protocol t, if the embedding embP of their plain
                parts into those of t preserves `tryInfo` (hE), and under `RoundsQueryLayout.OKG`. For the
                whole protocol embP is the identity and hE holds by definition.

Notation:
  `g`: a `GrW C P` (Iop/BatchWire.lean), the record of a round with proof-of-work bits; C: the
    verifier messages of the round; P: the plain part that the Fiat-Shamir query of the round holds;
  `g.more`, `g.put k α`, `g.get α` (fields of `GrW`): the honest prover tries the nonces 0, ..,
    more; the plain part with the nonce for the number k written over its nonce; the number for
    which the nonce of a plain part stands;
  `α`: a plain part, of type P;
  `chal`: a map `Blk lam W.K → C`, from the W.K blocks of an answer to a verifier message
    (`WireRB.chal`, Iop/BatchWire.lean);
  `tryInfo` (Compile/Batch/SpecOneCall.lean): the proof-of-work check, and whether the attempt is
    the last, read off the plain part of a Fiat-Shamir query; `tryInfoT W t`: `tryInfo` at the
    protocol t.

Limits: nothing on hash blocks: that the check depends on block 0 only is another hypothesis
(`Test0`).
-/
import Compile.Batch.DeadProver

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)

theorem failsAt_some {t : Tag} {q : FbIn lam L t} {x : (Blk lam W.K → Bool) × Bool}
    (h : tryInfoT W t q.plain = some x) (bl : Blk lam W.K) :
    failsAt W t q bl = (!x.1 bl && !x.2) := by
  unfold failsAt
  rw [h]

theorem failsAt_none {t : Tag} {q : FbIn lam L t}
    (h : tryInfoT W t q.plain = none) (bl : Blk lam W.K) : failsAt W t q bl = false := by
  unfold failsAt
  rw [h]

/-- what agF says at a Fiat-Shamir oracle `fb t` or a ghost name `fbw t j` of it -/
theorem agF_fb {t : Tag} {q : FbIn lam L t} {r r' : rngOf lam W.K (.fb t)}
    (h : agF W (.fb t) q r r' ∨ ∃ j, agF W (.fbw t j) q r r') :
    failsAt W t q r.1 = true ∧ failsAt W t q r'.1 = true :=
  h.elim id fun ⟨_, h⟩ => h

/-- Under `g.OK` and hE: `FitsLoop` holds of `agF W` at one search. -/
theorem fitsLoop_agF {t : Tag} {C P : Type} {chal : Blk lam W.K → C}
    {emb : P → PlainPart (shapeOf L t) (annOf L t)} {g : GrW C P} (hg : g.OK)
    (hE : ∀ α, tryInfoT W t (emb α) = some (fun bl => g.ok (chal bl), decide (g.more ≤ g.get α)))
    (α : P) :
    FitsLoop (agF W) chal t emb α g := by
  intro m q r r' hm hq ha
  obtain ⟨h1, h2⟩ := agF_fb W ha
  have hi := hE (g.put m α)
  rw [← hq, hg.get_put m α hm] at hi
  rw [failsAt_some W hi] at h1 h2
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at h1 h2
  exact ⟨h1.1, h2.1, h1.2⟩

theorem noFb_agF {t : Tag} {z : PlainPart (shapeOf L t) (annOf L t)} (hE : tryInfoT W t z = none)
    (q : FbIn lam L t) (r r' : rngOf lam W.K (.fb t)) (hq : q.plain = z) :
    ¬ agF W (.fb t) q r r' := by
  intro h
  have h1 : failsAt W t q r.1 = true := h.1
  rw [failsAt_none W (hq ▸ hE)] at h1
  exact nomatch h1

/-- Under `RoundsQueryLayout.OKG`, hE: the relation fits all searches of the rounds that are left. -/
theorem fitsSh_agF (t : Tag) :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)),
      RoundsQueryLayout.OKG s A Ws → (∀ z, tryInfoT W t (embP z) = tryInfo s A Ws z) →
      FitsSh (agF W) t s A Ws embP
  | [], _, _, _, _, _ => trivial
  | _ :: s, (_, A), (w, Ws), embP, hW, hE => by
    refine ⟨⟨fun α g hg => ?_, fun hn α q r r' hq => ?_⟩,
      ⟨fun α g hg => ?_, fun hn α q r r' hq => ?_⟩,
      fitsSh_agF t s A Ws _ hW.2 fun z => hE (.inr z)⟩
    · refine fitsLoop_agF W (hW.1.grJ_ok g hg) (fun α' => ?_) α
      rw [hE]
      show w.grJ.map _ = _
      rw [hg]
      rfl
    · refine noFb_agF W ?_ q r r' hq
      rw [hE]
      show w.grJ.map _ = _
      rw [hn]
      rfl
    · refine fitsLoop_agF W (hW.1.gr0_ok g hg) (fun α' => ?_) α
      rw [hE]
      show w.gr0.map _ = _
      rw [hg]
      rfl
    · refine noFb_agF W ?_ q r r' hq
      rw [hE]
      show w.gr0.map _ = _
      rw [hn]
      rfl

end Compile.Batch.Dead
