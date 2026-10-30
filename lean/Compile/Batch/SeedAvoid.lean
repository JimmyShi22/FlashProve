-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedAvoid.lean: the compiled verifiers of the scheme with batches never query the
auxiliary oracle. (Words of this library: lean/GLOSSARY.md.)

Why. The scheme with isk = (i, seed) (Compile/Batch/SeedStar.lean) derives the committer's coins
through the oracle `OracleName.other` of Compile/Batch/Oracles.lean. The theorem that allows this
(`Rom.deriveWith`) requires that none of the three algorithms of the scheme before the
transformation ever queries that oracle. For the committer and the compiled prover this is read off
the token programs (Compile/Batch/SeedShape.lean). Here it is shown of the verifier, which is an
oracle algorithm: of its parts; of the compiled verifier of one slot without and with the
strict-format check, for every tag, protocol, wire record, statement and proof string
(`avoids_verifyB`, `avoids_verifyBS`); of the three verifiers of Test, Link and Batch with that
check; and of V of Compile/Batch/Star.lean, which is made of these three (`avoids_V`).

Limits: nothing about how many queries a verifier makes, nor about what it accepts.
-/
import Compile.Batch.Star
import Compile.Batch.ForestFacts
import Rom.Derive

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem avoids_askV {o : OracleName} (ho : o ≠ OracleName.other) (q : domOf lam L o) :
    (askTypedOracle (K := K) o q).Avoids OracleName.other :=
  ⟨ho, fun _ => trivial⟩

theorem avoids_nodeV (a b : Dig lam) : (hashTreeNode (K := K) (L := L) a b).Avoids OracleName.other :=
  avoids_askV (by decide) _

theorem avoids_rnodeV (a b : Dig lam) : (rnodeV (K := K) (L := L) a b).Avoids OracleName.other :=
  avoids_askV (by decide) _

theorem avoids_climb {hN : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)}
    (h : ∀ a b, (hN a b).Avoids OracleName.other) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), (climbM hN path j c).Avoids OracleName.other
  | [], _, _ => trivial
  | s :: ss, j, c => by
      unfold climbM
      dsimp only
      split_ifs <;> exact Derive.Avoids.bind (h _ _) fun u => avoids_climb h ss (j / 2) u

theorem avoids_runCheck (c : Check lam L) : (runCheck (K := K) c).Avoids OracleName.other :=
  Derive.Avoids.bind (c := askTypedOracle OracleName.leaf c.inp)
    (g := fun d => (climbM hashTreeNode c.path c.j d).bind fun r => OComp.pure (decide (r = c.root)))
    (avoids_askV (by decide) _)
    fun d => Derive.Avoids.bind (avoids_climb avoids_nodeV _ _ _) fun _ => trivial

theorem avoids_runChecks : ∀ cs : List (Check lam L), (runChecks (K := K) cs).Avoids OracleName.other
  | [] => trivial
  | c :: cs =>
    Derive.Avoids.bind (c := runCheck c)
      (g := fun a => (runChecks cs).bind fun b => OComp.pure (a && b)) (avoids_runCheck c)
      fun _ => Derive.Avoids.bind (avoids_runChecks cs) fun _ => trivial

theorem avoids_reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    (reqCheck (K := K) (L := L) depthReq rtreq slot path c).Avoids OracleName.other := by
  unfold reqCheck
  split_ifs
  · exact Derive.Avoids.bind (c := askTypedOracle OracleName.rleaf (List.ofFn c))
      (g := fun d => (climbM rnodeV path slot d).bind fun r => OComp.pure (decide (r = rtreq)))
      (avoids_askV (by decide) _)
      fun d => Derive.Avoids.bind (avoids_climb avoids_rnodeV _ _ _) fun _ => trivial
  · exact trivial

/-- the recomputed chain of a slot: queries to the Fiat-Shamir oracle and to g of its tag only -/
theorem avoids_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain t cms x salt rtreq s A W embP i ph rts pls).Avoids OracleName.other
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      unfold recomputeChain
      split
      · split
        · exact Derive.Avoids.bind (avoids_askV (by simp) _) fun ans =>
            Derive.Avoids.bind (avoids_chainB t cms x salt rtreq s A W _ _ _ _ pls) fun _ => trivial
        · exact trivial
      · split
        · exact Derive.Avoids.bind (avoids_askV (by simp) _) fun ans =>
            Derive.Avoids.bind (avoids_chainB t cms x salt rtreq s A W _ _ _ _ pls) fun _ => trivial
        · exact trivial
      · split
        · split
          · refine Derive.Avoids.bind (avoids_askV (by simp) _) fun c => ?_
            refine Derive.Avoids.bind (avoids_askV (by simp) _) fun ans => ?_
            exact Derive.Avoids.bind
              (avoids_chainB t cms x salt rtreq s A W _ _ _ _ pls) fun _ => trivial
          · exact trivial
        · exact trivial
      · exact trivial

section Proto
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)

theorem avoids_afterB (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (afterB Q wq embS embE depthReq cms x π ρ rts ph).Avoids OracleName.other := by
  unfold afterB
  split
  · split_ifs
    · refine Derive.Avoids.bind (avoids_runChecks _) fun _ => ?_
      cases ph.slotVal with
      | none => exact trivial
      | some c => exact Derive.Avoids.bind (avoids_reqCheck _ _ _ _ c) fun _ => trivial
    · exact trivial
  · exact trivial

theorem avoids_verifyB : (verifyB t Q wq embS embP xin embE depthReq cms x π).Avoids OracleName.other := by
  refine Derive.Avoids.bind (avoids_chainB t _ _ _ _ _ _ _ _ _ _ _ _) fun r => ?_
  obtain _ | ⟨ρ, rts, ph⟩ := r
  · exact trivial
  · exact avoids_afterB Q wq embS embE depthReq cms x π ρ rts ph

/-- the end of the verifier with the strict-format check, with pruned Merkle paths -/
theorem avoids_afterBO (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph).Avoids OracleName.other :=
  Counts.afterBO (P := fun {_} c _ => OComp.Avoids (S := spec lam K L) OracleName.other c)
    ⟨fun _ _ => trivial, fun h hg => Derive.Avoids.bind h hg, fun h _ => h⟩
    (fun q => avoids_askV (by decide) q) (fun q => avoids_askV (by decide) q)
    (fun q => avoids_askV (by decide) q) (fun q => avoids_askV (by decide) q)
    Q wq embS embE depthReq cms x π ρ rts ph

theorem avoids_verifyBS (sMT sFS : ℕ) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).Avoids OracleName.other := by
  refine Derive.Avoids.bind (avoids_chainB t _ _ _ _ _ _ _ _ _ _ _ _) fun r => ?_
  obtain _ | ⟨ρ, rts, ph⟩ := r
  · exact trivial
  · show (if proofHasStrictFormat sMT sFS Q wq depthReq x π ρ rts ph then
        checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph
      else OComp.pure false).Avoids OracleName.other
    split_ifs
    · exact avoids_afterBO Q wq embS embE depthReq cms x π ρ rts ph
    · exact trivial

end Proto

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)

/-- Test's verifier with the strict-format check -/
theorem avoids_vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    (vTS W sMT sFS cm π).Avoids OracleName.other :=
  avoids_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Link's verifier with the strict-format check -/
theorem avoids_vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    (vLS W sMT sFS cm cm' π).Avoids OracleName.other :=
  avoids_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- a slot's verifier with the strict-format check -/
theorem avoids_vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    (vBS W sMT sFS cm x π).Avoids OracleName.other :=
  avoids_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- the verifier of the scheme of Compile/Batch/Star.lean -/
theorem avoids_V (p : Params) (v : IVK lam L) (x : X) (π : Prf lam L) :
    (V W p v x π).Avoids OracleName.other := by
  unfold V
  split
  · split_ifs
    · exact Derive.Avoids.bind (avoids_vTS W _ _ _ _) fun _ =>
        Derive.Avoids.bind (avoids_vLS W _ _ _ _ _) fun _ =>
          Derive.Avoids.bind (avoids_vBS W _ _ _ _ _) fun _ => trivial
    · exact trivial
  · exact trivial

end Seed
end Compile.Batch
