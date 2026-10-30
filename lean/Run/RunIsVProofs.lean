-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsVProofs.lean: the proofs of the statements of Run/RunIsV.lean (under their hypotheses, an
evaluation on a file is the definition's run of "the parser's tree, then the typed verifier over the
one oracle").

Trees of queries, their run and the coding over the one oracle: the head of Run/RunIsV.lean.
-/
import Run.RunIsV

set_option autoImplicit false

namespace Run
open ZKCP Rom

theorem run_draws : Spec.run_draws := by
  intro lam α c
  induction c with
  | pure a => exact Iff.rfl
  | query q k ih => exact forall_congr' ih
  | sample n k _ => exact Iff.rfl

/-- brought into the syntax of ZKCP/Defs.lean: the same result -/
theorem det_ofRom {lam : ℕ} {α : Type} (f : Oracle lam) :
    ∀ (c : Rom.OComp (rom lam) α), (ofRom c).det f = c.det (famOne f)
  | .pure _ => rfl
  | .query _ q k => det_ofRom f (k (f q))
  | .sample _ k => det_ofRom f (k 0)

/-- A typed tree without coins, coded over the one oracle and brought into the syntax of
ZKCP/Defs.lean, runs to the point mass at its result at the typed oracles read out. -/
theorem run_exit {S : OSpec} {lam : ℕ} {α : Type} (m : OracleCoding S lam) (f : Oracle lam)
    (c : Rom.OComp S α) (h : c.NoCoin) :
    (ofRom (c.overOne m)).run f = PMF.pure (c.det (readBlocks m (famOne f))) := by
  rw [ZKCP.OComp.run_of_noCoin f _
        ((run_draws lam α _).2 (drawsNoCoin_ofRom _ (noCoin_overOne m c h))),
    det_ofRom, det_overOne]

/-- what is done with the parser's output, run at f -/
theorem run_afterV {S : OSpec} {lam : ℕ} {IVK X Pf : Type} (m : OracleCoding S lam)
    (Vt : IVK → X → Pf → Rom.OComp S Bool) (f : Oracle lam) (ivk : IVK)
    (x : X) (hV : ∀ ivk x π, (Vt ivk x π).NoCoin) :
    ∀ v : Option Pf, (afterV (exitV m Vt) ivk x v).run f = PMF.pure (verdictV m Vt f ivk x v)
  | none => rfl
  | some π => run_exit m f (Vt ivk x π) (hV ivk x π)

/-- a tree that runs to a point mass, then a second tree -/
theorem run_bind_of {lam : ℕ} {α β : Type} (f : Oracle lam)
    (c : ZKCP.OComp lam α) (g : α → ZKCP.OComp lam β) (v : α) (w : β)
    (e : c.run f = PMF.pure v) (e' : (g v).run f = PMF.pure w) :
    (c.bind g).run f = PMF.pure w := by
  rw [run_bind, e, PMF.pure_bind, e']

theorem run_bare : Spec.run_bare := fun _ _ _ _ _ _ m Vt p f ivk x b v hV e =>
  run_bind_of f (p.parse ivk x b) (afterV (exitV m Vt) ivk x) v (verdictV m Vt f ivk x v)
    e (run_afterV m Vt f ivk x hV v)

theorem run_bare_lax : Spec.run_bare_lax := fun S X Y E Q m Vt spec T N hN f ivk x b hV =>
  run_bare S 256 (List (Iop.Dig 256)) X (Compile.Batch.OneProtocolProof 256 Q) ByteArray m Vt
    (paOfLax spec T N hN) f ivk x b (keep ivk (parseLaxW (m := Id) (hI f) (spec x) T b)) hV
    (paL_of_run f X Y E Q spec T N hN ivk x b)

/-- the two ways of saying what is done with the parser's output -/
theorem after_eq {lam : ℕ} {I X W IVK ISK Pf : Type}
    (A : Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) :
    WrO.after A ivk x = afterV A.V ivk x := by
  funext v
  cases v <;> rfl

theorem run_exit_V : Spec.run_exit_V := fun _ _ _ _ _ _ _ _ _ m At p =>
  ⟨rfl, funext fun ivk =>
      funext fun x =>
        funext fun b => congrArg (fun g => (p.parse ivk x b).bind g) (after_eq (exitOf m At) ivk x)⟩

theorem run_isV : Spec.run_isV := fun S lam I X W IVK ISK Pf B m At p f ivk x b v hV e => by
  rw [(run_exit_V S lam I X W IVK ISK Pf B m At p).2]
  exact run_bare S lam IVK X Pf B m At.V p f ivk x b v hV e

theorem run_isV_lax : Spec.run_isV_lax := fun S I X W ISK Y E Q m At spec T N hN f ivk x b hV =>
  run_isV S 256 I X W (List (Iop.Dig 256)) ISK (Compile.Batch.OneProtocolProof 256 Q) ByteArray m At
    (paOfLax spec T N hN) f ivk x b (keep ivk (parseLaxW (m := Id) (hI f) (spec x) T b)) hV
    (paL_of_run f X Y E Q spec T N hN ivk x b)

end Run
