-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Plus.lean: a protocol over external strings of the kind E, read as one
over "E with a value beside the string" (`ExtSpec.withS`, SeedOff.lean), has the same compiled
verifier.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. In a lane the one thing that sees the trace is the reading of the external string. So a value
that is read off the trace (in the use that is meant: a record's seeds) has to ride in `E.Str`: the
protocol of `mem_off` (SeedOff.lean) is over `withS E Sd`. With this file a protocol over E need not
change its type for that: the step to `withS` stays inside one lemma.

  `plusP`, `plusQ`
      Q's shape, blinded, extReads, reads, annotation; `accept x y τ` is Q's `accept x y.1 τ`.
  `plusE`, `plusW`
      The wire: `build f` is (the old `build f`, d), d a fixed value; all else is the same.
  `plusPi`
      A proof string for Q as one for `plusQ Q`: the same nine fields (`OneProtocolProof lam Q` and `OneProtocolProof lam
      (plusQ Q Sd)` are two types: one structure at two parameters).
  `plus_isLocal`, `plus_coherent`, `plus_okg`
      The three laws carry over.
  `verifyB_plus`, `verifyBS_plus`
      The compiled verifier (and the strict one) of `plusQ Q` at `plusW wq d` and `plusPi π` is that
      of Q at wq and π: one term.
  `mem_off_at`
      `mem_off_ours` (SoundOurs.lean) for a protocol over any E: the run is `verifyB` at Q itself;
      the lane is `laneOf` at `plusQ Q Sd` (a `Lane W` names no E).

Limits. All that SeedOff.lean and SoundOurs.lean leave out.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.SoundOurs

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}
variable {Y : Type} {E : ExtSpec}

def plusP (Q : InteractiveOracleProof Y E) (Sd : Type) : InteractiveOracleProof Y (ExtSpec.withS E Sd) where
  shape := Q.shape
  blinded := Q.blinded
  extReads := Q.extReads
  reads := Q.reads
  accept := fun x y τ => Q.accept x y.1 τ

def plusQ (Q : BatchInteractiveOracleProof Y E) (Sd : Type) : BatchInteractiveOracleProof Y (ExtSpec.withS E Sd) :=
    ⟨plusP Q.loc Sd, Q.ann⟩

def plusE {Sd : Type} (w : WireE E) (d : Sd) : WireE (ExtSpec.withS E Sd) where
  all := w.all
  which := w.which
  leaf := w.leaf
  depth := w.depth
  build := fun f => (w.build f, d)
  dec := w.dec
  pr := w.pr

def plusW {K : ℕ} {Sd : Type} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (d : Sd) :
    ProtocolQueryLayout lam K (plusQ Q Sd) :=
  ⟨wq.sh, plusE wq.ext d, wq.decO, wq.nOpen, wq.maxDepth⟩

def plusPi {Q : BatchInteractiveOracleProof Y E} (π : OneProtocolProof lam Q) (Sd : Type) : OneProtocolProof lam (plusQ Q Sd) :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path, π.rsalt⟩

theorem plus_isLocal {Q : BatchInteractiveOracleProof Y E} (Sd : Type) (h : Q.loc.IsLocal) :
    (plusQ Q Sd).loc.IsLocal :=
  fun x y y' τ τ' h1 h2 h3 h4 => h x y.1 y'.1 τ τ' h1 h2 h3 h4

theorem plus_coherent {Q : BatchInteractiveOracleProof Y E} (Sd : Type) (h : Q.ann.Coherent) :
    (plusQ Q Sd).ann.Coherent := h

theorem plus_okg {K : ℕ} {Sd : Type} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q} (d : Sd)
    (h : wq.OKG) : (plusW wq d).OKG :=
  ⟨h.sh, ⟨h.ext.nodup, h.ext.complete, fun f p a hf => h.ext.build_rd f p a hf⟩, h.opens, h.depth⟩

set_option smartUnfolding false in
/-- One term. -/
theorem verifyB_plus {Sd : Type} (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q) (d : Sd)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (dR : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    verifyB t (plusQ Q Sd) (plusW wq d) embS embP xin embE dR cms x (plusPi π Sd) =
      verifyB t Q wq embS embP xin embE dR cms x π := rfl

set_option smartUnfolding false in
theorem verifyBS_plus {Sd : Type} (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (d : Sd)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (dR : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    verifyOneProtocol sMT sFS t (plusQ Q Sd) (plusW wq d) embS embP xin embE dR cms x (plusPi π Sd) =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE dR cms x π := rfl

/-- mem_off_ours for a protocol over any kind of external strings: the run is the compiled
verifier's at Q itself. -/
theorem mem_off_at (t : Tag) {Y0 Sd : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof (Y0 × Sd) E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y0 × Sd → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y0 × Sd → E.Str → Prop} (State : E.Str → Y0 × Sd → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y0) (d : Sd)
    (extY : Tc W → List (Dig lam) → E.Str) (extS : Tc W → List (Dig lam) → Sd)
    (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (laneOf W t (plusQ Q Sd) wq.sh prjS prjP ε
      (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) (fun o => (xout o).map fun a => (a, d))
      (fun tr cms => (extY tr cms, extS tr cms))).step tr)
    (cms : List (Dig lam)) (x : Y0 × Sd) (π : OneProtocolProof lam Q) (inst : ℕ → Y0)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0, x.2) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1), x.2) (.atP τ) = false →
          State y (inst τ.idx, x.2) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y τ, ¬ Lg x y → State y (inst (Q.loc.shape.length - 1), x.2) (.full τ) = false →
      Q.loc.accept x y τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms ∧ extS pre cms = extS tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : extS tr cms ≠ x.2 ∨ Lg x (extY tr cms) :=
  mem_off_ours t (plusQ Q Sd) (plusW wq d) embS embP xin embE (plus_okg d hOK)
      (plus_isLocal Sd hloc) (plus_coherent Sd hco)
    State prjS hprjS prjP hprjP xout d extY extS ε hM hF hS cms x (plusPi π Sd) inst hx
        hlate hst1 hst2
    (fun y _ τ => hst3 y τ)
    ((verifyB_plus t Q wq d embS embP xin embE (W.dReq t) cms x π).symm ▸ hrun) hstab hagree

end TypedOracleCompiler.Compile.Batch
