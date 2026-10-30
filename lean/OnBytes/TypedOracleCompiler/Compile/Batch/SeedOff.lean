-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/SeedOff.lean: a part of the instance that stands in no query and is read
off the trace. `mem_of_accepted` bears it as it is, but for its hypothesis of stability.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. A verifier's decision can read a value (seeds) that is hashed nowhere: it is the oracle's
answers on a chain apart. `mem_of_accepted` (Sound.lean) takes the reading of the external string,
`extY` : trace → external roots → `E.Str`, as a free parameter, which the lane's state reads at each
prefix. So the value rides with the external string.

  `ExtSpec.withS E Sd`
      The kind of external strings E with a value in Sd beside the string; positions, symbols and
      reading are E's: no position reads the value.
  `mem_off`
      Instances are pairs (a, s). In the use that is meant a enters the first query (through xin,
      xout) and s does not; no hypothesis says so: xin may read s. The lane's state takes its s from
      the reading off the trace (`extS`), the decision takes the instance's. Outside `EM`, `EF` and
      the lane's step event, if the compiled verifier accepts (a, s): either the value read off the
      trace is not s, or the statement is in the language. The laws of the state function are asked
      at the instance's own s alone.
  `lane_off_ok1`
      That lane obeys the laws of a lane, from the joint law at one seed for all slots. This is the
      form to use.
  `lane_off_ok`
      The same from the given state function's joint law at every string and all instances. So the
      lane's step event is as rare as any lane's.

Limits. The hypothesis `hstab` of `mem_off` speaks of every Fiat-Shamir query at the tag such that
the roots occur in `pre ++ [q]`, and a Merkle answer is an occurrence: at `extS` it asks that at
every such query the value read off the prefix is the final one. The hypothesis as it stands is more
than a rule on makers of queries can give: the form to use is `mem_off_ours` (SoundOurs.lean). For
the string, `EM` pays for stability. For a value read off a chain apart nothing pays: a maker of
queries may ask a first query that names the root before it asks that chain. The first way out of
`mem_off`, that the value read off the trace is not s, is not shut here. It is thought, not proved,
that a checker which has itself recomputed s from the oracle would shut it: that wants an `extS`
which reads the chain apart off a trace (ReadRun.lean has one) and that the checker's own queries,
which lie in the trace, give it s; the second is in no file of this folder. Not said: any `extS`;
any protocol; soundness of anything.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- external strings of the kind E with a value in Sd beside them; no position reads the value -/
def ExtSpec.withS (E : ExtSpec) (Sd : Type) : ExtSpec :=
    ⟨E.Str × Sd, E.Pos, E.Sym, fun y p => E.rd y.1 p⟩

/-- A part of the instance that stands in no query, read off the trace. -/
theorem mem_off (t : Tag) {Y0 Sd : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof (Y0 × Sd) (ExtSpec.withS E Sd))
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
    (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε
      (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) (fun o => (xout o).map fun a => (a, d))
      (fun tr cms => (extY tr cms, extS tr cms))).step tr)
    (cms : List (Dig lam)) (x : Y0 × Sd) (π : OneProtocolProof lam Q) (inst : ℕ → Y0)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0, x.2) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1), x.2) (.atP τ) = false →
          State y (inst τ.idx, x.2) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y s τ, ¬ Lg x y → State y (inst (Q.loc.shape.length - 1), x.2) (.full τ) = false →
      Q.loc.accept x (y, s) τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms ∧ extS pre cms = extS tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : extS tr cms ≠ x.2 ∨ Lg x (extY tr cms) :=
  mem_of_accepted t Q wq embS embP xin embE hOK hloc hco
    (Lg := fun x (y : E.Str × Sd) => y.2 ≠ x.2 ∨ Lg x y.1)
    (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) prjS hprjS prjP hprjP
    (fun o => (xout o).map fun a => (a, d)) (fun tr cms => (extY tr cms, extS tr cms)) ε
        hM hF hS cms x π
    (fun i => (inst i, d)) (fun i => by
      show (xout (instX L (xin x) i)).map (fun a => (a, d)) = some (inst i, d)
      rw [hx i]
      rfl) hlate
    (fun y hL => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      show State y.1 (inst 0, y.2) _ = false
      rw [not_not.1 h1]
      exact hst1 y.1 h2)
    (fun y τ m hL h => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      have e : y.2 = x.2 := not_not.1 h1
      show State y.1 (inst τ.idx, y.2) _ = false
      have h' : State y.1 (inst (τ.idx - 1), y.2) (.atP τ) = false := h
      rw [e] at h' ⊢
      exact hst2 y.1 τ m h2 h')
    (fun y τ hL h => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      have e : y.2 = x.2 := not_not.1 h1
      have h' : State y.1 (inst (Q.loc.shape.length - 1), y.2) (.full τ) = false := h
      rw [e] at h'
      exact hst3 y.1 y.2 τ h2 h')
    hrun
    (fun pre q a post htr hocc => Prod.ext (hstab pre q a post htr hocc).1
        (hstab pre q a post htr hocc).2)
    hagree

/-- That lane obeys the laws of a lane, if the given state function obeys the joint law at every
string and all instances: the lane's state at (y, s) and the instance (a, _) is the given one at y
and (a, s). So its step event is as rare as any lane's. -/
theorem lane_off_ok {t : Tag} {Y0 Sd : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof (Y0 × Sd) (ExtSpec.withS E Sd)}
    {ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann}
    {prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)} {ε : Err Q.loc.shape}
    {State : E.Str → Y0 × Sd → PTr Q.loc.shape → Bool} {xout : Option X → Option Y0} {d : Sd}
    {extY : Tc W → List (Dig lam) → E.Str} {extS : Tc W → List (Dig lam) → Sd} {N : ℕ}
    (hws : RoundsQueryLayout.OKG Q.loc.shape Q.ann ws)
    (hj : ∀ y (x : Fin N → Option (Y0 × Sd)), JointLaw N Q.loc.shape Q.ann ε fun j =>
        (x j).map (State y)) :
    (laneOf W t Q ws prjS prjP ε (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ)
      (fun o => (xout o).map fun a => (a, d)) (fun tr cms => (extY tr cms, extS tr cms))).OK N :=
  laneOf_ok hws fun y x => by
    have h := hj y.1 fun j => (x j).map fun u => (u.1, y.2)
    have e : (fun j => ((x j).map fun u => (u.1, y.2)).map (State y.1)) =
        fun j => (x j).map ((fun (y : E.Str × Sd) (x : Y0 × Sd) τ => State y.1 (x.1, y.2) τ) y) :=
            funext fun j => by
      cases x j <;> rfl
    rw [e] at h
    exact h

/-- The same from the joint law at one seed for all slots: lane_off_ok asks the law at vectors with
a different seed in each slot; its proof uses one seed for all: that is what soundness "record by
record" gives. -/
theorem lane_off_ok1 {t : Tag} {Y0 Sd : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof (Y0 × Sd) (ExtSpec.withS E Sd)}
    {ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann}
    {prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)} {ε : Err Q.loc.shape}
    {State : E.Str → Y0 × Sd → PTr Q.loc.shape → Bool} {xout : Option X → Option Y0} {d : Sd}
    {extY : Tc W → List (Dig lam) → E.Str} {extS : Tc W → List (Dig lam) → Sd} {N : ℕ}
    (hws : RoundsQueryLayout.OKG Q.loc.shape Q.ann ws)
    (hj : ∀ y s (x : Fin N → Option Y0), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map fun a =>
        State y (a, s)) :
    (laneOf W t Q ws prjS prjP ε (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ)
      (fun o => (xout o).map fun a => (a, d)) (fun tr cms => (extY tr cms, extS tr cms))).OK N :=
  laneOf_ok hws fun y x => by
    have h := hj y.1 y.2 fun j => (x j).map Prod.fst
    have e : (fun j => ((x j).map Prod.fst).map fun a => State y.1 (a, y.2)) =
        fun j => (x j).map ((fun (y : E.Str × Sd) (x : Y0 × Sd) τ => State y.1 (x.1, y.2) τ) y) :=
            funext fun j => by
      cases x j <;> rfl
    rw [e] at h
    exact h

end TypedOracleCompiler.Compile.Batch
