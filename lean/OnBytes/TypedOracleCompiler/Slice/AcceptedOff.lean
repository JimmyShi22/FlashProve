-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/AcceptedOff.lean: the lemma on one accepted string for an instance of which one
part stands in no query and is read off the trace.

The sibling's road has this for `mem_of_accepted` (`mem_off`,
OnBytes/TypedOracleCompiler/Compile/Batch/SeedOff.lean). This file has it for `accepted_at_ours`
(OnBytes/TypedOracleCompiler/Slice/AcceptedOurs.lean), whose two hypotheses on the reading are the weaker ones: the
tie between reading and trace is asked at the accepted string's own openings, stability at its own
chain's queries.

Instances are pairs (a, s). The part a enters the first query; s does not. In a lane the one thing
that sees the trace is the reading of the external strings, so s rides beside them: the protocol is
over `ExtSpec.withS E Sd`, external strings of the kind E with a value in Sd beside them, which no
position reads. The lane's state takes its s from a reading off the trace (`extS`, a free
parameter); the decision takes the instance's own. The three laws of the state function are asked AT
THE INSTANCE's OWN s.

Main theorem: `accepted_off`: outside the two clashes and the lane's lucky steps, if the compiled
verifier accepts (a, s) with all its queries in the trace, then the value read off the trace is not
s, or the statement is in the language. Under conditions: those of `accepted_at_ours`, with the
three laws of the state function at s, and stability asked of both readings.

Not claimed. No `extS` is given. That `extS` is stable at our own chain's queries is a hypothesis;
for a value that a maker can ask for late nothing gives it. That a checker can shut the first way
out is not shown. The protocol is over `ExtSpec.withS E Sd`: for a protocol over E itself a
transport is wanted, which is not here. Nothing on soundness of any protocol. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.AcceptedOurs
import OnBytes.TypedOracleCompiler.Compile.Batch.SeedOff

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- A part of the instance that stands in no query, read off the trace, with both hypotheses on
the readings asked at the accepted string's own openings and its own chain's queries alone. d: a
fixed value in the place of s where a query's field is read back. -/
theorem accepted_off (t : Tag) {Y0 Sd : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof (Y0 × Sd) (ExtSpec.withS E Sd)) (wq : ProtocolQueryLayout lam W.K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
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
    (hst3 : ∀ y s τ, ¬ Lg x y →
      State y (inst (Q.loc.shape.length - 1), x.2) (.full τ) = false →
      Q.loc.accept x (y, s) τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
      tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms ∧ extS pre cms = extS tr cms)
    (hagree : ∀ p op, π.ext p = some op →
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE op.sym, op.salt⟩ →
      E.rd (extY tr cms) p = op.sym) : extS tr cms ≠ x.2 ∨ Lg x (extY tr cms) :=
  accepted_at_ours t Q wq embS embP xin embE hOK hloc hco
    (Lg := fun x (y : E.Str × Sd) => y.2 ≠ x.2 ∨ Lg x y.1)
    (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) prjS hprjS prjP hprjP
    (fun o => (xout o).map fun a => (a, d)) (fun tr cms => (extY tr cms, extS tr cms)) ε hM hF hS
    cms x π (fun i => (inst i, d))
    (fun i => by
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
    (fun pre q a post l cur htr ho =>
      Prod.ext (hstab pre q a post l cur htr ho).1 (hstab pre q a post l cur htr ho).2)
    hagree

end TypedOracleCompiler.Slice
