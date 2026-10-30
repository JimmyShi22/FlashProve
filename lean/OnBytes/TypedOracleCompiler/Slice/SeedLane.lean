-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedLane.lean: a second written protocol, without an instance and with local
rounds alone, as a lane whose state is a property of the external string and of the verifier's
messages; and what follows outside the named set of OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean if that
protocol's chain runs in the trace.

Why. A value that a chain of its own draws from an outer root (a record's seeds) can be bad for the
string under that root (two members of its list have the same answers). That hangs on the whole
string, so no local verifier decides it. The sibling's road has a lemma that needs no decision
(`no_coll`, OnBytes/TypedOracleCompiler/Compile/Batch/LaneStays.lean): outside the two clashes and the step event of
the lane whose state is "bad y ρ", if the chain runs in the trace and yields the verifier's messages
ρ, then bad is false of the string that the trace determines and ρ. This file says it for a written
protocol (`Written`, OnBytes/TypedOracleCompiler/Slice/PlainClause.lean) and a reading, with that lane as the second
lane of `batBadOff`.
 - `slotVal_none_local`: a chain of local rounds alone that has not joined a shared round does not
   join one;
 - `Written.laneBad ZT R εT bad`: the lane;
 - `batBadOff_bad_false`: outside `batBadOff` at that second lane, if ZT's chain under the root cm
   runs in the trace and yields ρ, then `bad (R.at W tr cm) ρ = false`. Asked: ZT has a round; what
   it writes of a plain part is read back.

Main definition: `Written.laneBad`.
Main theorems: `slotVal_none_local`, `batBadOff_bad_false`.

Not claimed. That the lane obeys the laws of a lane, which `batBadOff_rare` asks as a hypothesis:
that the protocol's wiring is lawful and, for the state "bad", a count of the protocol's verifier's
messages at every string. No protocol, no `bad` and no way from ρ to a value are given. That any run
holds the chain. What the heads of BatchClauseOff.lean and LaneStays.lean do not claim. The compiler
under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.BatchClauseOff
import OnBytes.TypedOracleCompiler.Slice.PlainClause

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A chain of local rounds alone that has not joined a shared round does not join one. -/
theorem slotVal_none_local {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (ws : RoundsQueryLayout lam K s (RoundSplits.allLocal s))
        (embP : PlainPart s (RoundSplits.allLocal s) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
        (ph ph' : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      ph.slotVal = none →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s (RoundSplits.allLocal s) ws embP i ph rts pls)
        (some (ρ, RTs, ph')) →
      ph'.slotVal = none
  | [], _, _, _, ph, ph', _, _, _, _, hc, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hc
  | r :: s, (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), hc, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ :=
        runsIn_chainB_cons (a := RAnn.allLocal r) (A := RoundSplits.allLocal s) h
      refine slotVal_none_local s ws _ (i + 1) ph₁ ph' rts' pls ρ RTs ?_ hr
      cases hv with
      | f1 root ans hk => rfl
      | f2 ρ root ans hk => rfl
      | join ρ rtj rt0 c ans hk hg => cases hk
      | f5 ρ0 c root ans hk => cases hk
      | f3 ρ0 c root ans hk => cases hc
      | f2' ρ c root ans hk => cases hc

end

variable {I A Sd : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}

/-- A written protocol without an instance as a lane whose state is "bad y ρ": 0 until all
verifier's messages are there; judged at the string as R reads it. It judges every chain under the
protocol's tag, whatever its first query's salt and plain part, at the string under the first of
that query's outer roots. -/
def Written.laneBad (ZT : Written W) (R : Reading L W.embE) (εT : Err ZT.P.shape)
    (bad : (Fin L.wordLength → L.Symbol) → Rho ZT.P.shape → Bool) : Lane W :=
  laneOf W ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq.sh ZT.prjS ZT.prjP εT (stBad bad)
    (fun _ => some ()) fun tr cms => R.at W tr (cms.getD 0 default)

/-- Outside the named set with that lane as its second: if the second protocol's chain under the
root cm runs in the trace and yields the verifier's messages ρ, then "bad" is false of the string
that R reads off the trace under cm and ρ. Asked: the second protocol has a round, and what it
writes of a plain part is read back. -/
theorem batBadOff_bad_false (Z : WrittenB W) (R : Reading L W.embE)
    (extS : Tc W → List (Dig lam) → Sd) (d : Sd) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → A × Sd → PTr Z.Q.loc.shape → Bool) (ZT : Written W)
    (εT : Err ZT.P.shape) (bad : (Fin L.wordLength → L.Symbol) → Rho ZT.P.shape → Bool)
    (hne : ZT.P.shape ≠ []) (hP : ∀ z, ZT.prjP (ZT.embP z) = some z) (tr : Tc W) (cm : Dig lam)
    (hB : ¬ batBadOff Z R extS d ε State (ZT.laneBad R εT bad) tr)
    (salt : Bits) (rtreq : Dig lam) (roots : List (Dig lam)) (plains : Plains ZT.P.shape)
    {ρ : Rho ZT.P.shape} {rts : RootsOfChain lam ZT.P.shape} {ph : Phase lam}
    (hr : RunsIn tr (recomputeChain (K := W.K) ZT.t [cm] none salt rtreq ZT.P.shape
      (RoundSplits.allLocal ZT.P.shape) ZT.wq.sh ZT.embP 0 .first roots plains) (some (ρ, rts, ph))) :
    bad (R.at W tr cm) ρ = false := by
  obtain ⟨hM, hF, -, hS2, -⟩ := not_bad3 hB
  exact no_coll ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) hne ZT.wq ZT.embP (fun _ => none) bad ZT.prjS
    ZT.prjP hP (fun _ => some ()) (fun tr cms => R.at W tr (cms.getD 0 default)) εT hM hF hS2
    [cm] () salt rtreq 0 roots plains (fun _ => ()) (fun _ => rfl)
    (fun _ _ h => absurd rfl h) hr
    (fun c hc => by
      rw [slotVal_none_local ZT.P.shape ZT.wq.sh ZT.embP 0 .first ph roots plains ρ rts rfl hr]
        at hc
      cases hc)
    (fun pre q a post l cur htr ho => R.at_before htr hM (ours_cms _ a ho _ (by simp)))

end TypedOracleCompiler.Slice
