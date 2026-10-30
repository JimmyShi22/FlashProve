-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/NoOther.lean: which oracles the compiled verifier's run asks at all. It
never asks the spare oracle `OracleName.other`.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. A checker of a file can be: type the file, then run the typed verifier over one hash oracle.
That no typed query in the log of the verifier's run has a public string (the strings of the calls
169) has two halves. One is about codes: a public string is the code of no typed point but of
`OracleName.other` at itself; it is not here. The other is here: the run never asks `OracleName.other`.

  `vNames t o`
      The names that a compiled verifier at the tag t may ask: leaf, node, rleaf, rnode, fb t, g t:
      at its own tag alone. Not: ann, other, the ghost names fbw, and fb or g at another tag.
  `vNames_ne`
      So o ≠ other, o ≠ ann, o ≠ fbw t' k.
  `counts_asksIn`
      "Every query has the property P" is one of the library's abstract counts (`Counts`,
      Compile/OctopusRom.lean; the number is not looked at). So `Counts.climbM`, `Counts.reqCheck`,
      `Counts.afterBO` (ForestFacts.lean) serve as they are.
  `asksIn_chainB`
      The chain, at every annotation (local, joining, shared rounds): fb t and, in the joining
      round, g t. (`chainB_lo`, OursFirst.lean, is the case of local rounds alone and says more: fb
      t alone.)
  `asksIn_runCheck`, `asksIn_runChecks`, `asksIn_reqCheck`, `asksIn_afterB`, `asksIn_afterBO`
      What follows the chain, in both forms: path by path, and the forests with pruned sets of
      paths.
  `asksIn_verifyB`, `asksIn_verifyBS`
      For every protocol Q, wire wq and all arguments: on every path, whatever the answers, every
      query's name is in `vNames t`. The tests of the strict format ask nothing: they are a `Bool`.
  `verifyB_log`, `verifyBS_log`
      The same of a log: every entry e of `((verify…).withTrace.det F).2`, at every family F of
      oracle functions, has `vNames t e.1`.
  `verifyB_log_ne`, `verifyBS_log_ne`
      So `e.1 ≠ OracleName.other` (and ≠ ann, ≠ fbw t' k).
  `asksIn_vT`, `asksIn_vL`, `asksIn_vB`, `asksIn_vTS`, `asksIn_vLS`, `asksIn_vBS`
      The six verifiers of the scheme at a whole wire, at the tags test, link, onl.
  `asksIn_chainAt`, `chainAt_log'`
      `chainAt` (ReadRun.lean) at every annotation.

Limits. Nothing on which points are asked at these names (no property of the inputs). Nothing on the
prover, the honest side or an adversary: they may ask `OracleName.other`. Nothing on a typing that asks the
one oracle before the run: its queries are not typed queries. Nothing on strings or codes: that no
point of leaf … g t has a public string is the other half. The forms of the verifier that are
functions of the oracle functions (`verifyF`, `verifyT`, `verifyP`) have no log.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Octopus
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the names that a compiled verifier at the tag t may ask -/
def vNames (t : Tag) : OracleName → Prop
  | .leaf => True
  | .node => True
  | .rleaf => True
  | .rnode => True
  | .fb t' => t' = t
  | .g t' => t' = t
  | .ann => False
  | .other => False
  | .fbw _ _ => False

theorem vNames_ne {t : Tag} {o : OracleName} (h : vNames t o) : o ≠ OracleName.other ∧ o ≠ OracleName.ann ∧ ∀ t' k,
    o ≠ OracleName.fbw t' k := by
  cases o <;> first
    | exact h.elim
    | exact ⟨fun e => OracleName.noConfusion e, fun e => OracleName.noConfusion e, fun _ _ e => OracleName.noConfusion e⟩

/-- "every query has the property P" as an abstract count: the number is not looked at -/
theorem counts_asksIn (S : OSpec) (P : (o : S.ι) → S.Dom o → Prop) :
    Counts S (fun {_} c _ => c.AsksIn P) where
  pure := fun _ _ => trivial
  bind := fun h hg => OComp.AsksIn.bind hg h
  mono := fun h _ => h

section
variable (t : Tag)

/-- the property of this file, at the family of oracles of the compiled scheme -/
abbrev VP (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag) : (o : OracleName) → domOf lam L o → Prop :=
    fun o _ => vNames t o

/-- The chain, at every annotation. -/
theorem asksIn_chainB (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).AsksIn (VP lam L t)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV (OracleName.fb t) _ rfl)
          intro ans
          refine OComp.AsksIn.bind ?_ (asksIn_chainB cms x salt rtreq s A W _ _ _ rts' pls)
          intro _
          exact trivial
        · exact trivial
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV (OracleName.fb t) _ rfl)
          intro ans
          refine OComp.AsksIn.bind ?_ (asksIn_chainB cms x salt rtreq s A W _ _ _ rts' pls)
          intro _
          exact trivial
        · exact trivial
      · split
        · rename_i rtj rts1 _
          split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine OComp.AsksIn.bind ?_ (asksIn_askV (OracleName.g t) _ rfl)
            intro c
            refine OComp.AsksIn.bind ?_ (asksIn_askV (OracleName.fb t) _ rfl)
            intro ans
            refine OComp.AsksIn.bind ?_
              (asksIn_chainB cms x salt rtreq s A W _ _ (.shr _ (show Dig lam from c)) rts' pls)
            intro _
            exact trivial
          · exact trivial
        · exact trivial
      · exact trivial

theorem asksIn_climbM {node : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)}
    (hn : ∀ a b, (node a b).AsksIn (VP lam L t)) (path : List (Dig lam)) (j : ℕ) (c : Dig lam) :
    (climbM node path j c).AsksIn (VP lam L t) :=
  Counts.climbM (counts_asksIn (typedOracleFamily lam K L) (VP lam L t)) hn path j c

theorem asksIn_runCheck (c : Check lam L) : (runCheck (K := K) c).AsksIn (VP lam L t) := by
  simp only [runCheck, bind_eq]
  refine OComp.AsksIn.bind ?_ (asksIn_askV OracleName.leaf c.inp trivial)
  intro d
  refine OComp.AsksIn.bind ?_
    (asksIn_climbM t (node := hashTreeNode) (fun _ _ => asksIn_askV OracleName.node _ trivial) c.path c.j d)
  intro _
  exact trivial

theorem asksIn_runChecks : ∀ l : List (Check lam L), (runChecks (K := K) l).AsksIn (VP lam L t)
  | [] => trivial
  | c :: cs => by
      simp only [runChecks, bind_eq]
      refine OComp.AsksIn.bind ?_ (asksIn_runCheck t c)
      intro a
      refine OComp.AsksIn.bind ?_ (asksIn_runChecks cs)
      intro _
      exact trivial

theorem asksIn_reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam)
    (rs : Bits) : (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs).AsksIn (VP lam L t) :=
  Counts.reqCheck (counts_asksIn (typedOracleFamily lam K L) (VP lam L t))
      (fun q => asksIn_askV OracleName.rleaf q trivial)
    (fun q => asksIn_askV OracleName.rnode q trivial) depthReq rtreq slot path c rs

variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
      (depthReq : ℕ)
  (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)

/-- what follows the chain, path by path -/
theorem asksIn_afterB (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (afterB Q wq embS embE depthReq cms x π ρ rts ph).AsksIn (VP lam L t) := by
  unfold afterB
  split
  · rename_i a b _ _
    split_ifs with hc
    · simp only [bind_eq]
      refine OComp.AsksIn.bind ?_ (asksIn_runChecks t (a ++ b))
      intro ok
      split
      · refine OComp.AsksIn.bind ?_ trivial
        intro _
        exact trivial
      · refine OComp.AsksIn.bind ?_ (asksIn_reqCheck t _ _ _ _ _ _)
        intro _
        exact trivial
    · exact trivial
  · exact trivial

/-- what follows the chain, with pruned sets of paths -/
theorem asksIn_afterBO (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph).AsksIn (VP lam L t) :=
  Counts.afterBO (counts_asksIn (typedOracleFamily lam K L) (VP lam L t))
      (fun q => asksIn_askV OracleName.leaf q trivial)
    (fun q => asksIn_askV OracleName.node q trivial) (fun q => asksIn_askV OracleName.rleaf q trivial)
    (fun q => asksIn_askV OracleName.rnode q trivial) Q wq embS embE depthReq cms x π ρ rts ph

end

/-! ## The two verifiers. The arguments stand in the order of verifyB | verifyOneProtocol. -/

/-- The compiled verifier of one slot asks at leaf, node, rleaf, rnode and at its own tag's fb and g
alone. -/
theorem asksIn_verifyB (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyB t Q wq embS embP xin embE depthReq cms x π).AsksIn (VP lam L t) := by
  unfold verifyB recomputeChainOfProof
  refine OComp.AsksIn.bind ?_
    (asksIn_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
        π.roots π.plains)
  intro r
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact trivial
  · exact asksIn_afterB t Q wq embS embE depthReq cms x π ρ rts ph

/-- The same for the verifier with the strict format and pruned sets of paths. -/
theorem asksIn_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).AsksIn (VP lam L t) := by
  unfold verifyOneProtocol recomputeChainOfProof
  refine OComp.AsksIn.bind ?_
    (asksIn_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
        π.roots π.plains)
  intro r
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact trivial
  · dsimp only
    split_ifs
    · exact asksIn_afterBO t Q wq embS embE depthReq cms x π ρ rts ph
    · exact trivial

/-- The log's form: every entry of the run's own log, at every family of oracle functions. -/
theorem verifyB_log (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (F : Fam (typedOracleFamily lam K L)) :
    ∀ e ∈ ((verifyB t Q wq embS embP xin embE depthReq cms x π).withTrace.det F).2, vNames t e.1 :=
  mem_trace_of_asksIn F (asksIn_verifyB t Q wq embS embP xin embE depthReq cms x π)

theorem verifyBS_log (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (F : Fam (typedOracleFamily lam K L)) :
    ∀ e ∈ ((verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).withTrace.det F).2,
        vNames t e.1 :=
  mem_trace_of_asksIn F (asksIn_verifyBS sMT sFS t Q wq embS embP xin embE depthReq cms x π)

/-- No entry of the log stands at the spare oracle (nor at ann, nor at a ghost name). -/
theorem verifyB_log_ne (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (F : Fam (typedOracleFamily lam K L)) :
    ∀ e ∈ ((verifyB t Q wq embS embP xin embE depthReq cms x π).withTrace.det F).2,
      e.1 ≠ OracleName.other ∧ e.1 ≠ OracleName.ann ∧ ∀ t' k, e.1 ≠ OracleName.fbw t' k :=
  fun e he => vNames_ne (verifyB_log t Q wq embS embP xin embE depthReq cms x π F e he)

theorem verifyBS_log_ne (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (F : Fam (typedOracleFamily lam K L)) :
    ∀ e ∈ ((verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).withTrace.det F).2,
      e.1 ≠ OracleName.other ∧ e.1 ≠ OracleName.ann ∧ ∀ t' k, e.1 ≠ OracleName.fbw t' k :=
  fun e he => vNames_ne (verifyBS_log sMT sFS t Q wq embS embP xin embE depthReq cms x π F e he)

/-! ## The six verifiers of the scheme; ReadRun's chain -/

variable (W : QueryLayout lam L)

theorem asksIn_vT (cm : Dig lam) (π : OneProtocolProof lam L.batT) :
    (vT W cm π).AsksIn (VP lam L Tag.test) := asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem asksIn_vL (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) :
    (vL W cm cm' π).AsksIn (VP lam L Tag.link) := asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem asksIn_vB (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    (vB W cm x π).AsksIn (VP lam L Tag.onl) := asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem asksIn_vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam L.batT) :
    (vTS W sMT sFS cm π).AsksIn (VP lam L Tag.test) := asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

theorem asksIn_vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) :
    (vLS W sMT sFS cm cm' π).AsksIn (VP lam L Tag.link) := asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

theorem asksIn_vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    (vBS W sMT sFS cm x π).AsksIn (VP lam L Tag.onl) := asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

variable {W}

theorem asksIn_chainAt (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (cms : List (Dig lam)) :
    (chainAt t Q wq embP xo salt rtreq roots plains cms).AsksIn (VP lam L t) :=
  asksIn_chainB t cms xo salt rtreq Q.loc.shape Q.ann wq.sh embP 0 .first roots plains

/-- chainAt's log at every annotation (OursFirst.lean's chainAt_log: at local rounds alone, fb t
alone) -/
theorem chainAt_log' (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (cms : List (Dig lam))
        (F : Fam (typedOracleFamily lam W.K L)) :
    ∀ e ∈ ((chainAt t Q wq embP xo salt rtreq roots plains cms).withTrace.det F).2, vNames t e.1 :=
  mem_trace_of_asksIn F (asksIn_chainAt t Q wq embP xo salt rtreq roots plains cms)

end TypedOracleCompiler.Compile.Batch
