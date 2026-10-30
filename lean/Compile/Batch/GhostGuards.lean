-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GhostGuards.lean: sanity lemmas: no algorithm of the compiled scheme queries the ghost
names `fbw t k`, as the docstring of `OracleName.fbw` (Compile/Batch/Oracles.lean) and the header of
Compile/Batch/SpecGhost.lean say (words of this library: lean/GLOSSARY.md).
    `NoGhost c`               the oracle algorithm c queries no ghost name, on any path; by
                              recursion on c
    `noGhost_realQ`           `realQ c` queries no ghost name, whatever c is; `realQ_of_noGhost`: an
                              algorithm that queries none is not changed by `realQ`
    `noGhost_C`, `noGhost_P`, `noGhost_V`, `noGhost_argB`
                              no algorithm of the scheme `argB W WP p` queries a ghost name: for
                              every wire record, with proof-of-work bits or without, well-formed or
                              not. C and P because they are `realQ` of something; V by going through
                              its definition (the chain queries fb t and g t; the verifications in
                              Merkle trees leaf, node, rleaf, rnode)
    `OComp.via_of_id`         a translation that sends every query to itself changes no algorithm
Limits: nothing is said on the extractor and the simulators, which are not oracle algorithms of this
kind.
-/
import Compile.Batch.GhostRouted
import Compile.Batch.ForestFacts
import Compile.Batch.GlueTools

noncomputable section

namespace Rom

variable {S : OSpec} {α : Type}

/-- a translation that sends every query to itself changes no algorithm -/
theorem OComp.via_of_id {φ : QMap S} (h : ∀ o q, φ o q = ⟨o, q, id⟩) : ∀ c : OComp S α, c.via φ = c
  | .pure _ => rfl
  | .query o q k =>
    (OComp.via_query_of (h o q) k).trans
      (congrArg (OComp.query o q) (funext fun r => OComp.via_of_id h (k r)))
  | .sample n k => congrArg (OComp.sample n) (funext fun r => OComp.via_of_id h (k r))

end Rom

namespace Compile.Batch
open Iop Rom Compile.GlueB

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The algorithm queries no ghost name. -/
def NoGhost {α : Type} : TypedOracleComputation lam K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, NoGhost (k r)
  | .query (.fbw _ _) _ _ => False
  | .query _ _ k => ∀ r, NoGhost (k r)

theorem ng_pure {α : Type} (a : α) : NoGhost (pure a : TypedOracleComputation lam K L α) := trivial

theorem NoGhost.bind {α β : Type} :
    ∀ {c : TypedOracleComputation lam K L α} {g : α → TypedOracleComputation lam K L β},
      NoGhost c → (∀ a, NoGhost (g a)) → NoGhost (c.bind g)
  | .pure a, _, _, hg => hg a
  | .sample _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query (.fbw _ _) _ _, _, h, _ => h
  | .query (.fb _) _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .leaf _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .node _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .rleaf _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .rnode _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query (.g _) _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .ann _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg
  | .query .other _ k, _, h, hg => fun r => NoGhost.bind (c := k r) (h r) hg

/-- `realQ c` queries no ghost name, whatever c is. -/
theorem noGhost_realQ {α : Type} : ∀ c : TypedOracleComputation lam K L α, NoGhost (realQ c)
  | .pure _ => trivial
  | .sample _ k => fun r => noGhost_realQ (k r)
  | .query (.fbw _ _) _ k => fun r => noGhost_realQ (k r)
  | .query (.fb _) _ k => fun r => noGhost_realQ (k r)
  | .query .leaf _ k => fun r => noGhost_realQ (k r)
  | .query .node _ k => fun r => noGhost_realQ (k r)
  | .query .rleaf _ k => fun r => noGhost_realQ (k r)
  | .query .rnode _ k => fun r => noGhost_realQ (k r)
  | .query (.g _) _ k => fun r => noGhost_realQ (k r)
  | .query .ann _ k => fun r => noGhost_realQ (k r)
  | .query .other _ k => fun r => noGhost_realQ (k r)

/-- an algorithm that queries no ghost name is not changed by `realQ` -/
theorem realQ_of_noGhost {α : Type} : ∀ c : TypedOracleComputation lam K L α, NoGhost c → realQ c = c
  | .pure _, _ => rfl
  | .sample n k, h => congrArg (OComp.sample n) (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query (.fbw _ _) _ _, h => h.elim
  | .query (.fb t) q k, h =>
    congrArg (OComp.query (S := spec lam K L) (.fb t) q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .leaf q k, h =>
    congrArg (OComp.query (S := spec lam K L) .leaf q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .node q k, h =>
    congrArg (OComp.query (S := spec lam K L) .node q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .rleaf q k, h =>
    congrArg (OComp.query (S := spec lam K L) .rleaf q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .rnode q k, h =>
    congrArg (OComp.query (S := spec lam K L) .rnode q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query (.g t) q k, h =>
    congrArg (OComp.query (S := spec lam K L) (.g t) q)
      (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .ann q k, h =>
    congrArg (OComp.query (S := spec lam K L) .ann q) (funext fun r => realQ_of_noGhost (k r) (h r))
  | .query .other q k, h =>
    congrArg (OComp.query (S := spec lam K L) .other q)
      (funext fun r => realQ_of_noGhost (k r) (h r))

/-! ## The verifier -/

theorem counts_noGhost :
    Counts (spec lam K L) (fun {_} c _ => NoGhost (lam := lam) (K := K) (L := L) c) where
  pure := fun _ _ => trivial
  bind := fun hc hg => NoGhost.bind hc hg
  mono := fun h _ => h

theorem ng_fb (t : Tag) (q : FbIn lam L t) : NoGhost (askTypedOracle (L := L) (K := K) (OracleName.fb t) q) :=
  fun _ => trivial
theorem ng_g (t : Tag) (q : JoiningRoundQuery lam L t) : NoGhost (askTypedOracle (L := L) (K := K) (OracleName.g t) q) := fun _ =>
  trivial

theorem ng_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      NoGhost (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          exact (ng_fb t _).bind fun ans =>
            (ng_chainB t cms x salt rtreq s A W _ _ _ rts' pls).bind fun r => ng_pure _
        · exact ng_pure _
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          exact (ng_fb t _).bind fun ans =>
            (ng_chainB t cms x salt rtreq s A W _ _ _ rts' pls).bind fun r => ng_pure _
        · exact ng_pure _
      · split
        · split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            exact (ng_g t _).bind fun c =>
              (ng_fb t _).bind fun ans =>
                (ng_chainB t cms x salt rtreq s A W _ _
                    (.shr _ (show Dig lam from c)) rts' pls).bind
                  fun r => ng_pure _
          · exact ng_pure _
        · exact ng_pure _
      · exact ng_pure _

theorem ng_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    NoGhost (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) := by
  unfold verifyOneProtocol recomputeChainOfProof
  refine (ng_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains).bind fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact ng_pure _
  · dsimp only
    split_ifs
    · exact Counts.afterBO (P := fun {_} c _ => NoGhost c) counts_noGhost
        (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
        Q wq embS embE depthReq cms x π ρ rts ph
    · exact ng_pure _

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- The verifier queries no ghost name. -/
theorem noGhost_V (v : IVK lam L) (x : X) (π : Prf lam L) : NoGhost (V W p v x π) := by
  unfold V
  split
  · split_ifs
    · simp only [bind_eq]
      exact (ng_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun a =>
        (ng_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun b =>
          (ng_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun c => ng_pure _
    · exact ng_pure _
  · exact ng_pure _

/-- The committer queries no ghost name. -/
theorem noGhost_C (i : I) : NoGhost (C W WP p i) := noGhost_realQ _

/-- The prover queries no ghost name. -/
theorem noGhost_P (k : ISK lam L) (b : List (X × Unit)) : NoGhost (P W WP p k b) := noGhost_realQ _

/-- No algorithm of the scheme queries a ghost name, for every wire record. -/
theorem noGhost_argB :
    (∀ i, NoGhost ((argB W WP p).C i)) ∧
    (∀ k b, NoGhost ((argB W WP p).P k b)) ∧
    ∀ v x π, NoGhost ((argB W WP p).V v x π) :=
  ⟨noGhost_C W WP p, noGhost_P W WP p, noGhost_V W p⟩

variable {W}



variable {WP p}



end Compile.Batch
