-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/NeedO.lean: under `W.NB nb` the verifiers `VO`, `VKO` for keys and proofs with pruned
Merkle paths (Compile/Batch/StarO.lean) read only the marked blocks of an answer (those that the
table of Compile/Batch/NeedTable.lean names; "what is needed" in the docstrings); and, for `Std m`,
what they cost if only these are queried, as in the second exit (Rom/OverOneN.lean) (words of this
library: lean/GLOSSARY.md).
The counterpart of the parts on V of Compile/Batch/NeedBlocks.lean, Compile/Batch/NeedCost.lean and
Compile/Batch/NeedP.lean.
    Part 1  `facBy_VO`, `facBy_VKO`: under `W.NB nb` the verifiers go on in the same way after
            answers in the relation `agree nb` (Compile/Batch/NeedTable.lean). Only the Fiat-Shamir
            queries of the chain matter, and the chain is that of `verifyOneProtocol`; at the oracles of
            leaves and nodes `agree` is equality
    Part 2  `costBoundAt_VO`, `costBoundAt_VKO`: the bound of V (`costBoundAt_V`,
            Compile/Batch/NeedCost.lean), cVBN W nb: the bound on the path verifications holds of
            the joint verification that replaces them too
    Part 3  `facOK_prunedK`: under `W.NB nb` a scheme A whose C, P, V have the property of Part 1
            keeps it when pruned (C and P are A's followed by a pure map). The step from it to what
            the second exit asks of a scheme, and a bound on V's queries over that exit, are not in
            this library.
    Part 4  `nb_setPr`: `W.NB nb` passes to `W.setPr F`, for all flags F for pruned paths;
            `cVBN_setPr`: the bound `cVBN` is the same for both
Limits: nothing on C's and P's numbers of queries. No probability and no error bound is stated here.
-/
import Compile.Batch.NeedL
import Compile.Batch.SizeO

open Rom Iop

namespace Compile.Batch
namespace Need

/-! ## Part 1. The verifiers go on in the same way -/

section Verifier
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fo" => OComp.FactorsBy (S := spec lam K L) (agree nb)

theorem fo_afterBC {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    Fo (afterBC Q wq embS embE depthReq cms x π s ρ rts ph) :=
  Counts.afterBC (P := fun {_} c _ => OComp.FactorsBy (S := spec lam K L) (agree nb) c)
    ⟨fun _ _ => trivial, fun h hg => OComp.FactorsBy.bind h hg, fun h _ => h⟩
    (fun q => fo_askV nb OracleName.leaf q fun _ _ h => h) (fun q => fo_askV nb OracleName.node q fun _ _ h => h)
    (fun q => fo_askV nb OracleName.rleaf q fun _ _ h => h) (fun q => fo_askV nb OracleName.rnode q fun _ _ h => h)
    Q wq embS embE depthReq cms x π s ρ rts ph

theorem fo_verifyBC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (s : List (Dig lam)) (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0) :
    Fo (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s) := by
  unfold verifyBC recomputeChainOfProof
  refine OComp.FactorsBy.bind (fo_chainB nb t _ _ _ _ _ _ _ _ _ _ _ _ hW) fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · trivial
  · dsimp only
    split_ifs
    · exact fo_afterBC nb Q wq embS embE depthReq cms x π s ρ rts ph
    · trivial

end Verifier

section Star
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) {nb : Tag → ℕ → ℕ} (hW : W.NB nb)

local notation "Fo" => OComp.FactorsBy (S := spec lam W.K L) (agree nb)

include hW

theorem fo_vTO (sMT sFS : ℕ) (cm : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    Fo (vTO W sMT sFS cm π) :=
  fo_verifyBC nb _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW.T
theorem fo_vLO (sMT sFS : ℕ) (cm cm' : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.link)) :
    Fo (vLO W sMT sFS cm cm' π) :=
  fo_verifyBC nb _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW.Lk
theorem fo_vBO (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : BPrfO lam L.onlineBatch) :
    Fo (vBO W sMT sFS cm x π) :=
  fo_verifyBC nb _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW.B

/-- Under `W.NB nb`: the verifier for pruned keys and proofs goes on in the same way after two
answers that agree on what is needed. -/
theorem facBy_VO (v : IVKO lam L) (x : X) (π : PrfO lam L) : Fo (VO W p v x π) := by
  unfold VO
  split
  · split_ifs
    · exact OComp.FactorsBy.bind (fo_vTO W hW _ _ _ _) fun _ =>
        OComp.FactorsBy.bind (fo_vLO W hW _ _ _ _ _) fun _ =>
          OComp.FactorsBy.bind (fo_vBO W hW _ _ _ _ _) fun _ => trivial
    · trivial
  · trivial

/-- The same with the entries in the key. -/
theorem facBy_VKO (v : IVKKO lam L) (x : X) (π : PrfKO lam L) : Fo (VKO W p v x π) :=
  facBy_VO W p hW v.1 x (reKO v.2 π)

end Star

/-! ## Part 2. What the verifiers cost -/

section Bounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m)
include hm

theorem cn_afterBC' {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CN nb m (afterBC Q wq embS embE depthReq cms x π s ρ rts ph) (cOpen wq + reqCost depthReq ph) :=
  cn_of_cb nb hm
    (Counts.afterBC VCost.counts_cb (VCost.cb_askV OracleName.leaf) (VCost.cb_askV OracleName.node)
      (VCost.cb_askV OracleName.rleaf) (VCost.cb_askV OracleName.rnode) Q wq embS embE depthReq cms x π s ρ rts ph)

theorem cn_afterBC {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CN nb m (afterBC Q wq embS embE depthReq cms x π s ρ rts ph) (cOpen wq + (depthReq + 1)) :=
  (cn_afterBC' nb hm Q wq embS embE depthReq cms x π s ρ rts ph).mono
    (Nat.add_le_add_left (reqCost_le _ _) _)

theorem cn_afterBC_lo {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (hp : ph.slotVal = none) :
    CN nb m (afterBC Q wq embS embE depthReq cms x π s ρ rts ph) (cOpen wq) := by
  have h := cn_afterBC' nb hm Q wq embS embE depthReq cms x π s ρ rts ph
  have e : reqCost depthReq ph = 0 := by unfold reqCost; rw [hp]; rfl
  rw [e, Nat.add_zero] at h
  exact h

theorem cn_verifyBC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Q) (s : List (Dig lam)) :
    CN nb m (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s)
      (cVQBN (nb t) wq depthReq) := by
  unfold verifyBC recomputeChainOfProof cVQBN
  refine OComp.CostBoundAt.bind (fun r => ?_)
    (cn_chainB nb hm t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBoundAt.pure _ _
  · dsimp only
    split_ifs
    · exact cn_afterBC nb hm Q wq embS embE depthReq cms x π s ρ rts ph
    · exact OComp.CostBoundAt.pure _ _

theorem cn_verifyBC_lo (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (hQ : RoundSplits.AllLo Q.loc.shape Q.ann) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Q) (s : List (Dig lam)) :
    CN nb m (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s) (cVQLN (nb t) wq) := by
  unfold verifyBC recomputeChainOfProof cVQLN
  refine OComp.CostBoundAt.bind_outs (fun r hr => ?_)
    (outs_chainB_lo t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann hQ wq.sh embP 0
      .first rfl π.roots π.plains)
    (cn_chainB_lo nb t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann hQ wq.sh embP 0
      .first rfl π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBoundAt.pure _ _
  · dsimp only
    split_ifs
    · exact cn_afterBC_lo nb hm Q wq embS embE depthReq cms x π s ρ rts ph (hr _ rfl)
    · exact OComp.CostBoundAt.pure _ _

end Bounds

section Three
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam W.K L) lam} (hm : Std m)
include hm

theorem cn_vTO (sMT sFS : ℕ) (cm : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    CN nb m (vTO W sMT sFS cm π) (cVQLN (nb .test) W.T) :=
  cn_verifyBC_lo nb hm _ _ _ _ (RoundSplits.allLo_allLocal _) W.T _ _ _ _ _ _ _ _ _

theorem cn_vLO (sMT sFS : ℕ) (cm cm' : Dig lam) (π : BPrfO lam (BatchInteractiveOracleProof.ofProto L.link)) :
    CN nb m (vLO W sMT sFS cm cm' π) (cVQLN (nb .link) W.Lk) :=
  cn_verifyBC_lo nb hm _ _ _ _ (RoundSplits.allLo_allLocal _) W.Lk _ _ _ _ _ _ _ _ _

theorem cn_vBO (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : BPrfO lam L.onlineBatch) :
    CN nb m (vBO W sMT sFS cm x π) (cVQBN (nb .onl) W.B W.depthReq) :=
  cn_verifyBC nb hm _ _ _ _ W.B _ _ _ _ _ _ _ _ _

/-- For `Std m`: on every path the marked blocks of the queries of `VO` add up to at most cVBN W nb:
the bound of V. -/
theorem costBoundAt_VO (p : Params) (v : IVKO lam L) (x : X) (π : PrfO lam L) :
    (VO W p v x π).CostBoundAt (needOf nb m).num (cVBN W nb) := by
  unfold VO cVBN
  split
  · split_ifs
    · simp only [bind_eq]
      refine (OComp.CostBoundAt.bind
        (t := cVQLN (nb .link) W.Lk + (cVQBN (nb .onl) W.B W.depthReq + 0))
        (fun a =>
          OComp.CostBoundAt.bind (t := cVQBN (nb .onl) W.B W.depthReq + 0)
            (fun b =>
              OComp.CostBoundAt.bind (t := 0)
                (fun c => OComp.CostBoundAt.pure _ _) (cn_vBO W nb hm _ _ _ _ _))
            (cn_vLO W nb hm _ _ _ _ _))
        (cn_vTO W nb hm _ _ _ _)).mono ?_
      omega
    · exact OComp.CostBoundAt.pure _ _
  · exact OComp.CostBoundAt.pure _ _

theorem costBoundAt_VKO (p : Params) (v : IVKKO lam L) (x : X) (π : PrfKO lam L) :
    (VKO W p v x π).CostBoundAt (needOf nb m).num (cVBN W nb) :=
  costBoundAt_VO W nb hm p v.1 x (reKO v.2 π)

end Three

/-! ## Part 3. A pruned scheme -/

section Pruned
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) {nb : Tag → ℕ → ℕ} {ISK : Type} {A : ZKCP.Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) ISK (PrfK lam L)}

/-- Under `W.NB nb`: a scheme whose algorithms go on in the same way after two answers that agree on
what is needed stays so when its keys and proofs are pruned. -/
theorem facOK_prunedK (hW : W.NB nb) (h : FacOK (agree nb) A) :
    FacOK (agree nb) (prunedK W p A) where
  C := fun i => OComp.FactorsBy.bind (h.C i) fun _ => trivial
  P := fun k b => OComp.FactorsBy.bind (h.P k b) fun _ => trivial
  V := fun v x π => facBy_VKO W p hW v x π


end Pruned

/-! ## Part 4. The flags -/

theorem readsFrom_setPr {lam K : ℕ} {nbf : ℕ → ℕ} :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} (fl : OpenList s) {i : ℕ},
      RoundsQueryLayout.ReadsFrom nbf s A W i → RoundsQueryLayout.ReadsFrom nbf s A (RoundsQueryLayout.setPr s A W fl) i
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, fs), _, H => ⟨H.1, readsFrom_setPr fs H.2⟩

theorem nb_setPr {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb : Tag → ℕ → ℕ}
    (H : W.NB nb) (F : PrFlags L) : (W.setPr F).NB nb :=
  ⟨readsFrom_setPr F.T H.T, readsFrom_setPr F.Lk H.Lk, readsFrom_setPr F.B H.B⟩

theorem cVBN_setPr {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)
    (F : PrFlags L) (nb : Tag → ℕ → ℕ) :
    cVBN (W.setPr F) nb = cVBN W nb := rfl

end Need
end Compile.Batch
