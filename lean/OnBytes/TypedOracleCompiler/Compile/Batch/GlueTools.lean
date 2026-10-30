-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/GlueTools.lean: a second form of Compile/Batch/GlueTools.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/GlueTools.lean, comments apart: statements:
`detBound_reqCheck`, `detBound_vT`, `detBound_vL`, `detBound_vTS`, `detBound_vLS`; proofs alone:
`detBound_afterB`. Every other declaration has that file's text.

`tVQB` stands in OnBytes/TypedOracleCompiler/Compile/Batch/TVQB.lean here, not in Compile/Batch/SpecBinding.lean.
Compile/Batch/GlueBinding.lean, which the head below names as the use of this file, has no second
form in this folder.

The rest of this head is the head of Compile/Batch/GlueTools.lean, to be read with these changes;
the files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that
name, this folder's.

Compile/Batch/GlueTools.lean: lemmas on the compiled verifier of one slot and on extraction, for the
proof of index binding (Compile/Batch/GlueBinding.lean) (words of this library: lean/GLOSSARY.md).

  Part 1  The verifier of one slot uses no coins and makes at most `tVQB`
          (Compile/Batch/SpecBinding.lean) queries: one for each round and one more for the joining
          round, one leaf and one path for each opening, one leaf and one path in the request tree
          (`detBound_verifyB`). The same holds with the strict-format check and pruned Merkle paths
          (`detBound_verifyBS`). (What that verifier accepts, `verifyB` accepts with other paths,
          from the same trace, if the wire record is well-formed: `runsIn_verifyB_of_strict`,
          Compile/Batch/ForestSound.lean.)
  Part 2  A query to the oracle `ann` at the end of a trace changes nothing in what is extracted
          (`extEnc_ann`).

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.TVQB
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts
import Compile.GlueBinding

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

/-! ## Part 1. The verifier of one slot is coin-free, and its number of queries -/

section Verifier
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem detBound_askV (o : OracleName) (q : domOf lam L o) : DetBound (askTypedOracle (L := L) (K := K) o q) 1 :=
  detBound_ask (S := typedOracleFamily lam K L) o q

/-- how often the chain can still join: once before the shared rounds, never afterwards -/
def Phase.joins : Phase lam → ℕ
  | .first => 1
  | .loc _ => 1
  | .shr _ _ => 0
  | .aft _ _ => 0

theorem joins_of_one {cms : List (Dig lam)} {x : Option X} {salt : Bits} {k : Kind} {ph : Phase lam}
    {h : Head lam X} {own : Bool} {next : Bits → Phase lam}
    (e : actOf cms x salt k ph = some (.one h own next)) (v : Bits) :
    (next v).joins ≤ ph.joins := by
  cases k <;> cases ph
    <;> simp only [actOf, Option.some.injEq, Act.one.injEq, reduceCtorEq] at e <;>
    (obtain ⟨-, -, rfl⟩ := e; exact le_rfl)

theorem joins_of_join {cms : List (Dig lam)} {x : Option X} {salt : Bits} {k : Kind}
    {ph : Phase lam} {ρ : Bits} (e : actOf cms x salt k ph = some (.join ρ)) : ph.joins = 1 := by
  cases k <;> cases ph <;> first | rfl | (simp only [actOf, Option.some.injEq, reduceCtorEq] at e)

theorem detBound_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      DetBound (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls) (s.length + ph.joins)
  | [], _, _, _, _, _, _, _ => detBound_pure _ _
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine ((detBound_askV _ _).bind (t := s.length + ph.joins + 0) fun ans =>
            ((detBound_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                (Nat.add_le_add_left (joins_of_one e _) _)).bind
              (t := 0) fun r => detBound_pure _ _).mono ?_
          simp only [List.length_cons]
          omega
        · exact detBound_pure _ _
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine ((detBound_askV _ _).bind (t := s.length + ph.joins + 0) fun ans =>
            ((detBound_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                (Nat.add_le_add_left (joins_of_one e _) _)).bind
              (t := 0) fun r => detBound_pure _ _).mono ?_
          simp only [List.length_cons]
          omega
        · exact detBound_pure _ _
      · rename_i ρ e
        split
        · rename_i rtj rts1 _
          split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine ((detBound_askV (L := L) (K := K) (OracleName.g t) _).bind
              (t := 1 + (s.length + 0 + 0)) fun c =>
                (detBound_askV (L := L) (K := K) (OracleName.fb t) _).bind
                  (t := s.length + 0 + 0) fun ans =>
                    (detBound_chainB t cms x salt rtreq s A W _ _
                        (.shr _ (show Dig lam from c)) rts' pls).bind
                      (t := 0) fun r => detBound_pure _ _).mono ?_
            simp only [List.length_cons, joins_of_join e]
            omega
          · exact detBound_pure _ _
        · exact detBound_pure _ _
      · exact detBound_pure _ _

theorem detBound_climbM (node : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam))
    (hn : ∀ a b, DetBound (node a b) 1) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), DetBound (climbM node path j c) path.length
  | [], _, _ => detBound_pure _ _
  | s :: ss, j, c => by
      simp only [climbM, bind_eq]
      have hlen : 1 + ss.length ≤ (s :: ss).length := by simp only [List.length_cons]; omega
      split_ifs
      · exact ((hn c s).bind fun u => detBound_climbM node hn ss (j / 2) u).mono hlen
      · exact ((hn s c).bind fun u => detBound_climbM node hn ss (j / 2) u).mono hlen

theorem detBound_runCheck (c : Check lam L) :
    DetBound (runCheck (K := K) c) (c.path.length + 1) := by
  simp only [runCheck, bind_eq]
  refine ((detBound_askV (L := L) (K := K) OracleName.leaf c.inp).bind (t := c.path.length + 0) fun d =>
    (detBound_climbM hashTreeNode (fun a b => detBound_askV _ _) c.path c.j d).bind
      (t := 0) fun r => detBound_pure _ _).mono ?_
  omega

theorem detBound_runChecks (m : ℕ) : ∀ l : List (Check lam L), (∀ c ∈ l, c.path.length ≤ m) →
    DetBound (runChecks (K := K) l) (l.length * (m + 1))
  | [], _ => detBound_pure _ _
  | c :: cs, h => by
      simp only [runChecks, bind_eq]
      refine (((detBound_runCheck c).mono
        (t := m + 1) (by have := h c (List.mem_cons_self); omega)).bind
        (t := cs.length * (m + 1) + 0) fun a =>
        (detBound_runChecks m cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')).bind
            (t := 0) fun b =>
          detBound_pure _ _).mono ?_
      simp only [List.length_cons]
      nlinarith

theorem detBound_reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) (rs : Bits) :
    DetBound (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs) (depthReq + 1) := by
  unfold reqCheck
  split_ifs with h
  · simp only [bind_eq]
    refine ((detBound_askV (L := L) (K := K) OracleName.rleaf _).bind (t := path.length + 0) fun d =>
      (detBound_climbM rnodeV (fun a b => detBound_askV _ _) path slot d).bind
        (t := 0) fun r => detBound_pure _ _).mono ?_
    omega
  · exact detBound_pure _ _

/-- What the verifier does after the chain is coin-free and makes at most nOpen (maxDepth + 1) +
(depthReq + 1) queries. -/
theorem detBound_afterB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    DetBound (afterB Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1)) := by
  unfold afterB
  split
  · rename_i a b _ _
    split_ifs with hc
    · simp only [bind_eq]
      refine ((detBound_runChecks wq.maxDepth (a ++ b) ?_).mono
          (Nat.mul_le_mul_right (wq.maxDepth + 1) hc.1)).bind fun ok => ?_
      · intro c hmem
        have := List.all_eq_true.1 hc.2 c hmem
        simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
        omega
      · split
        · exact (DetBound.bind (s := 0) (t := 0) (detBound_pure _ _) fun _ =>
              detBound_pure _ _).mono (Nat.zero_le _)
        · exact DetBound.mono
            ((detBound_reqCheck _ _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _)
            (Nat.le_of_eq (Nat.add_zero _))
    · exact detBound_pure _ _
  · exact detBound_pure _ _

theorem counts_detBound (S : OSpec) : Counts S (fun {_} c t => DetBound c t) where
  pure := fun a t => detBound_pure a t
  bind := fun h hg => h.bind hg
  mono := fun h hst => h.mono hst

/-- `checkPrunedOpenings`, with pruned Merkle paths, keeps the bound of `afterB`. -/
theorem detBound_afterBO {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    DetBound (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1)) :=
  (Counts.afterBO (counts_detBound (typedOracleFamily lam K L)) (detBound_askV _) (detBound_askV _)
      (detBound_askV _) (detBound_askV _) Q wq embS embE depthReq cms x π ρ rts ph).mono
    (Nat.add_le_add_left (reqCost_le _ _) _)

theorem detBound_verifyB (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    DetBound (verifyB t Q wq embS embP xin embE depthReq cms x π) (tVQB wq depthReq) := by
  unfold verifyB recomputeChainOfProof tVQB
  refine (detBound_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains).bind fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact detBound_pure _ _
  · exact detBound_afterB Q wq embS embE depthReq cms x π ρ rts ph

/-- The bound on the queries of verifyB holds for verifyOneProtocol too. -/
theorem detBound_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    DetBound (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) (tVQB wq depthReq) := by
  unfold verifyOneProtocol recomputeChainOfProof tVQB
  refine (detBound_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains).bind fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact detBound_pure _ _
  · dsimp only
    split_ifs
    · exact detBound_afterBO Q wq embS embE depthReq cms x π ρ rts ph
    · exact detBound_pure _ _

variable (W : QueryLayout lam L)

theorem detBound_vT (cm : Dig lam) (π : OneProtocolProof lam L.batT) :
    DetBound (vT W cm π) (tVQB W.T W.depthReqT) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem detBound_vL (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) :
    DetBound (vL W cm cm' π) (tVQB W.Lk W.depthReqL) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem detBound_vB (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (vB W cm x π) (tVQB W.B W.depthReq) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

theorem detBound_vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam L.batT) :
    DetBound (vTS W sMT sFS cm π) (tVQB W.T W.depthReqT) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

theorem detBound_vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) :
    DetBound (vLS W sMT sFS cm cm' π) (tVQB W.Lk W.depthReqL) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

theorem detBound_vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (vBS W sMT sFS cm x π) (tVQB W.B W.depthReq) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

end Verifier

/-! ## Part 2. An announcement changes nothing in what is extracted -/

namespace GlueTools

theorem firstPre_snoc {E Q D : Type} [DecidableEq D] (view : E → Option (Q × D)) (e : E)
    (h : view e = none) (tr : List E) (c : D) :
    Merkle.firstPre view (tr ++ [e]) c = Merkle.firstPre view tr c := by
  have hn : Merkle.hit view c e = none := by
    unfold Merkle.hit
    rw [h]
    rfl
  unfold Merkle.firstPre
  rw [List.findSome?_append, List.findSome?_cons, hn]
  simp

theorem preimage_snoc {E D Y : Type} [DecidableEq D] {Ev : Merkle.Events E D}
    (V : Merkle.OraclePair Ev Y) (e : E) (hl : V.leaf e = none)
    (hn : V.node e = none) (tr : List E) :
    ∀ {t : Merkle.Shape} (q : t.Pos) (c : D), V.preimage (tr ++ [e]) q c = V.preimage tr q c
  | _, .here, c => firstPre_snoc V.leaf e hl tr c
  | _, .left q, c => by
      simp only [Merkle.OraclePair.preimage,
        firstPre_snoc V.node e hn tr c, preimage_snoc V e hl hn tr q]
  | _, .right q, c => by
      simp only [Merkle.OraclePair.preimage,
        firstPre_snoc V.node e hn tr c, preimage_snoc V e hl hn tr q]

end GlueTools

section Ann
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- the entry that a query to `ann` at cm leaves in a trace -/
def annE (W : QueryLayout lam L) (cm : Dig lam) (u : Unit) : QA (typedOracleFamily lam W.K L) := ⟨OracleName.ann, cm, u⟩

theorem extLeaf_ann (tr : Tc W) (cm : Dig lam) (u : Unit) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extLeaf (tr ++ [annE W cm u]) d c j = extLeaf tr d c j :=
  GlueTools.preimage_snoc (pairM lam W.K L) (annE W cm u) rfl rfl tr _ c

theorem extEnc_ann (tr : Tc W) (cm : Dig lam) (u : Unit) (c : Dig lam) :
    extEnc W (tr ++ [annE W cm u]) c = extEnc W tr c := by
  simp only [extEnc, extLeaf_ann]

end Ann

end TypedOracleCompiler.Compile.Batch
