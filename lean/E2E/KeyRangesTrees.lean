-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesTrees.lean: IN FRONT OF THE KEY FILE's TEST ON THE RANGES TWO TREES ARE SENT: the
frame's count of the oracle messages that the first fifteen sub-protocols of the first chain state
(`treesTo`, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean: one for each root) is 2, in scope: one
tree of the index masks' sending, one of the sending of the multiplicities, in which the first
fold's fresh table rides; the lookups' links and the laying of their rows state none. Statements and
proofs, off the description's own text; the two numbers of trees BY THE KERNEL's OWN EVALUATION at
the library's typed sizes of a key.

  `flat_nils`, `link_noTrees`   a lookup's link states no oracle message
  `len_oracles`   a sending states as many as it has trees
  **`pre_trees`**   what stands in front of the ranges' test states as many as the two sendings have
                 trees: at all letters
  `trees_len`, `one_idx`, `one_msg`   a sending's number of trees reads its codes and messages
                 alone; at the written ones: 1 and 1
  **`trees15`**, `trees15_laid`   in scope: `treesTo … 15 = 2`, at the description's flat list and
                 at the thread `laid₁`

Limits. On the description's stated oracle messages alone. In scope; at the written sizes. Nothing
on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesFront
import E2E.KeyShapeFullSourced
import E2E.KeyBookHeldK1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place Link Oracle)
open VerifiableInference.Desc.Key (Xi FirstState Claim lookupLink lookupPlace lookupsOf firstChain
  layRows sendingPar pieces groupsTold rootsAt rootsBefore)
open H2K.JointK (keyFirstPre)
open AtPublicFiles.AtFiles (KeyNamed KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (six_sourced)
open AtPublicFiles.KeyBook (sendingPar_sent)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

theorem flat_nils {α β : Type} : ∀ l : List α, (l.map fun _ => ([] : List β)).flatMap id = []
  | [] => rfl
  | _ :: l => by
    rw [List.map_cons, List.flatMap_cons]
    exact flat_nils l

/-- A lookup's link states no oracle message. -/
theorem link_noTrees (one : OnBytes.Params.OneTime) (set : OnBytes.Params.Setting) (i : Nat)
    (x : VerifiableInference.Desc.Key.Lookup) :
    ((lookupLink one set i x).blocksInOrder.flatMap fun b => b.oracles.flatMap id) = [] := by
  have e : ((lookupLink one set i x).blocksInOrder.flatMap fun b => b.oracles.flatMap id) =
      (((lookupPlace set i x).entries.getD []).map fun _ => ([] : List Oracle)).flatMap id ++ [] :=
    rfl
  rw [e, List.append_nil, flat_nils]

/-- A sending states as many oracle messages as it has trees. -/
theorem len_oracles (P : VerifiableInference.Desc.K1.Par) :
    ((VerifiableInference.Desc.K1.oracles P).flatMap id).length = P.trees.length := by
  unfold VerifiableInference.Desc.K1.oracles
  simp

/-- **What stands in front of the ranges' test states as many as the two sendings have trees.** -/
theorem pre_trees (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) :
    ((keyFirstPre one D told set N).flatMap fun b => b.oracles.flatMap id).length =
      (sendingPar one pieces.idx "the index masks" #[one.indexMasks]
        (groupsTold told 0 (rootsAt D 0))).trees.length +
      (sendingPar one pieces.msg "the lookups' own message and what rides with it"
        (OnBytes.Wf.messageOf one.ranges)
        (groupsTold told (rootsBefore D 2) (rootsAt D 2))).trees.length := by
  have e : ((keyFirstPre one D told set N).flatMap fun b => b.oracles.flatMap id) =
      (VerifiableInference.Desc.K1.oracles (sendingPar one pieces.idx "the index masks"
        #[one.indexMasks] (groupsTold told 0 (rootsAt D 0))) ++ []).flatMap id ++
      ((VerifiableInference.Desc.K1.oracles (sendingPar one pieces.msg
        "the lookups' own message and what rides with it" (OnBytes.Wf.messageOf one.ranges)
        (groupsTold told (rootsBefore D 2) (rootsAt D 2))) ++ []).flatMap id ++
      ((((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1).flatMap Link.blocksInOrder).flatMap
        fun b => b.oracles.flatMap id)) := by
    unfold keyFirstPre
    rw [List.flatMap_append, List.flatMap_append, List.flatMap_cons]
    show _ ++ (_ ++ []) ++ _ ++ [] = _
    simp only [List.append_nil, List.append_assoc]
    rfl
  have e3 : ((((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1).flatMap
      Link.blocksInOrder).flatMap fun b => b.oracles.flatMap id) = [] := by
    rw [List.flatMap_assoc]
    refine List.flatMap_eq_nil_iff.2 fun Lk hL => ?_
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hL
    exact link_noTrees one set x.2 x.1
  rw [e, e3]
  simp only [List.append_nil, List.length_append]
  rw [len_oracles, len_oracles]

/-- A sending's number of trees reads its codes and its messages alone. -/
theorem trees_len (P : VerifiableInference.Desc.K1.Par) (cs : OnBytes.Codes)
    (ms : Array OnBytes.OracleNotice) (hc : P.codes = cs) (hs : P.sent = ms) :
    P.trees.length =
      (((VerifiableInference.Desc.Own.treesMade cs ms).map fun y => y.shapes.toList).getD
        []).length := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

theorem one_idx : (((VerifiableInference.Desc.Own.treesMade keyFull.codes #[keyFull.once.input]).map
    fun y => y.shapes.toList).getD []).length = 1 := by decide +kernel

theorem one_msg : (((VerifiableInference.Desc.Own.treesMade keyFull.codes
    (OnBytes.Wf.messageOf keyFull.ranges.x)).map fun y => y.shapes.toList).getD []).length = 1 := by
  decide +kernel

section Scope
variable {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **In scope two trees are sent in front of the ranges' test.** -/
theorem trees15 (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 15 = 2 := by
  have h6 := six_sourced hsrc scope
  have e1 : treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 15 =
      ((keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).flatMap
        fun b => b.oracles.flatMap id).length :=
    congrArg
      (fun l : List (Block FirstState Claim) =>
        (l.flatMap fun (b : Block FirstState Claim) => (b.oracles.flatMap id : List Oracle)).length)
      (take15 scope hsrc.named)
  refine e1.trans ((pre_trees _ _ _ _ _).trans ?_)
  rw [trees_len _ keyFull.codes #[keyFull.once.input] h6.codes
      (by rw [sendingPar_sent, h6.indexMasks]),
    trees_len _ keyFull.codes (OnBytes.Wf.messageOf keyFull.ranges.x) h6.codes
      (by rw [sendingPar_sent, h6.ranges]; rfl), one_idx, one_msg]

end Scope

/-- At the thread. -/
theorem trees15_laid {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
    (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (Pl : VerifiableInference.Desc.Key.LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀)
    (rc : Rc) (x : Xi) (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    treesTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs 15 = 2 :=
  trees15 hsrc scope

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.flat_nils
#print axioms AtPublicFiles.KeyThread.link_noTrees
#print axioms AtPublicFiles.KeyThread.len_oracles
#print axioms AtPublicFiles.KeyThread.pre_trees
#print axioms AtPublicFiles.KeyThread.trees_len
#print axioms AtPublicFiles.KeyThread.one_idx
#print axioms AtPublicFiles.KeyThread.one_msg
#print axioms AtPublicFiles.KeyThread.trees15
#print axioms AtPublicFiles.KeyThread.trees15_laid
