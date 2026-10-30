-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/LettersSame.lean: OF THE LETTERS OF LW (LettersAtX.lean) THAT READ THE PUBLIC
RECORD, WHICH ARE THE SAME AT TWO RECORDS THAT MEET SameRead (Scope/Rel.lean), AT EVERY LINK.

* links_same, built_same: the segments' records.
* atA_map: a function of an attention plan that does not see what stripPlan lays.
* nums_same, hpL_same, k8_same, k2n_same: the four letters; linkNumbers_same, k8Asks_same, k8NU_same
  behind them; attention_strip: the families of tables do not see what stripS lays.

Limits. Equations of terms; nothing is evaluated. Of look, k4pub, k4own and k11: nothing here.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.AtFull.Shape.LettersAtX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K1 (linkNumbers qFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2)
open HonestTraceRun.SetUp (SamePlans)

variable {X X₀ : Verify.Public}

theorem subproofs_same (P : SamePlans X X₀) (links : List Params.ReqLink) :
    Verify.subproofsWith X links = Verify.subproofsWith X₀ links := by
  unfold Verify.subproofsWith
  rw [HonestTraceRun.SetUp.rounds_same P, P.NGr, P.wsLay]

theorem links_same (S : SameRead X X₀) : linksOfX X = linksOfX X₀ := by
  have P := S.toSamePlans
  unfold linksOfX
  rw [HonestTraceRun.SetUp.links_same P, P.NGr, P.p4]

theorem built_same (S : SameRead X X₀) : builtOfX X = builtOfX X₀ := by
  unfold builtOfX
  rw [HonestTraceRun.SetUp.links_same S.toSamePlans, links_same S]

theorem atA_map (S : SameRead X X₀) (g : Nat) {β : Type} (f : Attention.Plan → β)
    (hf : ∀ a, f (stripPlan a) = f a) : X.A[g]?.map f = X₀.A[g]?.map f := by
  have e := congrArg (Option.map f) (S.atA g)
  simpa [Option.map_map, Function.comp_def, hf] using e

theorem linkNumbers_same (S : SameRead X X₀) (Y : Stages.LinkH) :
    linkNumbers (gOf X) Y = linkNumbers (gOf X₀) Y := by
  unfold linkNumbers
  simp only [gOf, S.G, S.H]
  rw [atA_map S Y.g (fun p => ((4 : Nat), (6 : Nat), some [p.iU3],
    some [p.seam.tl.ix.ZZ, p.seam.tl.ix.BZ])) fun _ => rfl]

theorem nums_same (S : SameRead X X₀) (l : Nat) : (LW X).nums l = (LW X₀).nums l := by
  show ((builtOfX X)[l]?).bind (linkNumbers (gOf X)) = ((builtOfX X₀)[l]?).bind (linkNumbers (gOf X₀))
  rw [built_same S, funext (linkNumbers_same S)]

theorem hpL_same (S : SameRead X X₀) (l : Nat) : (LW X).hpL l = (LW X₀).hpL l := by
  have hV : X.hS.V = X₀.hS.V := congrArg (·.V) S.hS
  have hT : X.hS.T = X₀.hS.T := congrArg (·.T) S.hS
  have hk : (Verify.borderOf X.y).kxb = (Verify.borderOf X₀.y).kxb := congrArg (·.kxb) S.lay
  show P1K2.pureLetters (gOf X) l = P1K2.pureLetters (gOf X₀) l
  unfold P1K2.pureLetters
  show ((builtOfX X)[l]?).map _ = ((builtOfX X₀)[l]?).map _
  rw [built_same S]
  simp only [gOf, hV, hT, hk, S.H, S.owner]

theorem attention_strip (T : Attention.Shape) :
    VerifiableInference.Desc.First.K8.Asks.attention (stripS T) =
      VerifiableInference.Desc.First.K8.Asks.attention T := by
  have hn : ((stripS T).calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl
      (fun a c => a + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length)
      0 = (T.calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl
      (fun a c => a + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length)
      0 := by
    show ((T.calls.map stripA).toList.filter _).foldl _ 0 = _
    rw [Array.toList_map, List.filter_map, List.foldl_map]
    rfl
  simp only [VerifiableInference.Desc.First.K8.Asks.attention]
  rw [hn]
  rfl

theorem k8Asks_same (S : SameRead X X₀) (Y : Stages.LinkH) :
    ProofFile.k8Asks (gOf X) Y = ProofFile.k8Asks (gOf X₀) Y := by
  have hh : VerifiableInference.Desc.First.K8.Asks.head X.hS =
      VerifiableInference.Desc.First.K8.Asks.head X₀.hS := by
    have e := congrArg VerifiableInference.Desc.First.K8.Asks.head S.hS
    exact e
  have hl : VerifiableInference.Desc.First.K8.Asks.layers X.y X.layers.rd Y.g =
      VerifiableInference.Desc.First.K8.Asks.layers X₀.y X₀.layers.rd Y.g := by
    rw [S.rd]
    have e := congrArg (fun y => VerifiableInference.Desc.First.K8.Asks.layers y X₀.layers.rd Y.g) S.lay
    exact e
  have ha := atA_map S Y.g (fun P => VerifiableInference.Desc.First.K8.Asks.attention P.S)
    fun a => attention_strip a.S
  unfold ProofFile.k8Asks
  simp only [gOf]
  rw [hh, hl, ha]

theorem k8NU_same (S : SameRead X X₀) (Y : Stages.LinkH) :
    ProofFile.k8NU (gOf X) Y = ProofFile.k8NU (gOf X₀) Y := by
  have ha := atA_map S Y.g (fun p => p.seam.nU) fun _ => rfl
  unfold ProofFile.k8NU
  simp only [gOf, S.H, S.G]
  rw [ha]

theorem k8_same (S : SameRead X X₀) (l : Nat) : (LW X).k8 l = (LW X₀).k8 l := by
  show ((builtOfX X)[l]?).map (fun Xl => k8ParWC (msgsAt msgsW) (gOf X) Xl l) =
    ((builtOfX X₀)[l]?).map (fun Xl => k8ParWC (msgsAt msgsW) (gOf X₀) Xl l)
  rw [built_same S]
  congr 1
  funext Y
  unfold k8ParWC
  rw [k8Asks_same S, k8NU_same S]

theorem k2n_same (S : SameRead X X₀) (a : Option Nat) : (LW X).k2n a = (LW X₀).k2n a := by
  show (P1K2.prepareAt proofSizedFull X qFull codesFull2 proofSizedFull.request
      proofSizedFull.request.answers).bind _ =
    (P1K2.prepareAt proofSizedFull X₀ qFull codesFull2 proofSizedFull.request
      proofSizedFull.request.answers).bind _
  simp only [P1K2.prepareAt, subproofs_same S.toSamePlans]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.links_same
#print axioms Johnson.AtFull.Shape.Scope.built_same
#print axioms Johnson.AtFull.Shape.Scope.nums_same
#print axioms Johnson.AtFull.Shape.Scope.hpL_same
#print axioms Johnson.AtFull.Shape.Scope.k8_same
#print axioms Johnson.AtFull.Shape.Scope.k2n_same
