-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/FirstEndShape.lean: CONDITIONAL: THE FIRST CHAIN's SHARE OF THE DOOR ON SHAPES (FirstEndHasTheShape,
AtFullSide/LaterThreads/DoorOnShapes.lean): what is handed of a state that the verifier's fold over the first chain returns has ONE
shape, read off the end of the run on shapes at the stored files.

  handedOf c           the value: statement, book, roots, W, own group, mask off the run's end c; the two marks true
  WeightsAtTheEnd h    a definition, meant as a hypothesis: at a state reached over the whole first chain the pending rows' weights
                       pass the door's test on their form
  first_end_shape      **FirstEndHasTheShape h a**, from the whole run at the stored files (hW), handedOf c = some a and WeightsAtTheEnd h

By what. The fold gives "reached" (reach_of_fold); at a reached state the whole shape is the table's run's value (shape_of_reached with
block_yes_all: no thread, no family J, no fall's silence); at 358 that value is the stored run's at any public files under the head
(shape_at_border); six of the eight components are read off it. The mark on the statement: tidy_at_head, at every reached state.

Limits. hW (closed lines of the kernel, in a library of their own) AND WeightsAtTheEnd ARE PREMISES. The premise KeyHasTheSizes of the share
is not spent. No thread, no prover, no coin. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.LaterThreads.DoorOnShapes
import Johnson.AtFull.Shape.Scope.BlockYesClosed
import Johnson.AtFull.Shape.Scope.EndAtScope
import Johnson.AtFull.Shape.Scope.YesOfWhole
import Johnson.Desc.Last.FourAtHead
import E2E.StartReqOk
import Johnson.ToldDescR.EndIs358

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open OnBytes OnBytes.Model
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn)
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc.Third (FirstEnd₃ firstOfS)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open ToldDesc (p14At)

/-- **The value**, off the end of the run on shapes. -/
def handedOf (c : ShA) : Option HandedShape :=
  match c.1.atEnd with
  | some (_, _, some q) =>
    some ⟨c.1.core.st, c.1.core.book, c.1.core.roots, true, q.w, q.own, q.mask, true⟩
  | _ => none

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- At a state reached over the whole first chain the pending rows' weights pass the door's test on their form. A definition, meant
as a hypothesis. -/
def WeightsAtTheEnd (h : HeadAtReturn files A) : Prop :=
  ∀ (z : ProofFile.InstPub) (s : S), Reach 0 h.firstChain.blocksInOrder (ProofFile.startS A.Z) 358 (z, s) →
    ∀ r ∈ s.rows, AtPublicFiles.AtFiles.weightsB (p14At A.Z).S (linLayOmega s.st.codes (p14At A.Z).S) r.g = true

/-- **THE FIRST CHAIN's SHARE.** -/
theorem first_end_shape (h : HeadAtReturn files A) {c : ShA} (hW : RunsAll 0 358 startShA c)
    {a : HandedShape} (ha : handedOf c = some a) (hw : WeightsAtTheEnd h) :
    FirstEndHasTheShape h a := by
  intro x rounds columns last handed fit _ fold isHanded
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have hB := O.made
  obtain ⟨X₀', hX₀⟩ := record_there Johnson.Unfolds.Layout.lay_size
  have hlen : h.firstChain.blocksInOrder.length = 358 := ToldDesc.flat_358 h.head.scope h.head.reads O
  have hr : Reach 0 h.firstChain.blocksInOrder (ProofFile.startS A.Z) 358 (x.pub, last) :=
    reach_of_fold 358 (Nat.le_of_eq hlen.symm) last rounds [] columns []
      (by rw [← hlen, List.take_length]; exact fold)
  have hJ := shape_of_reached h.head hB 0 (yes_of_whole h.head hB hW) (block_yes_all h.head hB)
    (z := x.pub) (AtPublicFiles.Start.reqOk_of_okStart fit) (Nat.le_refl 358) hr
  have hs : shA last = c :=
    shape_at_border h.head hB hX₀ (Nat.le_refl 358) rfl (run_of_whole hW X₀' hX₀) hJ
  have hcore : VerifiableInference.Desc.Ground.Sh.coreSh ⟨last.st, last.book, last.roots⟩ = c.1.core :=
    congrArg (fun y : ShA => y.1.core) hs
  have hend : VerifiableInference.Desc.First.Shape.endSh last.here = c.1.atEnd :=
    congrArg (fun y : ShA => y.1.atEnd) hs
  have htidy : VerifiableInference.Desc.Ground.Sh.stTidyB last.st = true :=
    VerifiableInference.Desc.Ground.Sh.tidy_mark
      (VerifiableInference.Desc.Last.tidy_at_head h.head.toAtMg 358 (x.pub, last) hr)
  have hwt := hw x.pub last hr
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 isHanded
  unfold S.firstEnd? at he
  unfold handedOf at ha
  rw [← hend] at ha
  cases hh : last.here with
  | mem o =>
    rw [hh] at he ha
    dsimp only [VerifiableInference.Desc.First.Shape.endSh] at he ha
    cases hl : o.lin with
    | none =>
      rw [hl] at he
      cases he
    | some l =>
      rw [hl] at he ha
      have hrows : last.rows = [VerifiableInference.Desc.First.rowOfClaim l.claim] := by
        unfold S.rows
        rw [hh]
        dsimp only
        rw [hl]
      have hel : e.lin = l := by
        have he' : (if l.w != noId then some (⟨last.st, last.book, l⟩ : Proof.FirstEnd) else none) =
            some e := he
        split at he'
        · cases he'
          rfl
        · cases he'
      have ha' : (⟨c.1.core.st, c.1.core.book, c.1.core.roots, true, l.w, l.own, l.mask, true⟩ :
          HandedShape) = a := Option.some.inj ha
      subst ha'
      unfold handedShape handedShapeOf
      dsimp only
      rw [hrows]
      dsimp only
      rw [hel, ← hcore, htidy, hwt _ (by rw [hrows]; exact List.mem_singleton.2 rfl)]
      rfl
  | _ =>
    rw [hh] at he
    cases he

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.first_end_shape
