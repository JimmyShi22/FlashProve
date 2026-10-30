-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K2ShareAt.lean: K2Share (Johnson/IMR/RecSeat.lean) as a theorem, and so
Johnson/IMR/RecRun.lean's top statements without their premise.

  k2Share: ∀ cs sh, K2Share cs sh: its five clauses are k2_recAll
    (Johnson/Goal/Meaning/K2Share/K2Whole.lean) and headFrontQ_rec, headOpenQ_rec, finishFrontQ_rec,
    finishBehindQ_rec (Johnson/Goal/Meaning/K2Share/RecFronts.lean).
  descPure_recAll_paid, descPure_run_paid: descPure_recAll and descPure_run at k2Share.
  finishFrontQ_group: THE FINISH's OWN COPY OF A GROUP (FinOwn.G), of which RecAll says nothing:
    where RecAll holds in front, the quiet step "F.0.front" (K2.finishFrontQ) lays there the plan's
    group at the walk's frame's link, and as the finish's frame a frame of the plan's shape and
    groups: by the library's finishFrontQ_iff (Johnson/Top/H0/Tw/K2C/Asks.lean).
  descPure_finish: so at the record that a fold over ALL of frontOf c returns: the record in front
    of the first block behind the last link.
  k2Grows: K2Grows (Johnson/IMR/GrowsSeat.lean): k2_grows and the four of
    Johnson/Goal/Meaning/K2Share/GrowsFronts.lean. descPure_growsRun_paid:
      Johnson/IMR/GrowsSeat.lean's
    descPure_growsRun at it.
ON WHAT IT STANDS: the files named stand on the law files under Johnson/Top/H0/K2Hears/ and
K2Hands/.
OBJECT: ProofFile.onlineDescription's value, at every o.
-/
import Johnson.IMR.RecRun
import Johnson.Goal.Meaning.K2Share.RecFronts
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.IMR.GrowsSeat
import Johnson.Goal.Meaning.K2Share.GrowsFronts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem k2Share (cs : Codes) (sh : Params.ReqShape) : K2Share cs sh where
  k2 := fun p => First.K2.k2_recAll cs sh p
  front := fun tl => First.K2.headFrontQ_rec tl
  openQ := fun P => First.K2.headOpenQ_rec P
  finFront := First.K2.finishFrontQ_rec
  finBehind := First.K2.finishBehindQ_rec

/-- **Johnson/IMR/RecRun.lean's top statement, its premise paid.** -/
theorem descPure_recAll_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (x : ProofFile.Inst), ProofFile.okBy o ProofFile.pureRoad.links Z x = true →
        ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : Cols) (r : S × List Fmt.RoundView × Cols),
          foldBlocks ft l₁ (ProofFile.startS Z x.pub) rs cols = .ok r →
          RecAll Z.first.codes Z.first.shape r.1 :=
  descPure_recAll k2Share h

/-- **What "F.0.front" lays as the finish's group is the plan's.** -/
theorem finishFrontQ_group {cs : Codes} {sh : Params.ReqShape} {s t : S}
    (h : First.K2.finishFrontQ s = .ok t) (R : RecAll cs sh s) :
    ∃ (a : FinOwn) (G : ReqGroup), t.here = .fin a ∧ a.G = some G ∧
      (reqGroups sh)[s.check.frame.link]? = some G ∧ FramePub sh a.fr ∧ RecAll cs sh t := by
  have Rt : RecAll cs sh t := First.K2.finishFrontQ_rec s t h R
  obtain ⟨G, x, s₁, a, k⟩ := (First.K2.finishFrontQ_iff s t).1 h
  obtain ⟨g1, g2, -, -, g5, g6⟩ := First.K2.finishFront_all k.front
  refine ⟨{ a with G := some G, fr := x.f }, G, ?_, rfl, ?_, R.walk.carry g1 g2 g5 g6, Rt⟩
  · rw [k.out]
  · rw [← R.walk.groups]
    exact k.group

/-- **At the record in front of the first block behind the last link.** -/
theorem descPure_finish {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (x : ProofFile.Inst), ProofFile.okBy o ProofFile.pureRoad.links Z x = true →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : Cols) (r : S × List Fmt.RoundView × Cols),
          foldBlocks ft (frontOf c) (ProofFile.startS Z x.pub) rs cols = .ok r →
          ∀ t, First.K2.finishFrontQ r.1 = .ok t →
            ∃ (a : FinOwn) (G : ReqGroup), t.here = .fin a ∧ a.G = some G ∧
              (reqGroups Z.first.shape)[r.1.check.frame.link]? = some G ∧
              FramePub Z.first.shape a.fr ∧ RecAll Z.first.codes Z.first.shape t := by
  obtain ⟨Z, A, B, c, h1, h2, h3, k⟩ := descPure_recAll_paid h
  refine ⟨Z, A, B, c, h1, h2, h3, fun x hx ft rs cols r hf t ht => ?_⟩
  exact finishFrontQ_group ht (k x hx (frontOf c) [] (List.append_nil _).symm ft rs cols r hf)

/-! ## The statement grows -/

theorem k2Grows : K2Grows where
  k2 := fun p => First.K2.k2_grows p
  front := fun tl => First.K2.headFrontQ_grows tl
  openQ := fun P => First.K2.headOpenQ_grows P
  finFront := First.K2.finishFrontQ_grows
  finBehind := First.K2.finishBehindQ_grows

/-- **Johnson/IMR/GrowsSeat.lean's statement on a fold, its premise paid.** -/
theorem descPure_growsRun_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ s rs cols = .ok r → Grows s.st r.1.st :=
  descPure_growsRun k2Grows h

/-- **Johnson/IMR/RecRun.lean's statement on a yes of the file's decision, its premise paid.** -/
theorem descPure_run_paid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      (∀ (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn),
          foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
            .ok (t, rs, cols) ∧
          foldBlocks 0 (l₂ ++ backOf c) t rs cols = .ok (e, [], []) ∧
          RecAll Z.first.codes Z.first.shape t) ∧
      ∀ (l i : Nat) (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), c.links[l]? = some Lk →
        Lk.hear[i]? = some b →
        ∃ (t e : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn),
          foldBlocks 0 (c.blocksInOrder.take (IM.flatIx c l i)) (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened = .ok (t, rs, cols) ∧
          foldBlocks 0 (b :: c.blocksInOrder.drop (IM.flatIx c l i + 1)) t rs cols = .ok (e, [], []) ∧
          RecAll Z.first.codes Z.first.shape t :=
  descPure_run k2Share h hr

#print axioms k2Share
#print axioms descPure_recAll_paid
#print axioms finishFrontQ_group
#print axioms descPure_finish
#print axioms descPure_run_paid
#print axioms k2Grows
#print axioms descPure_growsRun_paid

end Meaning.K2
