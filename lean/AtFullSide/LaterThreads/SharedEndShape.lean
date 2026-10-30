-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/SharedEndShape.lean: CONDITIONAL: on the head at a return of the maker. THE FULL
SIZE ALONE.

What is here. THE SHARED CHAIN's SHARE OF THE DOOR ON SHAPES (SharedEndHasTheShape,
AtFullSide/LaterThreads/DoorOnShapes.lean), PAID UNDER THE HEAD, AT A WRITTEN VALUE: at an instance
whose key has the plan's sizes, the end of every state that the verifier's fold over the shared
chain returns has the shape that the guards' run over that chain's twelve members gives at the typed
sizes and the written tests.

  sharedRunAt Q pU pO      the guards' run over the twelve members, from the first state's shape
  writtenSharedEnd         **THE WRITTEN VALUE**: what the last chain's start reads of that run's
                           value, at the typed sizes (realSized) and the written tests piUFull, piOFull:
                           a closed term: it names no public file, no head and no letter
  run_alike, sharedRunAt_plan, sharedRun_at_the_head   under the head the run at the chain's own plan
                           and seated tests is the run at the written values
  shape_of_fold            where the fold over a whole list returns, the run on shapes returns the last
                           state's shape: general
  carries_at_the_shared_chain   (B1) at every number of the shared chain's flat list, and its length
  shared_end_at_the_head   **writtenSharedEnd = some b, and SharedEndHasTheShape h b**

By what. The proximity test's writers' carries_at (Honest/K12/AtFile/EndAtProof.lean), yes_head and
gTest_alike (Honest/K12/AtFile/EndAtHead.lean), whose shape_run_real (Honest/K12/AtFile/EndShapeRun.lean)
is an evaluation in Lean's kernel; the steps by which carries_at's premises are met under the head are
those of their end_at_head's own proof, typed here once more because that proof keeps them inside.
shape_reach, run_front (Honest/Thread/Shape.lean); reach_of_fold (Johnson/Top/H0/Walk/Reach.lean);
first_shape (Johnson/Desc/K14/Shape/Run.lean); sharedOf_eq (E2E/KeyShapeSharedChain.lean).

A THREAD IS AN ARGUMENT AND NOTHING OF IT IS READ. carries_at is stated at a thread; of it it reads the
list of members and the number of the first tree. So the readers, the fields and an input of the
shared chain's thread are arguments of the last two statements; the ends name none of them.

Not shown here. That the head is met. That any fold returns. The value itself is not evaluated here:
that the run returns is the writers' closed test. Nothing on a prover or a run. Nothing on soundness,
on completeness, on hiding or on any other property.
No property is claimed.
-/
import AtFullSide.LaterThreads.DoorOnShapes
import AtFullSide.LaterThreads.PublicFactsAtTheHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.EndAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn IndexReaders SharedThreadParts sharedThread)
open ProofFile.Honest.K12.AtFile (ZP gKP carries_at yes_head gTest_alike alike_head_O)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (Alike alike_head_U written_at_head qAt_written planOf)
open ProofFile.Honest.K14 (Plan2 ChainAt chainAt_shared shared_flat_at plan2_at_head)
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block Chain K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Ground.Sh (tidy_mark)
open _root_.Desc.K14 (P14 St blocks blocksOr)
open _root_.Desc.K14.Honest (keyW)
open _root_.Desc.K14.Shape (sh2 first_shape marked_first)
open AtPublicFiles.AtFiles (Sh₂ sh₂ gTest₂ gEnd₂ SharedSh sharedOf)
open H2K.Member (piUFull piOFull)
open H2K.JointK (guEntry omegaEntry pGu pGomega sharedPre shared_cut_omega)

/-- **The guards' run over the shared chain's twelve members, from the first state's shape.** -/
def sharedRunAt (Q : P14) (pU pO : P12) : Except String Sh₂ :=
  (ZP Q ((_root_.Desc.K14.withU Q.S).getD #[]) pU pO (fun _ _ _ _ => true)).run 12
    (sh2 (_root_.Desc.K14.first Q.codes (keyW Q.par.S.fold.index)), true)

/-- **THE WRITTEN VALUE**: what the last chain's start reads of the run's value, at the typed sizes and
the written tests. -/
def writtenSharedEnd : Option SharedSh :=
  realSized.bind fun sized =>
    (sharedRunAt (planOf sized.2 sized.1.shape).P piUFull piOFull).toOption.map sharedOf

/-- The run reads of the two tests what their alike parameters say. -/
theorem run_alike {pU qU pO qO : P12} (AU : Alike pU qU) (AO : Alike pO qO) (Q : P14)
    (sentU : Array OracleNotice)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a : Sh₂) (n : ℕ) :
    (ZP Q sentU pU pO v).run n a = (ZP Q sentU qU qO v).run n a := by
  have guards : (ZP Q sentU pU pO v).g = (ZP Q sentU qU qO v).g := by
    funext b
    show (if b < 9 then gKP Q sentU b else if b = 9 then gTest₂ pU _ _ else
        if b = 10 then gTest₂ pO _ _ else gEnd₂) =
      (if b < 9 then gKP Q sentU b else if b = 9 then gTest₂ qU _ _ else
        if b = 10 then gTest₂ qO _ _ else gEnd₂)
    rw [gTest_alike AU, gTest_alike AO]
  induction n with
  | zero => rfl
  | succ n ih =>
    show ((ZP Q sentU pU pO v).run n a).bind ((ZP Q sentU pU pO v).g n) =
      ((ZP Q sentU qU qO v).run n a).bind ((ZP Q sentU qU qO v).g n)
    rw [ih, guards]
    rfl

/-- **Where the verifier's fold over a whole list returns, the run on shapes returns the last state's
shape.** General in the shape's letters and the list. -/
theorem shape_of_fold {S Cl : Type} (Y : Shape S) {bs : List (Block S Cl)} {ft n : Nat}
    (length : bs.length = n) (carries : ∀ j, Carries bs ft Y j) {s₀ last : S}
    {rounds : List Fmt.RoundView} {columns : List VerifiableInference.Desc.OpenedColumn}
    (fold : VerifiableInference.Desc.foldBlocks ft bs s₀ rounds columns = .ok (last, [], []))
    {a₀ t : Y.Sh} (first : Y.sh s₀ = a₀) (runs : Y.run n a₀ = .ok t) : t = Y.sh last := by
  subst first
  have reached : Johnson.Desc.First.Walk.Tied.Reach ft bs (fun _ : Unit => s₀) n ((), last) :=
    Johnson.Desc.First.Walk.Tied.reach_of_fold n (Nat.le_of_eq length.symm) last _ _ _ _
      (by rw [← length, List.take_length]; exact fold)
  exact shape_reach Y carries reached t runs

/-- The run reads the codes and the shape alone. -/
theorem sharedRunAt_plan (A : ProofFile.Honest.K14.SendPub) (pU pO : P12) :
    sharedRunAt A.P pU pO = sharedRunAt (planOf A.P.codes A.P.S).P pU pO := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {nO : H2U.PlaceNums}

/-- CONDITIONAL on the head. **The run at the chain's own plan and seated tests is the run at the written
values.** -/
theorem sharedRun_at_the_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (AO : Alike (pGomega nO) piOFull) :
    ∃ sized, realSized = some sized ∧
      sharedRunAt (K1.qAt Zp Np) (pGu Np) (pGomega nO) =
        sharedRunAt (planOf sized.2 sized.1.shape).P piUFull piOFull := by
  obtain ⟨x, typed, written⟩ := written_at_head h
  have AU : Alike (pGu Np) piUFull := alike_head_U h
  refine ⟨_, typed, (run_alike AU AO _ _ _ _ _).trans ?_⟩
  have plan := sharedRunAt_plan ⟨K1.qAt Zp Np, 0⟩ piUFull piOFull
  rw [qAt_written written Np] at plan ⊢
  exact plan

/-- CONDITIONAL on the head. **(B1) at every number of a thread's list that is the shared chain's, and
that list's length.** The steps are those of end_at_head's proof (Honest/K12/AtFile/EndAtHead.lean). -/
theorem carries_at_the_shared_chain {Bk : ProverCoinCounts} {V W X Pb : Type}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hO : Np.O = some nO)
    (T : Thread Bk St ProofFile.Cl V W X Pb) {key : W → TableKey}
    (chain : ChainAt T (K1.qAt Zp Np) Zp.p.chains key)
    (list : T.bs = (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    {sentU : Array OracleNotice} {layO : OnBytes.TreeLay} (plan : Plan2 (K1.qAt Zp Np) sentU layO) :
    T.bs.length = 12 ∧ ∀ j, Carries T.bs T.ft
      (ZP (K1.qAt Zp Np) sentU (pGu Np) (pGomega nO) (fun _ _ _ _ => true)) j := by
  have h := hA.toAtMg
  obtain ⟨B⟩ := plan.eight
  have hplan : ∀ b ∈ blocksOr (K1.qAt Zp Np), b.planOk = true := by
    have e : blocksOr (K1.qAt Zp Np) = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
      unfold blocksOr
      rw [B.made]
      rfl
    rw [e]
    exact ProofFile.Honest.K12.Light.planOk_head_eight h _ B.made
  have hpre : (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np).length = 9 := by
    unfold sharedPre
    rw [AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : T.bs = (sharedPre ProofFile.Cl Zp.p.chains (K1.qAt Zp Np) Np ++ [guEntry ProofFile.Cl Np]) ++
      omegaEntry ProofFile.Cl nO :: [H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np] := by
    rw [list, shared_flat_at]
    exact shared_cut_omega ProofFile.Cl Zp.p.chains _ Np nO hO
  have gets : ∀ (pre : List (Block St ProofFile.Cl)) (a b c : Block St ProofFile.Cl), pre.length = 9 →
      ((pre ++ [a]) ++ b :: [c])[9]? = some a ∧ ((pre ++ [a]) ++ b :: [c])[10]? = some b ∧
      ((pre ++ [a]) ++ b :: [c])[11]? = some c ∧ ((pre ++ [a]) ++ b :: [c]).length = 12 := by
    intro pre a b c hl
    simp [List.getElem?_append, hl]
  obtain ⟨g9, g10, g11, gl⟩ := gets _ (guEntry ProofFile.Cl Np) (omegaEntry ProofFile.Cl nO)
    (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt Zp Np) Np) hpre
  have he := H2K.JointK.early_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_U h)
  have ha := H2K.JointK.answers_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_U h)
  have hOf : (fourOf Np).O = some (pGomega nO) := by
    show Np.O.map _ = _
    rw [hO]
    rfl
  have he' := H2K.JointK.early_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_O h hOf)
  have ha' := H2K.JointK.answers_of_planOk _ (ProofFile.Honest.K12.Light.planOk_head_O h hOf)
  exact ⟨by rw [hc]; exact gl, carries_at plan chain hplan (by rw [hc]; exact g9)
    (by rw [hc]; exact g10) (by rw [hc]; exact g11) (by rw [hc]; exact gl) he ha he' ha'
    (fun _ _ _ _ => true)⟩

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL on h. **THE SHARED CHAIN's SHARE, AT THE WRITTEN VALUE.** reads, parts, input: a thread of
the shared chain, of which nothing is read but its list of members. -/
theorem shared_end_at_the_head (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) {Wt : Type}
    (parts : SharedThreadParts A Wt) (input : Common W₀ Rc TableKey) :
    ∃ b, writtenSharedEnd = some b ∧ SharedEndHasTheShape h b := by
  obtain ⟨numbers, place, planned, seated, rfl⟩ := omega_place_at_the_head h
  obtain ⟨sentU, layO, plan⟩ := plan2_at_head h.head
  have AO : Alike (pGomega numbers) piOFull := alike_head_O h.head.toAtMg seated
  have chain : ChainAt (sharedThread h reads parts input) (K1.qAt A.Z h.places) A.Z.p.chains
      fun v => v.key := by
    unfold sharedThread
    exact chainAt_shared ..
  obtain ⟨length₀, carries₀⟩ := carries_at_the_shared_chain h.head planned
    (sharedThread h reads parts input) chain rfl plan
  have length : h.description.shared.blocksInOrder.length = 12 := length₀
  have carries : ∀ j, Carries h.description.shared.blocksInOrder 0
      (ZP (K1.qAt A.Z h.places) sentU (pGu h.places) (pGomega numbers) (fun _ _ _ _ => true)) j :=
    carries₀
  have goes : _root_.Desc.K14.withU (K1.qAt A.Z h.places).S = some sentU := plan.facts.goes
  have yes := yes_head h.head.toAtMg AO goes
  obtain ⟨t, runs⟩ := run_front _ _ 12 12 (Nat.le_refl 12) yes
  obtain ⟨sized, typed, same⟩ := sharedRun_at_the_head (nO := numbers) h.head.toAtMg AO
  have here : sharedRunAt (K1.qAt A.Z h.places) (pGu h.places) (pGomega numbers) = .ok t := by
    unfold sharedRunAt
    rw [goes]
    exact runs
  refine ⟨sharedOf t, ?_, sharedEnd_of_sharedSh h fun x rounds columns last _ sizes fold => ?_⟩
  · unfold writtenSharedEnd
    rw [typed]
    show (sharedRunAt (planOf sized.2 sized.1.shape).P piUFull piOFull).toOption.map sharedOf = _
    rw [← same, here]
    rfl
  · have starts : h.description.start₂ (h.description.pub x) =
        _root_.Desc.K14.first (K1.qAt A.Z h.places).codes x.pub.key := rfl
    have fits : VerifiableInference.Desc.Own.keyFits x.pub.key
        (K1.qAt A.Z h.places).par.S.fold.index = true := sizes
    have first : sh₂ (_root_.Desc.K14.first (K1.qAt A.Z h.places).codes x.pub.key) =
        (sh2 (_root_.Desc.K14.first (K1.qAt A.Z h.places).codes
          (keyW (K1.qAt A.Z h.places).par.S.fold.index)), true) :=
      Prod.ext (first_shape (K1.qAt A.Z h.places) x.pub.key fits)
        (tidy_mark (marked_first (K1.qAt A.Z h.places).codes x.pub.key).1)
    have is := shape_of_fold
      (ZP (K1.qAt A.Z h.places) sentU (pGu h.places) (pGomega numbers) (fun _ _ _ _ => true))
      length carries fold ((congrArg sh₂ starts).trans first) runs
    rw [is]
    exact (AtPublicFiles.AtFiles.sharedOf_eq last).symm

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.run_alike
#print axioms AtFullSide.LaterThreads.sharedRun_at_the_head
#print axioms AtFullSide.LaterThreads.carries_at_the_shared_chain
#print axioms AtFullSide.LaterThreads.shared_end_at_the_head
