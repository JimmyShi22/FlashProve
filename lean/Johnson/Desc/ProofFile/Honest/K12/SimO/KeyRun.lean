-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the key file's proximity test on G_omega: the condition at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/KeyRun.lean: AT THE KEY FILE's DESCRIPTION, at a run of the frame's walking prover, at the job `jobAtOmega` at a simulators' job whose state is `stateAtOmega`: the door's equation and the clause on the columns, so the condition at a called second part behind the guard, from its clause `asks`. The key file's shared chain is `chainOf` at `keyAsProof` (Johnson/Desc/Key/SharedChainIsChainOf.lean), so the road of the proof file's goes over.

  `flat_ten_key`       the first ten blocks of the key file's shared chain
  `start_key`, `door_key_at_omega`   the start of that chain; the door's equation, as `door_at_omega` at this description
  `keyJobO`            the job
  `onOmega_key_of_door`   the statement from the door's equation as a premise: any simulators' state that meets it
  `onOmega_key_at_run` **the statement**

Premises, named. On the run: hpl, hR, hrun, hc, S, h10. On the filling: hg, hgO, hlaid, hα. The book's: hbk, e₂, hf, ho, hst, hmem. Public: T, hk, hk', hrows, hfit, hQ, hcf, hw0, hw1, hat, hinO, hsrc, hdep. The clause `asks`.

Limits. A conditional. That E2E/KeyProver.lean's half at the place is this job's is not said here. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.OnAtHead
import Johnson.Desc.Key.SharedChainIsChainOf
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.Key (Source LaterPlaces keyAsProof sharedPar beforeSharedPoint sharedTests)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first frontBlock blocks chainOf)
open Desc.K14.Honest (Like)
open H2K.Pub (sgOf)
open Johnson.Prover.Link (μOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  carriedAt storedShown Placed Member Weights TableRand carryE Ahead Face)
open ProofFile.Honest.K14 (SendPub jobOmega sendingPart liftSend sendPlace SendDeclared sendingsFit)
open ProofFile.Honest.K12.Sim2 (stateFromViewOnSharedChain stateFromViewOnSharedChain_at_stand)

/-- **The first ten blocks of a shared chain at `sharedTests`.** -/
theorem flat_ten_key {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14) (N : LaterPlaces)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ (pre : List (Block St Cl)) (tl : List (Block St Cl)),
      ((chainOf c Q (sharedTests N) VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder = pre ++ tl ∧
      pre.length = 10 ∧
      List.Forall₂ Like pre (frontBlock c :: ([b1, b2, b3, b4, b5, b6, b7, b8] ++
        [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U))])) := by
  rw [Desc.K14.Law.flat_retype_all c Q b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb]
  refine ⟨Desc.K14.Law.frontOf c :: ([b1, b2, b3, b4, b5, b6, b7, b8].map Block.retype ++
      [Desc.K14.Law.bareOf (Block.retype (VerifiableInference.Desc.K12.Seat.onGu
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U))))]),
    (((N.O.toList.map fun nO => VerifiableInference.Desc.K12.Seat.onGomega
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))) ++
      [VerifiableInference.Desc.K12.Seat.last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ sharedTests N)]).map
        Block.retype).map Desc.K14.Law.bareOf, ?_, rfl, ?_⟩
  · simp [sharedTests]
  · exact .cons (Desc.K14.Honest.like_frontOf c) (.cons (Desc.K14.Honest.like_retype b1)
      (.cons (Desc.K14.Honest.like_retype b2) (.cons (Desc.K14.Honest.like_retype b3)
      (.cons (Desc.K14.Honest.like_retype b4) (.cons (Desc.K14.Honest.like_retype b5)
      (.cons (Desc.K14.Honest.like_retype b6) (.cons (Desc.K14.Honest.like_retype b7)
      (.cons (Desc.K14.Honest.like_retype b8) (.cons ⟨rfl, rfl, rfl, rfl⟩ .nil)))))))))

/-- The key file's start of the shared chain. -/
theorem start_key (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (bp : List (ℕ × ℕ))
    (x : VerifiableInference.Desc.Key.Xi) :
    (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).start₂ ((VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).pub x) =
      first (sharedPar Xs.chains bp).codes x.key := by
  unfold VerifiableInference.Desc.Key.descriptionFromSource
  rfl

/-- **The door's equation at the key file.** As `door_at_omega`, whose proof it repeats at this description. -/
theorem door_key_at_omega {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    {W₀ Rc Tr X₀ Y V Pq : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : VerifiableInference.Desc.Key.Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y} {r : RunC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)}
    (hpl : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true) (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl V (Common W₀ Rc TableKey) X₀ Pq)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pq)
    (pre t : List (Block (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).S₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).Cl)) (i : ℕ)
    (S : StandsAt (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder R.shared σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (bs : List (Block St Unit)) (p : P12)
    (hpre : List.Forall₂ Like pre (frontBlock c ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])))
    (hstart : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).start₂ ((VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).pub x) = first Q.codes (P.key x))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hi : i = firstLen J.p.nums.stages) :
    ∃ m, ProofFile.Honest.midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      doorOmegaF Q sentU bs p (fun w : Common W₀ Rc TableKey => w.key) colsOpened m.st.input (restFront J m) =
        stateAtOmega Q sentU p (frontBlock c :: (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])) (P.key x)
          ((r.run.beforeAt (ProofFile.Honest.storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, u.number⟩).cut i) := by
  obtain ⟨m, s, cols, hm, hin, ho, hseen, hfold, hrd, hcl, -⟩ := stateFromViewOnSharedChain_at_stand hpl hR hrun σ u pre t i S hc
    (first Q.codes) (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) (fallOmega Q sentU p) (P.key x)
    hstart.symm
  refine ⟨m, hm, ?_⟩
  have hlen : m.seen.length = (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
    have Q' := ((VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk_ok).1 hpl
    obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ProofFile.Honest.ready_ok hR
    obtain ⟨-, l2, -⟩ := ProofFile.Honest.runC_laidAs hrun hR (ProofFile.Honest.steps_shaped s1 Q'.blocks₁)
      (ProofFile.Honest.steps_shaped s2 Q'.blocks₂) (ProofFile.Honest.steps_shaped s3 Q'.blocks₃)
    have d₂ := ProofFile.Honest.laidAs_drawn l2
    have hall : r.run.played.2.1.length = R.shared.length := by
      have h1 := congrArg List.length d₂
      rw [List.length_map] at h1
      exact h1.trans l2.1
    have hfits := S.fits
    rw [hseen, ProofFile.Honest.roundsOf_length, List.length_take, hall, ← hi]
    omega
  obtain ⟨e1, e2⟩ := rest_front_at J m (pre.flatMap (·.rounds)).length hlen
  have hN : m.seen.take (pre.flatMap (·.rounds)).length =
      ProofFile.Honest.roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) := by
    rw [hseen]
    unfold ProofFile.Honest.roundsOf
    rw [← List.map_take, List.take_take]
    simp
  rw [hstart] at hfold
  have hd := door_of_opened c Q sentU bs p pre hpre (P.key x) _ cols s hfold
    (fun w : Common W₀ Rc TableKey => w.key) m.st.input (restFront J m) (by rw [hin]) (e1.trans hN)
    (e2.trans ho)
  have hL : (frontBlock c :: (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])).flatMap (·.rounds) =
      pre.flatMap (·.rounds) := rounds_like hpre
  have hf' := Desc.K14.Honest.fold_like 0 _ _ hpre _ _ _ _ hfold
  show _ = stateFromViewOnSharedChain _ (first Q.codes) _ _ _ _
  unfold stateFromViewOnSharedChain ProofFile.Honest.K12.Sim2.doorFromViewOnSharedChain
  rw [hL, hcl, hrd]
  dsimp only
  rw [hf']
  show _ = ((VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) s).toOption.getD _ 
  rw [hd]
  rfl


/-- The job at the key file's test. -/
abbrev keyJobO {W₀ Rc X₀ : Type} (Q : P14) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    TestJob (Common W₀ Rc TableKey) X₀ :=
  (jobAtOmega ⟨Q, 0⟩ pO (doorOmegaF Q (sentOf Q.S) bs pU (fun w : Common W₀ Rc TableKey => w.key) colsOpened) weights rand none).toRun.toTest

/-- **The condition at a run, at the key file's description, from the door's equation.** The equation is `door_key_at_omega`'s or `door_at_omega_scope`'s, by the simulators' state that a caller lays. -/
theorem onOmega_key_of_door {W₀ Rc Tr X₀ Y : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    {w₀ : W₀} {rc : Rc} {x : VerifiableInference.Desc.Key.Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    {r : RunC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)}
    (hpl : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true)
    (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (Q : P14) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (Js : SimJob TableKey)
    (σ : Side St VerifiableInference.Desc.Key.Claim Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hσ : σ.block.place = pO.place) (pre t : List (Block St VerifiableInference.Desc.Key.Claim))
    (S : StandsAt (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder R.shared σ
      (restMember (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded pre t (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages))
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hdoor : ∀ m, midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).rec₀ m.st.input (restFront (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) =
        Js.rec₀ ((Face.shared : Face Empty (Common W₀ Rc TableKey) TableKey).pub m.st.input)
          ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩).cut
            (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).laid)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨Q, 0⟩ weights rand) (sendingPart (jobOmega ⟨Q, 0⟩)) :
        ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hbk : bookCutsOmega Bk ⟨Q, 0⟩ pO = true)
    (e₂ : Ahead) (hf : (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0 + 1⟩)[(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length]? = some e₂)
    (ho : e₂.owner = ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length → ∃ a a', (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dd : ℕ → Fmt.Drawn)
    (T : FirstTies (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) s next rest Dd
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)))
    (hk : s.h ≤ s.k) (hk' : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ Rc TableKey) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length → mem t = mem' t) →
      μOf (sgOf s) ((keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).rows₀ w fr mem) = μOf (sgOf s) ((keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)) = true)
    (hQ : sendingsFit (⟨Q, 0⟩ : SendPub).P = true) (hcf : colFitsOmega ⟨Q, 0⟩ pO = true)
    (hw0 : widthFits (jobOmega ⟨Q, 0⟩) 0 = true) (hw1 : widthFits (jobOmega ⟨Q, 0⟩) 1 = true)
    (preO tO : List (Block St VerifiableInference.Desc.Key.Claim)) (bO : Block St VerifiableInference.Desc.Key.Claim)
    (hcutO : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder = preO ++ bO :: tO)
    (hpO : bO.place = sendPlace 5) (hdO : SendDeclared bO (jobOmega ⟨Q, 0⟩))
    (hinO : (preO.flatMap (·.rounds)).length + 2 ≤ (pre.flatMap (·.rounds)).length)
    (hat : (⟨Q, 0⟩ : SendPub).atPoint < (preO.flatMap (·.rounds)).length)
    (os : List (Fmt.Shape × Fmt.TreeSource))
    (hsrc : os.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
      [(1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0),
       (1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 1),
       (1, Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)))])
    (hdep : [depthOf pO 0, depthOf pO 1, (pO.nums.stages.headD default).Z.a] = os.map (·.1.a))
    (K : OnBytes.Codes) :
    ∃ (c : ProofFile.Honest.RowCoins
        [(firstPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField,
        (restPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀),
      midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
          Dp.ts.length = os.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) K Dp ∧
          DataAsks (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) Dp cc Rw) →
        (∃ cs, m.opened = some cs) ∧
          OnEntryOwn Face.shared (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js K 1 os (restMember (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded c.2.1.2.2 m
            (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)) := by
  obtain ⟨c, m, hm, hca, hin, hf3, hon⟩ := onOmega_at_run hpl _ rfl Js hR σ pre t S hg hlaid e₂ hf ho hst hmem
    s next rest Dd T hk' hrows hfit hrun hc (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
    Face.shared 1 os K
  refine ⟨c, m, hm, hca, hin, hf3, fun hasks => hon ?_ ?_ hasks⟩
  · exact hdoor m hm
  · exact trees_at_run_omega hpl hR hrun ⟨Q, 0⟩ pO _ weights rand _ rfl Js σ hσ pre t S hc hg hlaid preO tO bO hcutO
      hpO (by rw [hpO]; exact hgO) hdO hinO hbk hQ hcf hw0 hw1 hat e₂ hf ho hst hmem s next rest Dd T hk hrows os
      hsrc hdep _ m _ hm hca

/-- **The condition at a run, at the key file's description.** -/
theorem onOmega_key_at_run {W₀ Rc Tr X₀ Y : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    (hα : ∀ x, P.key x = x.key) {w₀ : W₀} {rc : Rc} {x : VerifiableInference.Desc.Key.Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    {r : RunC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)}
    (hpl : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true)
    (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (Q : P14) (hQe : Q = sharedPar Xs.chains (beforeSharedPoint Pl)) (pU pO : P12)
    (hU : pU = H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (bs : List (Block St Unit))
    (hbs : bs = [b1, b2, b3, b4, b5, b6, b7, b8]) (hb : blocks Q = some bs)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (Js : SimJob TableKey)
    (hJs : Js.rec₀ = stateAtOmega Q (sentOf Q.S) pU (frontBlock (keyAsProof Xs.chains) ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)])))
    (σ : Side St VerifiableInference.Desc.Key.Claim Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hσ : σ.block.place = pO.place) (pre t : List (Block St VerifiableInference.Desc.Key.Claim))
    (S : StandsAt (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder R.shared σ
      (restMember (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded pre t (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages))
    (h10 : pre = (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder.take 10)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).laid)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨Q, 0⟩ weights rand) (sendingPart (jobOmega ⟨Q, 0⟩)) :
        ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hbk : bookCutsOmega Bk ⟨Q, 0⟩ pO = true)
    (e₂ : Ahead) (hf : (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0 + 1⟩)[(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length]? = some e₂)
    (ho : e₂.owner = ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length → ∃ a a', (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨(keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dd : ℕ → Fmt.Drawn)
    (T : FirstTies (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) s next rest Dd
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)))
    (hk : s.h ≤ s.k) (hk' : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ (w : Common W₀ Rc TableKey) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length → mem t = mem' t) →
      μOf (sgOf s) ((keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).rows₀ w fr mem) = μOf (sgOf s) ((keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).rows₀ w fr mem'))
    (hfit : drawsFit (((H2K.JointK.laidOf (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)) = true)
    (hQ : sendingsFit (⟨Q, 0⟩ : SendPub).P = true) (hcf : colFitsOmega ⟨Q, 0⟩ pO = true)
    (hw0 : widthFits (jobOmega ⟨Q, 0⟩) 0 = true) (hw1 : widthFits (jobOmega ⟨Q, 0⟩) 1 = true)
    (preO tO : List (Block St VerifiableInference.Desc.Key.Claim)) (bO : Block St VerifiableInference.Desc.Key.Claim)
    (hcutO : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder = preO ++ bO :: tO)
    (hpO : bO.place = sendPlace 5) (hdO : SendDeclared bO (jobOmega ⟨Q, 0⟩))
    (hinO : (preO.flatMap (·.rounds)).length + 2 ≤ (pre.flatMap (·.rounds)).length)
    (hat : (⟨Q, 0⟩ : SendPub).atPoint < (preO.flatMap (·.rounds)).length)
    (os : List (Fmt.Shape × Fmt.TreeSource))
    (hsrc : os.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
      [(1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0),
       (1, Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 1),
       (1, Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)))])
    (hdep : [depthOf pO 0, depthOf pO 1, (pO.nums.stages.headD default).Z.a] = os.map (·.1.a))
    (K : OnBytes.Codes) :
    ∃ (c : ProofFile.Honest.RowCoins
        [(firstPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField,
        (restPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀),
      midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p).take (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
          Dp.ts.length = os.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) K Dp ∧
          DataAsks (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) Dp cc Rw) →
        (∃ cs, m.opened = some cs) ∧
          OnEntryOwn Face.shared (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js K 1 os (restMember (keyJobO Q pU pO bs weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded c.2.1.2.2 m
            (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)) := by
  refine onOmega_key_of_door hpl hR hrun Q pU pO bs weights rand Js σ hσ pre t S hc ?_ hg hlaid hgO hbk e₂ hf ho hst
    hmem s next rest Dd T hk hk' hrows hfit hQ hcf hw0 hw1 preO tO bO hcutO hpO hdO hinO hat os hsrc hdep K
  intro m hm
  subst hbs hU
  have hbq : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] := hb
  obtain ⟨pre₀, tl, e, hl, hL⟩ := flat_ten_key (Cl := VerifiableInference.Desc.Key.Claim) (keyAsProof Xs.chains) Q Pl
    b1 b2 b3 b4 b5 b6 b7 b8 hbq
  have e' : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder = pre₀ ++ tl := by
    show ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
    rw [VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat, ← hQe]
    exact e
  have hp : pre = pre₀ := h10.trans ((congrArg (List.take 10) e').trans (List.take_left' hl))
  rw [hp] at S
  obtain ⟨m', hm', he⟩ := door_key_at_omega hpl hR hrun σ _ pre₀ t _ S hc (keyAsProof Xs.chains) Q (sentOf Q.S)
    [b1, b2, b3, b4, b5, b6, b7, b8] _ hL (by rw [hα x, hQe]; exact start_key Xs N Pl _ x) _ rfl
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
  obtain ⟨m2, -, -, -, -, hm2, hin2, -⟩ := called_at_run hpl hR σ _ pre₀ t _ S hrun hc
  have hin : m.st.input = ⟨w₀, rc, P.key x⟩ := by
    rw [← Option.some.inj (Except.ok.inj (hm2.symm.trans hm))]
    exact hin2
  have hkey : (Face.shared : Face Empty (Common W₀ Rc TableKey) TableKey).pub m.st.input = P.key x := by
    rw [hin]
    rfl
  rw [hkey, hJs]
  exact he

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.flat_ten_key
#print axioms ProofFile.Honest.K12.Light.onOmega_key_of_door
#print axioms ProofFile.Honest.K12.Light.onOmega_key_at_run
