-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the key file's proximity test on G_omega: the public premises at a sourced description.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/KeyAt.lean: `onOmega_key_at_run` (SimO/KeyRun.lean) at a sourced key description in scope, where the shared chain's parameters are the written `QK` (`par_sourced`): `FirstTies`, the fit of the challenges, the checks on the columns, the numbers of rounds and roots, by Lean's kernel at `QK` and `piKOFull`.

  `key_numbers`, `key_checks`   the written facts
  `onOmega_key_sourced`   **the statement**

What is left. The clause `asks`. The door's equation: hdoor: `door_key_at_omega` or `door_at_omega_scope` at the simulators' state that stands. On the run: hR, hrun, hc, S, h10. On the filling: hg, hgO, hlaid. The book's: hbk, hT. That the place stands like the written one: A, and hUr for the test on G_u's rounds. On the challenges: hdue.

Limits. A conditional. That E2E/KeyProver.lean's half at the place is this job's is not said here. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.KeyRun
import Johnson.Desc.ProofFile.Honest.K12.SimO.Key
import Johnson.Desc.ProofFile.Honest.K12.SimO.OnAtMaker
import E2E.KeyShapeSharedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces keyAsProof sharedPar beforeSharedPoint sharedTests)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first frontBlock blocks chainOf)
open Desc.K14.Honest (Like)
open H2K.Pub (sgOf)
open H2K.Member (piKOFull piKUFull)
open Johnson.Prover.Link (μOf)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open AtPublicFiles.AtFiles (KeySourced)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  carriedAt storedShown Placed Member Weights TableRand carryE Ahead Face)
open ProofFile.Honest.K14 (SendPub jobOmega sendingPart liftSend sendPlace SendDeclared sendingsFit send_declares sendDeclared_like)

theorem key_numbers : (blocks QK).map (fun bs =>
    (((bs.take 4).flatMap (·.rounds)).length,
     (bs.flatMap (·.rounds) ++ (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds).length,
     rootsOf ((bs.take 4).flatMap (·.rounds)),
     rootsOf (bs.flatMap (·.rounds) ++ (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds))) =
    some (4, 43, 1, 7) := by
  decide +kernel

theorem key_checks : (sendingsFit QK && colFitsOmega ⟨QK, 0⟩ piKOFull && widthFits (jobOmega ⟨QK, 0⟩) 0 &&
    widthFits (jobOmega ⟨QK, 0⟩) 1) = true := by
  decide +kernel

theorem src_key_written :
    firstListAtKey.map (fun o => ProofFile.Honest.srcOf 1 o.2) = [(1, 1 + 0), (1, 1 + 1), (1, 7)] := by
  decide +kernel

theorem dep_key_written :
    [depthOf piKOFull 0, depthOf piKOFull 1, (piKOFull.nums.stages.headD default).Z.a] =
      firstListAtKey.map (·.1.a) := by
  decide +kernel

theorem rounds_split {S Cl : Type} (f : Block S Cl) (bs : List (Block S Cl)) (u : Block S Cl) :
    (f :: (bs ++ [u])).flatMap (·.rounds) = f.rounds ++ (bs.flatMap (·.rounds) ++ u.rounds) := by
  simp [List.flatMap_append]

/-- **The condition at a run, at a sourced key description.** -/
theorem onOmega_key_sourced {W₀ Rc Tr X₀ Y : Type} {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {Bk : ProverCoinCounts} {P : Prover W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    {w₀ : W₀} {rc : Rc} {x : VerifiableInference.Desc.Key.Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc VerifiableInference.Desc.Key.Xi TableKey Tr X₀ Y}
    {r : RunC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl)}
    (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k = .ok R)
    (hrun : runC (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ = .ok r)
    (pU pO : P12) (hU : pU = H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U) (A : AtKeyPlace pO)
    (hUr : (proximityTestKind guardedProximityTestParts pU : Block T12 Unit).rounds = (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (hb : blocks QK = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (Js : SimJob TableKey) (hJ : Js.p = pO) (ho' : Js.own = true)
    (σ : Side St VerifiableInference.Desc.Key.Claim Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hσ : σ.block.place = pO.place) (pre t : List (Block St VerifiableInference.Desc.Key.Claim))
    (S : StandsAt (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder R.shared σ
      (restMember (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded pre t (firstLen (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages))
    (h10 : pre = (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder.take 10)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hdoor : ∀ m, midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).rec₀ m.st.input (restFront (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) =
        Js.rec₀ ((Face.shared : Face Empty (Common W₀ Rc TableKey) TableKey).pub m.st.input)
          ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩).cut
            (firstLen (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)))
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).laid)
    (hor : σ.block.rounds.length ≤ σ.block.oracles.length)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨QK, 0⟩ weights rand) (sendingPart (jobOmega ⟨QK, 0⟩)) :
        ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hbk : bookCutsOmega Bk ⟨QK, 0⟩ pO = true)
    (hT : ProofFile.Honest.K12.Own.tiesOB Bk pO.place 2 = true)
    (hdue : drawsFit (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).roundsDeclaredByBlocks.2.1 ρ.shared = true) :
    ∃ (c : ProofFile.Honest.RowCoins
        [(firstPart (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField,
        (restPart (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀),
      midSharedAtW (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) : ProofFile.Honest.Part Empty (Common W₀ Rc TableKey) X₀).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p).take (firstLen (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
          Dp.ts.length = firstListAtKey.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) H2K.Member.codesKeyFull Dp ∧
          DataAsks (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m.st.input (restFront (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m)
            (carriedCoins (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) m) Dp cc Rw) →
        (∃ cs, m.opened = some cs) ∧
          OnEntryOwn Face.shared (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js H2K.Member.codesKeyFull 1 firstListAtKey
            (restMember (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js : Member Empty _ _ _).guarded c.2.1.2.2 m
            (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)) := by
  have hpl : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).planOk = true := hs.named.plan
  have e := par_sourced hs scope
  obtain ⟨s, next, rest, hlit⟩ : ∃ s next rest, piKOFull.nums.stages = s :: next :: rest := ⟨_, _, _, rfl⟩
  have hst : (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages = s :: next :: rest := by
    show pO.nums.stages = _
    rw [A.nums, hlit]
  have F₁ : FirstPubOwn (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js := firstPubOwn_key A _ rfl rfl Js hJ ho'
  have hle := S.le
  have hi : firstLen (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.nums.stages ≤ σ.block.rounds.length := by omega
  obtain ⟨hfit, T⟩ := firstTies_at_run hR (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀) Js σ _ pre t _ S hi hor hlaid F₁ s next rest hst hdue
  have FP := formPub_of_B (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p s next rest hst F₁.form
  have hk' : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have hT' : ProofFile.Honest.K12.Own.tiesOB Bk (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place (keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).members.length = true := hT
  unfold ProofFile.Honest.K12.Own.tiesOB at hT'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT'
  obtain ⟨⟨t2, t3⟩, t4⟩ := hT'
  obtain ⟨e₂, he₂, k2⟩ := Option.map_eq_some_iff.1 t2
  -- the cut at the sending
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    Desc.K14.Honest.flatOf_carried (Cl := VerifiableInference.Desc.Key.Claim) (keyAsProof Xs.chains) QK
      b1 b2 b3 b4 b5 b6 b7 b8 (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last hb
  have eD : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := by
    show ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
    rw [VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat, e]
    exact eF
  have eO : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder =
      [x0, x1, x2, x3, x4] ++ x5 :: x6 :: x7 :: x8 :: tl := eD
  obtain ⟨-, -, dO, pO'⟩ := send_declares QK 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hpO : x5.place = sendPlace 5 := l5.place.trans pO'
  -- the numbers
  have kn := key_numbers
  rw [hb] at kn
  have kn' := Option.some.inj kn
  have n1 : (([b1, b2, b3, b4, b5, b6, b7, b8].take 4).flatMap (·.rounds)).length = 4 := congrArg (·.1) kn'
  have n2 : ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) ++
      (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds).length = 43 := congrArg (·.2.1) kn'
  have n3 : rootsOf (([b1, b2, b3, b4, b5, b6, b7, b8].take 4).flatMap (·.rounds)) = 1 := congrArg (·.2.2.1) kn'
  have n4 : rootsOf ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) ++
      (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds) = 7 := congrArg (·.2.2.2) kn'
  have hq : List.flatMap (fun y : Block St VerifiableInference.Desc.Key.Claim => y.rounds) [x0, x1, x2, x3, x4] =
      ([b1, b2, b3, b4, b5, b6, b7, b8].take 4).flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds]
    rfl
  have hqp : pre.flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) ++ (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds := by
    obtain ⟨pre₀, tl₀, e₀, hl₀, hL₀⟩ := flat_ten_key (Cl := VerifiableInference.Desc.Key.Claim) (keyAsProof Xs.chains) QK Pl
      b1 b2 b3 b4 b5 b6 b7 b8 hb
    have e' : (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).shared.blocksInOrder = pre₀ ++ tl₀ := by
      show ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
        (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
      rw [VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat, e]
      exact e₀
    have hp : pre = pre₀ := h10.trans ((congrArg (List.take 10) e').trans (List.take_left' hl₀))
    have r1 := rounds_like hL₀
    have h3 : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U))).rounds =
        (proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds := by
      rw [← hU]
      exact hUr
    rw [hp, ← r1, rounds_split, h3]
    rfl
  have kc := key_checks
  simp only [Bool.and_eq_true] at kc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := kc
  refine onOmega_key_of_door hpl hR hrun QK pU pO _ weights rand Js
    σ hσ pre t S hc hdoor hg hlaid hgO hbk e₂ he₂ (congrArg (·.1) k2) (congrArg (·.2) k2) (fun t' ht => ?_)
    s next rest _ T FP.hk hk' (fun w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) hfit c1
    (by rw [colFitsOmega_stages _ (congrArg (·.stages) A.nums)]; exact c2) c3 c4 [x0, x1, x2, x3, x4] _ x5 eO hpO
    (sendDeclared_like l5.rounds l5.oracles dO) (by rw [hq, hqp, n1, n2]; decide)
    (by rw [hq, n1]; show 0 < 4; decide) firstListAtKey (by rw [hq, hqp, n3, n4]; exact src_key_written)
    (by
      unfold depthOf
      rw [A.nums]
      exact dep_key_written) H2K.Member.codesKeyFull
  have e4 := congrArg (·[t']?) t4
  simp only [List.getElem?_map, List.getElem?_take, if_pos ht] at e4
  obtain ⟨a, ha⟩ : ∃ a, (carryE Bk ⟨(keyJobO QK pU pO [b1, b2, b3, b4, b5, b6, b7, b8] weights rand : TestJob (Common W₀ Rc TableKey) X₀).p.place, 0⟩)[t']? = some a :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [ha, Option.map_some] at e4
  obtain ⟨a', ha', k3⟩ := Option.map_eq_some_iff.1 e4.symm
  exact ⟨a, a', ha, ha', (congrArg (·.1) k3).symm, (congrArg (·.2.1) k3).symm,
    (congrArg (·.2.2) k3).symm⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.key_numbers
#print axioms ProofFile.Honest.K12.Light.key_checks
#print axioms ProofFile.Honest.K12.Light.onOmega_key_sourced
