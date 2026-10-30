-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of the row of the test on the ranges.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowRangesPub.lean: what onAtRun_ranges asks of the numbers and
the book, at the written sending of the multiplicities and at keyBook, by Lean's kernel.

  k1CutFits_congr, oneSenderPub_congr   the two tests read a plan's codes and messages alone
  msgFull, rngStage   the plan at the written codes and messages; the test's first stage
  one_sender_full, book_rng_full, book_rng_at   the numbers and the book, by the kernel; at a plan
  msgTree, tree_facts_full, tree_facts_at   the sending's tree
  msg_cut   where the sender stands
  onAtRun_ranges_book   onAtRun_ranges at keyBook and the multiplicities' job, its public premises paid

Limits. onAtRun_ranges_book keeps hj, hg, hgS and hleft as premises, and holds JS to msgJob at rangesTestJob's
own entry and groups: that the prover's multiplicities sender is this job is the caller's. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesAtRun
import E2E.KeyBookAtWritten
import E2E.KeyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Place)
open Johnson.Prover.Send (shapeAt)
open H2K.Member (piKRFull)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub rideMsg msgPlace rngPlace)
open Lk6.AtPlan (keyFull)
open ProofFile.Honest ProofFile.Honest.K12

/-- The test on the book reads of a plan its codes and messages alone. -/
theorem k1CutFits_congr (Bk : ProverCoinCounts) (a : Addr) (n : ℕ) (s : Addr)
    {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes) (hs : P.sent = P'.sent)
    (ride : ℕ → Option K1.Ride) (kk : ℕ) :
    k1CutFits Bk a n s P ride kk = k1CutFits Bk a n s P' ride kk := by
  have e1 : ∀ j, K1.dueMsg P.codes (shapeAt P j) (ride j) = K1.dueMsg P'.codes (shapeAt P' j) (ride j) :=
    fun j => by simp only [shapeAt, hc, hs]
  have e2 : ∀ j, K1.startR P ride j = K1.startR P' ride j := fun j => by
    unfold K1.startR
    simp only [e1]
  have e3 : K1.dueR P ride = K1.dueR P' ride := by
    unfold K1.dueR
    rw [e2, hs]
  unfold k1CutFits
  rw [e1, e2, e3]

/-- **The plan at the written codes and messages.** -/
def msgFull : VerifiableInference.Desc.K1.Par :=
  { place := msgPlace, codes := keyFull.codes, gp := ⟨0, 0⟩, work := 0,
    parts := [("", OnBytes.Wf.messageOf keyFull.ranges.x)] }

/-- The test's first stage. -/
abbrev rngStage : Fmt.M1.Stage := piKRFull.nums.stages.headD default

theorem one_sender_full : OneSenderPub msgFull rideMsg rngStage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

theorem book_rng_full : (fullPub.map fun K =>
    k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 0 ⟨msgPlace, 0⟩ msgFull rideMsg 0 &&
      k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 1 ⟨msgPlace, 0⟩ msgFull rideMsg 1 &&
      tiesB (keyBook K) rngPlace 1) = some true := by
  decide +kernel

/-- The public numbers read of a plan its codes and messages alone. -/
theorem oneSenderPub_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) {ride : ℕ → Option K1.Ride} {s : Fmt.M1.Stage}
    (h : OneSenderPub P' ride s) : OneSenderPub P ride s := by
  have es : ∀ k, shapeAt P k = shapeAt P' k := fun k => by simp only [shapeAt, hs]
  exact ⟨by rw [hs]; exact h.two, by rw [hs, hc]; exact h.mine, by rw [es]; exact h.main1,
    by rw [es]; exact h.rows1, by rw [es, hc]; exact h.ell, by rw [es, hc]; exact h.tail, h.ride1,
    h.hk, h.room, by rw [es]; exact h.deg, by rw [es, hc]; exact h.due⟩

theorem book_rng_at {K : KeyPub} (hK : fullPub = some K) {P : VerifiableInference.Desc.K1.Par}
    (hc : P.codes = msgFull.codes) (hs : P.sent = msgFull.sent) :
    k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 0 ⟨msgPlace, 0⟩ P rideMsg 0 = true ∧
      k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 1 ⟨msgPlace, 0⟩ P rideMsg 1 = true ∧
      tiesB (keyBook K) rngPlace 1 = true := by
  have e := book_rng_full
  rw [hK] at e
  have e' : (k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 0 ⟨msgPlace, 0⟩ msgFull rideMsg 0 &&
      k1CutFits (keyBook K) ⟨rngPlace, 1⟩ 1 ⟨msgPlace, 0⟩ msgFull rideMsg 1 &&
      tiesB (keyBook K) rngPlace 1) = true := Option.some.inj e
  simp only [Bool.and_eq_true] at e'
  exact ⟨(k1CutFits_congr _ _ _ _ hc hs _ _).trans e'.1.1,
    (k1CutFits_congr _ _ _ _ hc hs _ _).trans e'.1.2, e'.2⟩

/-- The tree of the written sending. -/
abbrev msgTree : OnBytes.TreeShape := msgFull.trees.getD 0 {}

theorem tree_facts_full : msgFull.trees[0]? = some msgTree ∧
    columnWidth msgFull 0 = msgTree.mainWidth + msgTree.maskWidth ∧
    msgTree.logN = (piKRFull.nums.first.headD default).1.a ∧
    ProofFile.Honest.srcOf 0 (piKRFull.nums.first.headD default).2 = (0, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- A column's width, of a plan's codes and messages. -/
def widthOf (c : OnBytes.Codes) (s : Array OnBytes.OracleNotice) (t : ℕ) : ℕ :=
  let lay := (VerifiableInference.Desc.Own.treesMade c s).getD {}
  let mine := (List.range s.size).filter fun k => lay.tree[k]? == some t
  (mine.map fun k => (s.getD k default).shape.mainRows *
      (if (s.getD k default).shape.mainDeg == 3 then 3 else 1)).sum +
    (mine.map fun k => (s.getD k default).shape.maskRows * 3).sum

/-- The numbers of a tree read of a plan its codes and messages alone. -/
theorem tree_facts_at {P : VerifiableInference.Desc.K1.Par} (hc : P.codes = msgFull.codes)
    (hs : P.sent = msgFull.sent) : P.trees[0]? = some msgTree ∧
    columnWidth P 0 = msgTree.mainWidth + msgTree.maskWidth ∧
    (P.trees.getD 0 {}).logN = (piKRFull.nums.first.headD default).1.a := by
  have e1 : P.trees = msgFull.trees := by
    unfold VerifiableInference.Desc.K1.Par.trees
    rw [hc, hs]
  have e2 : columnWidth P 0 = columnWidth msgFull 0 := by
    show widthOf P.codes P.sent 0 = widthOf msgFull.codes msgFull.sent 0
    rw [hc, hs]
  obtain ⟨f1, f2, f3, -⟩ := tree_facts_full
  exact ⟨by rw [e1]; exact f1, by rw [e2]; exact f2, by rw [e1]; exact f3⟩

section Cut
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open AtPublicFiles.KeyBook (places_named fullFirst)
open VerifiableInference.Desc (Block)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **Where the multiplicities' sender stands**: the second block of the key file's first chain. -/
theorem msg_cut (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    ∃ (b₀ bS : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)
      (tS : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)),
      (keyFileDescription Xs N Pl).first.blocksInOrder = [b₀] ++ bS :: tS ∧ bS.place = msgPlace ∧ bS.rounds.length = 2 ∧
      b₀.rounds.length = 2 := by
  have r := (places_named scope h).1
  have e : ((keyFileDescription Xs N Pl).first.blocksInOrder.map fun b => (b.place, b.rounds.length)) = fullFirst := r
  cases hf : (keyFileDescription Xs N Pl).first.blocksInOrder with
  | nil =>
    rw [hf] at e
    have hl := congrArg List.length e
    have f : fullFirst.length = 19 := by decide +kernel
    simp only [List.map_nil, List.length_nil] at hl
    omega
  | cons b₀ l =>
    cases l with
    | nil =>
      rw [hf] at e
      have hl := congrArg List.length e
      have f : fullFirst.length = 19 := by decide +kernel
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hl
      omega
    | cons bS tS =>
      rw [hf] at e
      have e0 := congrArg (·[0]?) e
      have e1 := congrArg (·[1]?) e
      have f0 : fullFirst[0]?.map (·.2) = some 2 := by decide +kernel
      have f1 : fullFirst[1]? = some (msgPlace, 2) := by decide +kernel
      simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ] at e0 e1
      rw [f1] at e1
      rw [← e0] at f0
      have g1 := Option.some.inj e1
      exact ⟨b₀, bS, tS, rfl, congrArg Prod.fst g1, congrArg Prod.snd g1, Option.some.inj f0⟩

end Cut

section Join
open VerifiableInference.Desc.Key (Xi rangesParams LaterPlaces Source pieces)
open H2K.Member (codesKeyFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyThread (rangesTestJob sentRanges place_sourced)
open AtPublicFiles.Key (msgJob)
open VerifiableInference.Desc (Block)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky X₀ Y : Type}

theorem msgFull_sent : msgFull.sent = OnBytes.Wf.messageOf keyFull.ranges.x := by
  show ([("", OnBytes.Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray = _
  simp

theorem two_in_front : 2 < firstLen piKRFull.nums.stages := by decide +kernel

/-- **The clause of the rule at the list of the test on the ranges, at the key's book and the
multiplicities' own job.** What stays: hj, the filling's hg and hgS, and hleft. -/
theorem onAtRun_ranges_book (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K : KeyPub}
    (hK : fullPub = some K) {H : Prover W₀ Rc Xi Ky Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K) W₀ Rc Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins (keyBook K)} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k ρ = .ok r)
    (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → OnBytes.Slice.GF) (groups : List (List ℕ))
    (first first' : ℕ)
    (L : Lettered (keyBook K) (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi)
    (hplace : L.place = rngPlace)
    (hrow : L.row = testPairs (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl))
    (hOn : L.On = OnEntry Face.own (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)
      codesKeyFull 0 piKRFull.nums.first)
    (hg : ((G.prover H).first.find? fun g => g.place == rngPlace) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Y) Xs N Pl entry groups first)))
    (hgS : ((G.prover H).first.find? fun g => g.place == msgPlace) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit)
        (msgJob (X := Y) entry Xs.Y.k.oneTime pieces groups first' rideMsg)))
    (hj : treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 = 1)
    (hleft : ∀ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc Xi Unit)
        (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)).part.carries)
      (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y Xi)
      (pre' t' : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)),
      testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob (X' := Y) Xs N Pl entry groups first)
        (simRanges Xs N Pl) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).first.blocksInOrder R.first σ (restMember (V := Local W₀ Rc Xi Unit)
                            (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)) pre' t'
        (firstLen (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.nums.stages) →
      InsideOf .own (keyBook K) 0 (G.prover H).first σ.block (T.I₁ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midAtW (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt (keyBook K) k 0 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
        (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)).part = .ok ca →
      (laidOf (keyFileDescription Xs N Pl) ρ (r.run.played.1.take ((pre'.flatMap (·.rounds)).length +
                     σ.roundsTo 1)) [] []).front 0
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtRanges (rangesTestJob (X' := Y) Xs N Pl entry groups first) codesKeyFull piKRFull.nums.first
        (stretches _ ca) m) :
    OnAtRun₁ T ρ r L := by
  have hp := place_sourced hS scope
  have hJ : (rangesTestJob (X' := Y) Xs N Pl entry groups first).p = piKRFull := hp
  have hpl : (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.place = rngPlace := by
    rw [hJ]
    exact place_KR
  obtain ⟨-, er, -, -, ec⟩ := AtPublicFiles.AtFiles.five_sourced hS scope
  have hc : (msgJob (W := Local W₀ Rc Xi Unit) (X := Y) entry Xs.Y.k.oneTime pieces groups first'
      rideMsg).P.codes = msgFull.codes := ec
  have hs : (msgJob (W := Local W₀ Rc Xi Unit) (X := Y) entry Xs.Y.k.oneTime pieces groups first'
      rideMsg).P.sent = msgFull.sent := by
    rw [msgFull_sent, ← er]
    exact AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _
  obtain ⟨b₀, bS, tS, hcut, hbp, hb2, hb0⟩ := msg_cut scope hS.named
  obtain ⟨f1, f2, f3⟩ := tree_facts_at hc hs
  have f4 := tree_facts_full.2.2.2
  obtain ⟨g0, g1, g2⟩ := book_rng_at hK hc hs
  refine onAtRun_ranges scope hS T hρ hR hrun entry groups first L (hplace.trans hpl.symm) hrow hOn
    (by rw [hpl]; exact hg) (by rw [hpl]; exact g2)
    (msgJob (X := Y) entry Xs.Y.k.oneTime pieces groups first' rideMsg) rfl rfl (fun _ _ => rfl)
    [b₀] bS tS hcut (fun h => by rw [h] at hb2; cases hb2) (by rw [hbp]; exact hgS)
    (fun pre' t' blk _ _ => ?_) 1 msgTree f1 f2 hj f3 f4 ?_ (by rw [hplace, hbp]; exact g0)
    (by rw [hplace, hbp]; exact g1) hleft
  · have e2 := two_in_front
    have e3 : ([b₀].flatMap (·.rounds)).length = 2 := by
      simpa using hb0
    omega
  · show OneSenderPub _ rideMsg ((rangesParams N).nums.stages.headD default)
    rw [hp]
    exact oneSenderPub_congr hc hs one_sender_full

end Join

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.k1CutFits_congr
#print axioms ProofFile.Honest.K12.Sim2.one_sender_full
#print axioms ProofFile.Honest.K12.Sim2.book_rng_full
#print axioms ProofFile.Honest.K12.Sim2.oneSenderPub_congr
#print axioms ProofFile.Honest.K12.Sim2.book_rng_at
#print axioms ProofFile.Honest.K12.Sim2.tree_facts_at
#print axioms ProofFile.Honest.K12.Sim2.msg_cut
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_ranges_book
