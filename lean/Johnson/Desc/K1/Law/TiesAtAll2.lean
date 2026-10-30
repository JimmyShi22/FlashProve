-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TiesAtAll2.lean: MORE PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 AT ITS TWO
OTHER PLACES (the first segment's opening, number 2; W's commitment, number 356), AT THE
CLOSED CONSTANT, each in the premise's own type: the second batch beside TiesAtAll.lean (this
folder), at the same letters and under the same four premises hA, O, hP1, hP2. Definitions: none.
Statements with their proofs.

  `radii_written`, `radii_reject`   BY LEAN's KERNEL (`decide +kernel`; maxRecDepth 1000000 for
      their elaboration alone): the two tests on the radii, `condPort` and `powB` at 128, accept at
      the written parameters of the two places, at the radii of the written list of rounds with
      each round's error bound (`radRec 0`, `radRec 81`: the first chain's sendings number 0 and
      81); the negative test: at a radius of 10,000,000 the first rejects, at 200 bits the second
  `G_hCond` `G_hpow` `W_hCond` `W_hpow` (W_rad := `radRec 81 (parWZ Zp wMsgFull)`)
  `G_hreq` `G_hdig` `G_hhead`   calls of Johnson/Desc/AtSeats/ConstrLettersAtAll.lean and
      ReplyLeft.lean
  `W_hplan` `G_hplan`   the two sub-protocols' own tests on their parameters accept: off hOk,
      through the maker's opening (the steps of at_356 and at_first,
      Johnson/Desc/AtSeats/CountsAtFour.lean, kept one conjunct longer)
  `G_hY`   a G_Y with G_hY and G_hYF, off G_hX
  `G_hdg`   at piece 2 of segment 0 stands the lookup on the calls (G_dg := false): in scope the
      output head's segment is number 24, not 0
each with the ending _atAll.

What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. That
`radRec 81`'s radii are those of the constant's list of sampled oracle messages. W_HP, G_HP, G_hPlG,
W_hFacts, G_hFacts: not here. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PowB
import Johnson.Desc.AtSeats.ConstrLettersAtAll
import Johnson.Desc.AtSeats.ReplyLeft
import Johnson.IMR.SealSeat
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.First.Look.K3Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription Strs)
open VerifiableInference.Desc.Sound (mgAll mgBase)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (wMsgFull StepG)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.PlanWritten (madePinnedAt cutIs)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Desc.First.Walk (LayPar)
open ProofFile (Cl)
open IM (Open)

set_option maxRecDepth 1000000 in
theorem radii_written : condPort parGF (radRec 0 parGF) = true ∧
    powB parGF (radRec 0 parGF) 128 = true ∧ condPort parWF (radRec 81 parWF) = true ∧
    powB parWF (radRec 81 parWF) 128 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem radii_reject : condPort parGF (fun _ => 10000000) = false ∧
    powB parGF (radRec 0 parGF) 200 = false ∧ condPort parWF (fun _ => 10000000) = false ∧
    powB parWF (radRec 81 parWF) 200 = false := by
  decide +kernel

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

/-! ## The constraints' three letters -/

theorem G_hreq_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    ∀ x x' : ProofFile.InstPub × S, x'.1 = x.1 → hA.𝔇.H.req x' = hA.𝔇.H.req x :=
  fun x x' h => HashBuild.req_atAll hA x x' h

theorem G_hdig_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    ∀ (x x' : ProofFile.InstPub × S) (y y' : Strs) w k, x'.1 = x.1 → y'.cell = y.cell →
      hA.𝔇.digitsPart k x' y' w → hA.𝔇.digitsPart k x y w :=
  fun x x' y y' w k _ _ h0 => HashBuild.dig_atAll hA k x x' y y' w h0

theorem G_hhead_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) (G₀ : ProofFile.Ground)
    (G_X : LayPar) :
    ∀ (nm : String) (x x' : ProofFile.InstPub × S) (y y' : Strs) w p i,
      StepG Cl G₀.first (gpOf Zp) nm G_X (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links)
        Zp.first.lin.kCol x x' →
      (mgAll hA.𝔇 mgBase).pub .unheard x = true → y'.cell = y.cell →
      hA.𝔇.headPart p i x' y' w → hA.𝔇.headPart p i x y w :=
  fun _ x x' y y' w p i h _ _ h0 =>
    HashBuild.head_atAll hA p i x x' y y' w h.1 (reply_G x x' h) h0

/-- At piece 2 of segment 0 stands the lookup on the calls. -/
theorem G_hdg_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    First.Look.k3SortAt hA.𝔇.pubD.d3.X 0 2 = some false := by
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  show First.Look.k3SortAt (P5J.At.X Zp) 0 2 = some false
  unfold First.Look.k3SortAt VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
  rw [p4, ng] <;> rfl

/-! ## Under the opening -/

variable (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
include hA O

/-- The opening's own test on its parameters accepts, under every name. -/
theorem G_hplan_atAll (G_X : LayPar) : ∀ nm : String,
    (openingZero Bs.G₀.first (gpOf Zp) nm G_X
      (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links) Zp.first.lin.kCol :
        Block S Cl).planOk = true := by
  intro nm
  have hok : ∀ b ∈ cF.blocksInOrder, b.planOk = true := fun b hb => (hOk_atAll hA O b hb).1
  obtain ⟨Lk, b, e1, e2, h⟩ := IM.k1_first_of hA.scope hA.reads O
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hA.scope hA.reads O (by omega) 0] at h5
  have hp := hok b (List.mem_of_getElem? h5)
  have hp1 : (planOkOwn (firstPar Bs.G₀.first (gpOf Zp)) &&
      firstPlanOk Bs.G₀.first (gpOf Zp).samples) = true := by
    rcases h with h | ⟨fb, _, h⟩
    · rw [IM.alone_planOk h] at hp
      exact (IM.retype_planOk _ hp).1
    · have ep : b.planOk =
          (((firstSegmentOpening Bs.G₀.first (gpOf Zp) : Block S Unit).retype : Block S Cl).planOk &&
            (fb.retype : Block S Cl).planOk) := congrArg (·.planOk) h
      rw [ep] at hp
      exact (IM.retype_planOk _ (Bool.and_eq_true_iff.1 hp).1).1
  show ((planOkOwn (firstPar Bs.G₀.first (gpOf Zp)) &&
      firstPlanOk Bs.G₀.first (gpOf Zp).samples) && true) = true
  rw [hp1]
  rfl

/-- A G_Y with G_hY and G_hYF, off G_hX. -/
theorem G_hY_atAll (G_X : LayPar)
    (hX : Johnson.Desc.First.Walk.Seat.zeroAt Zp.p.built.links Zp.p.X = some G_X) :
    ∃ G_Y, hA.𝔇.built[0]? = some G_Y ∧ G_Y.Fp = G_X.X.Fp := by
  unfold Johnson.Desc.First.Walk.Seat.zeroAt at hX
  obtain ⟨Y, hY, hX⟩ := Option.bind_eq_some_iff.1 hX
  refine ⟨Y, hY, ?_⟩
  split at hX
  · cases hX
  · obtain ⟨_, _, hX⟩ := Option.bind_eq_some_iff.1 hX
    obtain ⟨hp, _, hX⟩ := Option.bind_eq_some_iff.1 hX
    obtain rfl := Option.some.inj hX
    rfl

variable (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hP1

theorem G_hCond_atAll : condPort (firstPar Bs.G₀.first (gpOf Zp))
    (radRec 0 (firstPar Bs.G₀.first (gpOf Zp))) = true := by
  rw [eG_atAll hA O hP1]
  exact radii_written.1

theorem G_hpow_atAll : powB (firstPar Bs.G₀.first (gpOf Zp))
    (radRec 0 (firstPar Bs.G₀.first (gpOf Zp))) 128 = true := by
  rw [eG_atAll hA O hP1]
  exact radii_written.2.1

theorem W_hCond_atAll :
    condPort (parWZ Zp wMsgFull) (radRec 81 (parWZ Zp wMsgFull)) = true := by
  rw [eW_atAll hA O hP1]
  exact radii_written.2.2.1

theorem W_hpow_atAll :
    powB (parWZ Zp wMsgFull) (radRec 81 (parWZ Zp wMsgFull)) 128 = true := by
  rw [eW_atAll hA O hP1]
  exact radii_written.2.2.2

/-- The own test on its parameters of W's commitment, with the own group and (Eval) behind it,
accepts. -/
theorem W_hplan_atAll :
    (atM4 (Cl := Cl) (whereOf Zp) (sendAtS (parWZ Zp wMsgFull))).planOk = true := by
  have hok : ∀ b ∈ cF.blocksInOrder, b.planOk = true := fun b hb => (hOk_atAll hA O b hb).1
  obtain ⟨-, -, -, b, b', w, hb, -, hw, rfl, hl⟩ := IM.back_of O
  unfold K13.wBlock wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain rfl : msg = wMsgFull := Option.some.inj (hm.symm.trans (W_hm_atAll hA O hP1))
  have h5 := (IM.back_numbers hA.scope hA.reads O).1 3 b hb
  have hp := hok _ (List.mem_of_getElem? h5)
  have hp2 : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := hp
  have hp3 := (Bool.and_eq_true_iff.1 hp2).1
  rw [IM.alone_planOk hl] at hp3
  have hp4 := (IM.retype_planOk _ hp3).1
  exact hp4

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.radii_written
#print axioms VerifiableInference.Desc.K1.radii_reject
#print axioms VerifiableInference.Desc.K1.G_hreq_atAll
#print axioms VerifiableInference.Desc.K1.G_hdig_atAll
#print axioms VerifiableInference.Desc.K1.G_hhead_atAll
#print axioms VerifiableInference.Desc.K1.G_hdg_atAll
#print axioms VerifiableInference.Desc.K1.G_hplan_atAll
#print axioms VerifiableInference.Desc.K1.G_hY_atAll
#print axioms VerifiableInference.Desc.K1.G_hCond_atAll
#print axioms VerifiableInference.Desc.K1.G_hpow_atAll
#print axioms VerifiableInference.Desc.K1.W_hCond_atAll
#print axioms VerifiableInference.Desc.K1.W_hpow_atAll
#print axioms VerifiableInference.Desc.K1.W_hplan_atAll
