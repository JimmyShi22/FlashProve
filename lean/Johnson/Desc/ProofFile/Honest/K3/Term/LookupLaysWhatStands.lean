-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupLaysWhatStands.lean: the kind "lookup" (K3): at the first
chain's thread of `lettersHead` (Honest/Thread/FirstHead.lean) the member at each of the fifty
lookups lays every rider's clause that follows from "what the lookup has heard stands for some
rounds" (`StandsHere`, Honest/K3/Law/Thread/LaysStands.lean), under the library's hypothesis alone.

What is shown.
  `ownPlanTestGivesTheHearingsTest`, `wholePlanTestGivesTheHearingsTest`,
  `statedPlanTestGivesTheHearingsTest`: where a lookup's sub-protocol passes its test on the plan,
    the library's test `fitsVia` (Johnson/Desc/First/Look/Via/Via.lean) accepts the place's public
    parameters. The test on the plan has `fitsVia` as a conjunct; `theOwn_plan`, `theWhole_plan` and
    `theStated_plan` (Honest/K3/Law/PlanOkGives.lean) keep only its first half.
  `lookupHearingsTestHolds`: so at every link below 25 and either sort, at the public structure's own
    place.
  `lookupPromiseHoldsInFront`: from the thread's invariant in front of a lookup, the lookup's promise
    in front holds (`k3OnIn`).
  `lookupLaysWhatStands`: `LaysAt` at the lookup's border, at every number `standsAtNumber` and every
    clause that follows from `StandsHere` at the place's first slot.

Hypotheses that remain. `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`. Every
letter of `lettersHead` but "keeps" is a variable; "keeps" is `kpBy f` at a variable f. l < 25.
`clauseFollowsFromStanding`: an implication on states alone.

Limits. Implications. Nothing here shows that the invariant or a step holds at any run. That the
clause stays past a later member is not shown here. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysStands
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysNextLight
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.KeepsThread
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanOkGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain FileDescription Place Strs KindName)
open VerifiableInference.Desc.First (Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3 (pieceAt theOwn theWhole theStated k3OnIn)
open VerifiableInference.Desc.K3.Law (fitsVia)
open VerifiableInference.Desc.Sound (mgAll mgBase mgAll_more_closed linksFull MsgT)
open VerifiableInference.Desc.Sound.MgAt (pieceOf borderOf k3_open_calls k3_open_digits)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The test on the plan holds the hearing's test -/

theorem ownPlanTestGivesTheHearingsTest {Cl : Type} (claim : OnBytes.Model.Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theOwn claim runs X codes shape a = some b)
    (hp : b.planOk = true) :
    ∃ i d p, a.link = some i ∧ a.piece = pieceAt X i d ∧ placeAt X i d = some p ∧
      fitsVia p = true := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hpc
      obtain ⟨p, hpl, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have hp' : ((VerifiableInference.Desc.K3.planOk p laid
          ([] : List (VerifiableInference.Desc.First.Look.Guest FS Cl)) &&
          VerifiableInference.Desc.K3.Law.fitsVia p) && key) = true := by
        cases runs <;> exact hp
      simp only [Bool.and_eq_true] at hp'
      exact ⟨i, digits, p, hi, by simpa using hpc, hpl, hp'.1.2⟩

theorem wholePlanTestGivesTheHearingsTest {Cl : Type} (claim : OnBytes.Model.Aff → Cl)
    (runs : Bool) (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes)
    (shape : OnBytes.Params.ReqShape) (a : Place) (b : Block FS Cl)
    (h : theWhole claim runs X codes shape a = some b) (hp : b.planOk = true) :
    ∃ i d p, a.link = some i ∧ a.piece = pieceAt X i d ∧ placeAt X i d = some p ∧
      fitsVia p = true := by
  unfold theWhole at h
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  split at hp
  · have hp₀ : (b₀.planOk && true) = true := hp
    exact ownPlanTestGivesTheHearingsTest claim runs X codes shape a b₀ hb (by simpa using hp₀)
  · exact ownPlanTestGivesTheHearingsTest claim runs X codes shape a b₀ hb hp

theorem statedPlanTestGivesTheHearingsTest {Cl : Type} (claim : OnBytes.Model.Aff → Cl)
    (readers : Nat → Option (VerifiableInference.Desc.K3.Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theStated claim readers X codes shape a = some b)
    (hp : b.planOk = true) :
    ∃ i d p, a.link = some i ∧ a.piece = pieceAt X i d ∧ placeAt X i d = some p ∧
      fitsVia p = true := by
  unfold theStated at h
  obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain rfl := Option.some.inj h
    exact wholePlanTestGivesTheHearingsTest claim true X codes shape a _ hb hp
  · split at h
    · obtain rfl := Option.some.inj h
      exact wholePlanTestGivesTheHearingsTest claim true X codes shape a _ hb hp
    · split at h
      · obtain rfl := Option.some.inj h
        exact wholePlanTestGivesTheHearingsTest claim true X codes shape a _ hb hp
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact wholePlanTestGivesTheHearingsTest claim true X codes shape a b₀ hb hp

/-! ## 2 Under the library's hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The piece of the lookup's written place is the public structure's. -/
theorem lookupPieceIsThePublicOne (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat)
    (d : Bool) : (IM.k3Place l d).piece = pieceAt Zp.p.X l d := by
  cases d with
  | false => exact P5J.k03_pieceAt h.toAtMg l
  | true => exact P5J.k03_pieceAt_dig h.toAtMg l

/-- **At every link below 25 and either sort the hearing's test accepts the place's public
parameters.** -/
theorem lookupHearingsTestHolds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (linkBelow : l < 25) (d : Bool) : ∃ p, placeAt Zp.p.X l d = some p ∧ fitsVia p = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', hb', ep, hpk, -⟩ := lot_spot_head h.scope h.reads O h.laid.planOk l linkBelow d
  unfold K3Lot.hear at hb'
  obtain ⟨y, _, hst⟩ := List.mem_filterMap.1 hb'
  have hpy : y.2.2 = IM.k3Place l d := (theStated_place _ _ _ _ _ _ b' hst).symm.trans ep
  obtain ⟨i, d', p, k1, k2, k3, k4⟩ := statedPlanTestGivesTheHearingsTest _ _ _ _ _ _ b' hst hpk
  rw [hpy] at k1 k2
  obtain rfl : l = i := Option.some.inj k1
  obtain rfl : d = d' := pieceAt_inj _ _ _ _ ((lookupPieceIsThePublicOne h l d).symm.trans k2)
  exact ⟨p, k3, k4⟩

end

/-! ## 3 At the thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- From the invariant in front of a lookup, the lookup's promise in front. -/
theorem lookupPromiseHoldsInFront {l : Nat} (linkBelow : l < 25) (d : Bool)
    {p : VerifiableInference.Desc.First.Look.P} (placeIs : placeAt Zp.p.X l d = some p)
    {k : Coins Bk} {st : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (invariantInFront : Thr (LK).thread (borderOf l d) k st m E) : k3OnIn p st = true := by
  have hq : Pub.lookIn l (pieceAt Zp.p.X l d) ∈
      ((pubSets (LK).MgP.more (LK).links (LK).ps)[borderOf l d]?).getD [] := by
    show Pub.lookIn l (pieceAt Zp.p.X l d) ∈
      ((pubSets (mgAll h.𝔇 mgBase).more linksFull (flatPlacesOf linksFull true))[borderOf l
        d]?).getD []
    have e : pieceAt Zp.p.X l d = pieceOf l d := (lookupPieceIsThePublicOne h l d).symm
    rw [mgAll_more_closed h.𝔇 mgBase rfl, e]
    cases d with
    | false => exact (k3_open_calls linkBelow).1
    | true => exact (k3_open_digits linkBelow).2.1
  exact onIn_thr (LK) (VerifiableInference.OnPublicFiles.k3At_mgAll h.𝔇 mgBase) placeIs hq
    invariantInFront

/-- **The lookup's member lays every clause that follows from "what the lookup has heard stands for
some rounds".** Conditional on what this file's head lists. -/
theorem lookupLaysWhatStands {l : Nat} (linkBelow : l < 25) (d : Bool) (standsAtNumber : Nat)
    (c : RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)
    (clauseFollowsFromStanding : ∀ p, placeAt Zp.p.X l d = some p → ∀ v t,
      StandsHere d standsAtNumber p.first t → c.prop (borderOf l d + 1) v t) :
    LaysAt (LK).thread (borderOf l d) c := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l linkBelow d
  obtain ⟨s, hs, e1, e2, e3, -⟩ := site_digits_paid h l linkBelow d
  have hps := site_p_is hs
  rw [e1, e2] at hps
  obtain ⟨p, hp1, hfv⟩ := lookupHearingsTestHolds h linkBelow d
  obtain rfl : s.p = p := Option.some.inj (hps.symm.trans hp1)
  exact lays_stands (LK).thread _ _ _ _ Fd base A B O hs hM.inLot (hp.trans e3.symm) hM.mem hM.place
    hM.plan
    (fun k st m E hA => lookupPromiseHoldsInFront h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
      linkBelow d hps hA)
    hfv standsAtNumber c (fun v t hst => clauseFollowsFromStanding s.p hps v t (e2 ▸ hst))

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.ownPlanTestGivesTheHearingsTest
#print axioms ProofFile.Honest.K3.Term.wholePlanTestGivesTheHearingsTest
#print axioms ProofFile.Honest.K3.Term.statedPlanTestGivesTheHearingsTest
#print axioms ProofFile.Honest.K3.Term.lookupPieceIsThePublicOne
#print axioms ProofFile.Honest.K3.Term.lookupHearingsTestHolds
#print axioms ProofFile.Honest.K3.Term.lookupPromiseHoldsInFront
#print axioms ProofFile.Honest.K3.Term.lookupLaysWhatStands
