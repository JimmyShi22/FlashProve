-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15D.lean: WHAT THE COMPOSITION OF THE PROXIMITY TEST's LAW ASKS (CoreFacts), AT ROW 1.15 OF THE KEY FILE's TABLES, AT THE TABLES' FILES' FILLING: in the very form in which the claim's half of the row takes it as a premise (hfacts of back_15_at, Johnson/RunOne/Law/K12Back15.lean). One statement with its proof: calls alone. IT PAYS NO FIELD OF THE TABLES.
OBJECT. CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) … (smpK oNo) mem (· = x₁) at every state in front of the test that the tables' promise holds of and that was reached.
USER. Whoever joins row 1.15.
LETTERS. K12Back15.lean's; r: the radii by stage.
PAID INSIDE, against coreFacts_one (K12Facts15C.lean): the seat's accepting run out of the held one · the seat's planOk · the test's own state is made of the chain's state (door_is) · its codes and the one member of the group under test (front15, out of the promise's test on the state's shape) · K1.Tie (tie_six) · the member's entry in the list of six, its main rows.
WHAT STAYS. On the list of rounds: hpl hl joh hfit hc. The caller's two letters: hoNo hmem. Of a reached state: hseed (message 1 bears an OOD sample of its shape) · hm (the plain test on that sample accepts). AND hword: the word off the plain strings is the word as sent.
Limits. That the premises can be met together is not shown. As empty as hword, hseed and hm. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15C
import Johnson.RunOne.Law.K12Facts15A
import Johnson.RunOne.Law.K12Back15
import Johnson.RunOne.Law.RngDoorIs
import Johnson.RunOne.Law.K12Shape15
import Johnson.RunOne.KeyFillSeedAt
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.Law.K12Core15At
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay beginRun_smpStay)
open OnBytes.Maker
open _root_.Run
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows23 (Fk oneAt On₁ fr₁)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open LPFD LPFD.CandLaid
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf johOk)
open Johnson.RunOne.Law.K12Law15At
open Johnson.RunOne.Law.K12Back15 (BK)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {Cells Rec : Type}
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)
  (oNo : Mem → ℕ) (mem : ℕ → Option Mem)
  (rdT : (x : Mem) → ((sigOf csKey x.1.l).om x.2).Msg → Part → ℕ → GE)

/-- **CoreFacts at row 1.15, at the filling, in the form in which the claim's half takes it.** -/
theorem coreFacts_15 (hpl : (descriptionFromSource X N P).planOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (r : Fmt.M1.Stage → ℕ) (joh : johOk (rangesParams N) r = true)
    (hfit : ∀ a rest, (rangesParams N).nums.stages = a :: rest →
      r (sgOf a).st < ((six.get i₁).2 + 1) * 2 ^ ((sgOf a).C.a - aOf csKey (six.get i₁).1))
    (hc : X.Y.k.oneTime.codes = csKey) (hoNo : oNo x₁ = 1) (hmem : mem 1 = some x₁)
    (hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y)
    (hm : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ o, a.2.d.st.oracles[1]? = some o ∧ o.shape = (six.get i₁).1 ∧
      ∀ m : Seat1, m.sh = (six.get i₁).1 → m.id = 1 → H2K.First.ok (sampleL csKey m o) = true)
    (nl : ℕ → ℕ) (rd : ℕ → ℕ)
    (hword : ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      ∀ a' rest G0 Ly D, Fixes (rangesParams N) t a' rest G0 Ly D → ∀ j : Fin D.mems.length,
        HEq (strOf csKey (D.mems.get j).sh (six.get i₁).2 (layOf (D.mems.get j))
            (W0 (FR DK) (nuOf (rangesParams N) nl t) D.book a.2 (D.mems.get j).t).1
            (W0 (FR DK) (nuOf (rangesParams N) nl t) D.book a.2 (D.mems.get j).t).2)
          (VerifiableInference.Desc.Sound.wordsOf (Fk X N P) csKey x₁.1.l x₁.1.seat (strsOf (FR DK) a.2) x₁.2)) :
    ∀ (a : (Xi × FirstState) × (FR DK).E.Str) (t : T12),
      (On₁ X N P (DK.at frS.P.T.a) (BK X decT recOf) atSix (RK tab) coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) (fun s => r s.st) rd) (t, a.2) →
      ∀ rs gs b, (held (Johnson.RunOne.Sound.bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b →
      CoreFacts csKey (Fk X N P) (FR DK) (rangesParams N) (nuOf (rangesParams N) nl t) (fun s => r s.st) (smpK oNo) mem (· = x₁) t a.2 a.1 (strsOf (FR DK) a.2) := by
  intro a t hon hh ht hq rs gs b hd
  have hn2 : n₁ (oneAt X) = 2 := hl
  obtain ⟨h15n, _, _, _⟩ := hon.elim (fun hx => (hx rfl).elim) id
  have h15 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 a.1.2 = true := hn2 ▸ h15n
  have hy : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide a.1.2 rs gs = .ok b.2 :=
    (held_decide _ a.1 rs gs b hd).2
  obtain ⟨_, _, hcod, _, ⟨G, hG, hone⟩, _⟩ := K12Shape15.front15 h15
  have hw := hword a t hon hh ht
  obtain rfl := RngAtKeyD.door_is _ _ _ _ ht
  exact K12Facts15.coreFacts_one csKey (Fk X N P) (FR DK) _ r rd oNo (fun a : Xi × FirstState => a.2.d.st) mem a.2 a.1 _
    (RngAtKeyD.recD a.1.2) x₁ (six.get i₁).1 (six.get i₁).2 1 joh (K12Facts15.plan_of X N P hpl) hfit hy ht hq
    (hcod.trans hc) (fun G0 h0 => by obtain rfl := Option.some.inj (hG.symm.trans h0); exact hone)
    (hseed a.1 hh) (tie_six i₁) (hm a.1 hh) (by decide) (by decide) rfl hoNo rfl hmem hw

end

end Johnson.RunOne.Law.K12Core15At

#print axioms Johnson.RunOne.Law.K12Core15At.coreFacts_15
