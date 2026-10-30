-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormAtt.lean: K9's FALL ON THE FREE SLOTS, AT THE TWELVE ATTENTION SEGMENTS, IN THE
FORM OF THE FRAME's PREMISE. The bound on falls of the smallness test (`falls_five_by_owner`,
Johnson/P1K8R/FallsAtLists.lean, which does not lie beneath this file) asks of K9
the premise hF9: a `FallDebt` for `quietFall` wherever it is counted, at the letter qF. HERE: THAT PREMISE's TEXT AT l
:= 2 g + 1 IS THE END, AND IT IS EXCHANGED, NOT PAID: for hPW (the gate's condition gives what our bound asks of the
state in front of the batching) and hq (our bound is at most qF there). After the feed-forward layers'
`k4_fallDebt_form` (its Law/FallForm.lean, known here by its letters alone). AT THE OTHER THIRTEEN SEGMENTS NOTHING IS
HAD. Statements and proofs; no definition; no goal is stated.
  `quietFall_place_att`   under the head, g < 12: the fall's place is the place behind that segment's batching in that
      file's spelling (`K8.quietPlace`): by `piece_at_seat` (Honest/K9/KeepsAtPlace.lean), the library's
      `IM.k9Where_fields`, `sub_odd` (Honest/K9/SeatTied.lean)
  **`k9_fallDebt_form_att`**   under the head · cut : the first chain's list is pre₁ ++ [e₁] · u₀: any `HTailF2`: the
      end does not read it · hPW: at the batching of 2 g + 1, PW b fr s' gives `HeldLive`, the lookups' `Clause` at what
      each of the two lookups has heard, and "reached by the wrapped blocks" · hq. THE END: hF9's text, with fs for the
      list of falls and PW b for the gate's condition. HOW: K9's seat by `seated_at_head` (Honest/K9/AtHead.lean) · the
      written cut and the distinct places by the frame's `file_head`, `places_nodup` · that house's `counted_at_own`
      (where the fall is counted, b is the batching) · `batch_rounds_are`, `one_of_fits` (the data are one round's, of
      K9's entry) · `drop_split` (the list behind) · our `k9_fallDebt_att_list_blocks` (Honest/K9/FallDebtAttList.lean)
      · `fallDebt_mono`; the attention plan by the library's `H2K5.Door.planAt_all`, the two lookups' places by its
      `P1K9.bothPlaces_at_head`
WHERE IT WOULD BE TRUE FOR NOTHING. Where PW b holds of no state; where the fall is counted at no member. Whoever calls
it lays qF at or above our bound, and the right side of the bound on falls grows with it. hq IS NOT THAT THEOREM's hqF
(the fall's stated share is at most qF): our bound carries `kapSl 128 ^ 3`, the stated share does not: qF is laid at or
above both. NO NUMBER IS EVALUATED; nothing says that any sum is below 1. The letter notGood in the fall's stated share
has no payer.
WHAT IS NOT CLAIMED. hPW at any gate's condition. BY A READER's READING: at PW := that house's `PWith Z c Bs Pr` the
fourth conjunct is `PLast`'s first field `WrapEnd` (Johnson/P1K8R/CountedAtRch.lean) at 2 g + 1; the first three the
caller lays into Pr and pays in that theorem's hPr by `attClauses_handed` (Johnson/P1K8R/ClausesAtFrame.lean), which
ends in them to the letter: THE FIRST OF THESE TWO JOINS IS Honest/K9/FallFormAttWith.lean's; THE SECOND IS NOT TYPED.
Called by that file alone. At the full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 531 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallDebtAttList
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtPlace
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile
import Johnson.P1K8R.CountedAtOwn
import Johnson.P1K8R.LastAtAsks
import Johnson.P1K9R.AreadyClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt KindFits repsAt fallSeat)
open Iop
open H2K5.Honest (HeldLive)
open VerifiableInference.Desc.First.Look (placeAt)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- The place of K9's fall at an attention segment is the place behind that segment's batching, in the smallness
test's house's spelling. -/
theorem quietFall_place_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {p : Desc.K9.Where} (hp : IM.k9At Zp (2 * g + 1) = some p) (n top : ℕ) (ng : Odds) :
    (quietFall p n top ng).place =
      ProofFile.Honest.K8.quietPlace (2 * g + 1) (if 2 * g + 1 = 24 then 1 else 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e1 := piece_at_seat h.scope h.reads O (by omega : 2 * g + 1 < 25) hp
  obtain ⟨e2, e3, -⟩ := IM.k9Where_fields hp
  rw [sub_odd g hg] at e1
  have e0 : ((2 * g + 1 == 0) : Bool) = false := by simp
  rw [e0] at e1
  have e4 : p.piece = 8 := e1
  rw [if_neg (by omega)]
  show (⟨p.chain, some p.link, p.piece + 1, .frame⟩ : Place) = ⟨1, some (2 * g + 1), 9 + 2 * 0, .frame⟩
  rw [e2, e3, e4]

/-- **THE FRAME's PREMISE ON K9's FALL, AT THE TWELVE ATTENTION SEGMENTS, EXCHANGED**: its end is that premise's text at
l := 2 g + 1, with fs for the list of falls and PW b for the gate's condition. -/
theorem k9_fallDebt_form_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (u₀ : HTailF2)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (PW : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPW : ∀ g, g < 12 → ∀ b, cF.blocksInOrder[14 * (2 * g + 1) + 9]? = some b → ∀ a pC pD,
      (P5J.At.X Zp).A[g]? = some a → placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC →
      placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD → ∀ fr s', PW b fr s' →
      HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧ Clause pD (s'.tl?.bind (·.heard)) ∧
        ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * (2 * g + 1) + 9) (z, s'))
    (hq : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g + 1) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g p u, g < 12 → IM.k9At Zp (2 * g + 1) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1))) 0 b
        (b' :: B ++ [e₁]) dsb [] (PW b)
        (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)))) := by
  intro A b b' B e _ hn g p u hg hp hu hmem dsb hk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, hpl, hcut⟩ := ProofFile.Honest.file_head h.toAtMg
  have hl : 2 * g + 1 < 25 := by omega
  have hall : cF.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e]
    simp
  have hlen : A.length = 14 * (2 * g + 1) + (if 2 * g + 1 = 24 then 11 else 9) :=
    P1K8.counted_at_own h.scope h.reads O hcut (ProofFile.Honest.places_nodup hpl).1 hall hn hmem hl
      (Or.inr (quietFall_place_att h hg hp _ _ _))
  rw [if_neg (by omega)] at hlen
  have hb : cF.blocksInOrder[14 * (2 * g + 1) + 9]? = some b := by
    rw [← hlen, hall]
    simp
  -- the seat, and the block
  obtain ⟨Lk, p', w, Sd⟩ := seated_at_head h (2 * g + 1) hl
  rw [if_neg (by omega)] at Sd
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans Sd.numbers)
  have hw : w = u := Option.some.inj (Sd.tested.symm.trans hu)
  subst hw
  have hbat : b = Lk.batch (claimsInBy Lk.each Lk.hear Lk.order) := by
    have e9 : cF.blocksInOrder[14 * (2 * g + 1) + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) :=
      Sd.batching
    exact Option.some.inj (hb.symm.trans e9)
  -- the data of the one round
  have hr : b.rounds = [{ entry := Desc.K9.entry p }] :=
    P1K8.batch_rounds_are h.scope h.reads O hl (by rw [if_neg (by omega)]; exact hb) hp
  rw [hr] at hk
  obtain ⟨d, rfl, he, h5, h6⟩ := P1K8.one_of_fits hk
  -- the list behind
  have htail : cF.blocksInOrder.drop (14 * (2 * g + 1) + 9 + 1) = b' :: B ++ [e₁] := by
    rw [← hlen]
    exact P1K8.drop_split (by rw [cut, e])
  -- the public readings
  obtain ⟨a, ha⟩ := H2K5.Door.planAt_all h hg
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h (2 * g + 1) hl
  have K := k9_fallDebt_att_list_blocks h hg Sd u₀ ha hC hD d he h5 h6 (notGood (2 * g + 1)) 0 (PW b)
    (ProofFile.startS Zp) (hPW g hg b hb a pC pD ha hC hD)
  rw [htail, ← hbat] at K
  exact P1K8.fallDebt_mono K (fun _ _ hh => hh) (hq g hg b p w hp hu)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.quietFall_place_att
#print axioms ProofFile.Honest.K9.k9_fallDebt_form_att
