-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Toy.lean: A TOY FOR THE ROW K06_law: ALL NINE PREMISES OF THE OUTPUT HEAD's ROW AT THE REAL SEAT (RowPriceAtSeatStatement, Law/RowRides.lean, from which rowRides
is had) HOLD TOGETHER AT ONE VALUE: so they do not contradict each other, and Lean applies the law to it (k06Toy_spends).
WHAT IT IS NOT, FIRST. NOT A MEMBER AT THE RELEASE. ALL OF IT IS MADE IN LEAN; NO FILE IS READ; NO RUN OF ANY PROGRAM STANDS BEHIND IT.
 1. THE ROUNDS are built by the sender beside the text (Law/HeadSends.lean: head_sendsC), not sent by the prover's program; EVERY DRAW IS THE ELEMENT 1 (the sender serves all draws; the toy
    takes these).
 2. EVERY POSITION BELOW 1023 IS CHECKED AND HAS A COST (r = 0, e = 1023: K06Toy.costed_K), so the policy's four forms do ask something of the
    cells: BUT THE HEAD's WEIGHTS ARE ALL 0: every logit is 0, every cost is the lift 2^sh = 256 = theta alone; nothing is over; cap = 0; the mean's and the cap's slacks are 0. Nothing on a cost that a model's
    logits make, on a clip that bites, or on the table of exponentials (the cells answer to a table of two values, which is no premise of the row).
 3. THE CELLS are those of Law/CellsWithCosts.lean (cells_with_costs: withCosts over the honest cells of THE STREAM OF ZEROS); all tokens of the request are 0, and so is the reply.
 4. THE RECORD sK IS LAID BY HAND (Law/K06ToyRecord.lean): a blank one; what the lookup heard is made up; THE LEDGER IS FRESH (1000 free numbers, nothing laid in front: no lookup's, no layer's scalar). It is
    a record of no fold.
 5. hR is the stored full-size example's head's shape BY AN EVALUATION ALONE (Law/K07MemberAt.lean's head); iU3 := 0, work := 0, link 0.
 6. IT IS AT Head.blockAt hR 0 0 0. K06_law's line (RowRidesStatement) speaks of Head.blockOf W l at a public record W: NO W IS EXHIBITED IN LEAN.
 7. Opened is met with the reads READ AS THE STATED SUMS OF THE CELLS (as the row has it), not at the seat's places. "join", the keys' ranges, planes: not in the row's premises, not here.
 8. c AND mask ARE TIED TO NOTHING IN FRONT OF THE DRAWS, as in the row.
WHAT IT IS.
  K06Toy        there are cells c such that FOR EVERY MASK ROW there are a record behind, rounds and columns with: the block's decision goes on from sK · the ledger in front is WellLaid · the tests on the
                plan [BY decide AT THE STORED EXAMPLE's NUMBERS] · 0 < d · the test on the request · the token is below V · the rounds' words are below the prime · no draw is bad under K6's rule cut at the
                tight ceiling · Opened: all 35 forms worth 0 and the claim on the weights true at the record behind.
  k06Toy        it holds. k06Toy_spends: Came.rowPriceAtSeat applies to it with nothing else in hand: ClosedWhole at the record behind, for every mask row.
  SentShaped · sent_at_record · k06Toy_of_sent   the joints: what the sender hands at the record's letters; from there to the nine.
WHAT IT IS BUILT OF: from other files: the sender, NormTruth, the cells · the row, row_true, ruleK6T_of_row, given_ok, the letters' laws · made for it: Opened at the truth (Law/OpenedHead | OpenedNorm |
OpenedAll | OpenedSent), seatBack_at (Law/HeardBack.lean), the rounds' shape (Law/TapeShape.lean), the record.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06ToyParts
import Johnson.Desc.Kinds.Law.K06ToyRecord
import Johnson.Desc.Kinds.Law.TapeShape
import Johnson.Desc.Kinds.Law.Takes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Tape (tapeT)
open K07Real (hR pR)
open K06Toy (sK FK)

/-- What an honest sending of all the block's rounds hands, every draw the element 1. -/
def SentShaped [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) : Prop :=
  ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
    Canonical rs ∧ hear F rs = some (H, G, []) ∧ Sound.NoBad (Came.rowRuleC c mask F) rs ∧
    WellLaid G ∧
    (let _ : Norm.Heard := H.1
     let _ : FinalNorm.Heard := H.2.1
     let _ : Heard := H.2.2
     let _ : FinalNorm.Reads := normReadsAtCells c
     let _ : Reads := readsAt c.toCells
     WeightTrue c.toCells G mask noEnt ∧
      ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) ∧
    ShapedAs [oneE] rs rounds

/-- **ALL PREMISES OF K6's ROW AT THE REAL SEAT (RowPriceAtSeatStatement), AT ONE VALUE.** -/
def K06Toy : Prop :=
  ∃ (c : NCells), ∀ (mask : Nat → E), ∃ (s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (blockAt hR 0 0 0).decide sK rs gs = .ok s' ∧ WellLaid ((seatAt hR 0).ledger sK) ∧
    (parOf hR 0).ok = true ∧ hasFeatures (parOf hR 0) ∧
    (parOf hR 0).okStart ((seatAt hR 0).request sK) = true ∧
    (∀ y, Reply.token (seatAt hR 0).toSeat sK = some y → y < (parOf hR 0).sizes.V) ∧
    Canonical rs ∧ Sound.NoBad (ruleK6T (parOf hR 0) (seatAt hR 0) sK c mask) rs ∧
    Opened (parOf hR 0) (seatAt hR 0) s' c mask

/-- The toy's clauses are the law's premises: the law applies to it with nothing else in hand. -/
theorem k06Toy_spends (m : K06Toy) :
    ∃ (c : NCells), ∀ (mask : Nat → E), ∃ (s' : S),
      ClosedWhole (parOf hR 0) (seatAt hR 0) s' c mask := by
  obtain ⟨c, hm⟩ := m
  refine ⟨c, fun mask => ?_⟩
  obtain ⟨s', rs, gs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hm mask
  exact ⟨s', Came.rowPriceAtSeat hR 0 0 0 sK c mask s' rs gs h1 h2 h3 h4 h5 h6 h7 h8 h9⟩

/-- From what the sender hands, at the record's letters, to the toy. -/
theorem k06Toy_of_sent
    (hsend : ∀ (g : Given) (c : NCells) (mask : Nat → E), given pR (seatAt hR 0) sK = .ok g →
      (dataOf c).Holds → HonestHead c.toCells → SentShaped c mask FK) : K06Toy := by
  have hgs := K06Toy.given_K
  cases hg : given pR (seatAt hR 0) sK with
  | error e => rw [hg] at hgs; cases hgs
  | ok g =>
    obtain ⟨z, y, hz, hty, hP, hgeq⟩ := Came.given_ok pR (seatAt hR 0) sK g hg
    -- the cells
    have hy0 : y = 0 := by
      rw [K06Toy.token_K] at hty
      exact (Option.some.inj hty).symm
    subst hy0
    have hcells : ∃ c : NCells, (dataOf c).Holds ∧ HonestHead c.toCells := by
      subst hgeq
      letI : Sizes := pR.sizes
      letI : Policy := pR.policy
      letI : Request := (seatAt hR 0).request sK
      letI : Token := ⟨0⟩
      obtain ⟨c, hH, _, _, _, hl, hm, hc, _⟩ :=
        cells_with_costs (sT := pR.sT) K06Toy.plan_ok K06Toy.start_ok (K06Toy.token_lt 0 hty)
          K06Toy.admits_K
      exact ⟨c, hH, hl, hm, hc⟩
    obtain ⟨c, hH, hC⟩ := hcells
    refine ⟨c, fun mask => ?_⟩
    obtain ⟨rs, H, G, hcan, hhear, hnb, hWG, hopen, hshape⟩ := hsend g c mask hg hH hC
    -- the rounds' shape
    have htape := tape_returns pR.work [oneE]
      (fun x hx => by rw [List.mem_singleton.mp hx]; rfl) rs rounds hshape rounds_plain
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp htape
    have ht' : tapeT { rows := fun e => e.name == "BAT-sigma" } rs
        ((pR.declare rounds).map (·.entry)) = some t := by
      rw [← ht]
      unfold Par.declare headRule
      rw [List.map_map]
      rfl
    -- the layings
    obtain ⟨s1, s2, e1, e2⟩ := K06Toy.lays_K G H
    obtain ⟨w, hd⟩ := decide_returns (fun _ => ()) (seatAt hR 0) 0 4 pR sK s1 s2 rs [] g t H G hg
      ht' hhear e1 e2
    obtain ⟨bL, bH, bG, _⟩ := seatBack_at hR 0 0 sK g rs [] G H w s1 s2 hg K06Toy.wellLaid_K hcan
      hhear e1 e2
    refine ⟨_, rs, [], hd, K06Toy.wellLaid_K, K06Toy.plan_ok,
      K06Toy.has_features, K06Toy.start_ok, K06Toy.token_lt, hcan,
      Came.ruleK6T_of_row pR (seatAt hR 0) sK c _ hg hnb, g, H, bG.trans hg, bH, ?_⟩
    rw [bL]
    exact hopen

/-- At the record's letters the sender's premises hold. -/
theorem sent_at_record (g : Given) (c : NCells) (mask : Nat → E)
    (hg : given pR (seatAt hR 0) sK = .ok g) (hH : (dataOf c).Holds)
    (hC : HonestHead c.toCells) : SentShaped c mask FK := by
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := Came.given_ok pR (seatAt hR 0) sK g hg
  letI : Sizes := pR.sizes
  letI : Policy := pR.policy
  letI : Request := (seatAt hR 0).request sK
  letI : Token := ⟨y⟩
  obtain ⟨hw, hzt, hblock⟩ := letters_of_lookup pR.sT pR.floor z.1 z.2 K06Toy.plan_ok hP
  letI : FinalNorm.In := (fromLookup pR.floor z.1 z.2).norm
  letI : In := (fromLookup pR.floor z.1 z.2).head
  have P := planFacts K06Toy.plan_ok
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hls : ls ≤ lPd := Came.ls_le_lPd K06Toy.has_features hdS
  have hlt : lt = 10 := rfl
  have hlPd : lPd = 13 := by decide
  have szP : zP.size = lt + lPd := by
    unfold zP
    rw [Array.size_append, hzt]
    simp [halves]
  have sPt : (List.replicate lt oneE).toArray.size = lt := by simp
  have hF := K06Toy.fresh_K.less (m := 9 + (Part.MaskedSum.ownSlots
      (callOf 0 (zS (List.replicate lt oneE).toArray) 2).all + 2 +
      (7 + (1 + (Part.MaskedSum.ownSlots (callOf 1 (List.replicate lt oneE).toArray 4).all + 4 +
        (1 + (Part.MaskedSum.ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (Part.MaskedSum.ownSlots (callOf 1 zP 2).all + 2 + 0))))))))) (by
    rw [own_callOf, own_callOf, own_callOf, own_callOf, zS_size _ sPt, sPt, hzt, szP, hlt, hlPd]
    omega)
  obtain ⟨rs, H, G, a1, a2, a3, a4, a5, a6⟩ := sent_opened c mask K06Toy.wellLaid_K hH hC
    K06Toy.start_ok (K06Toy.token_lt y hty) hw hzt hls hdS hblock hF
  exact ⟨rs, H, G, a1, a2, a3, a4, a6, a5⟩

/-- **K06_law's TOY.** -/
theorem k06Toy : K06Toy := k06Toy_of_sent sent_at_record

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Toy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Toy_spends
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06Toy_of_sent
