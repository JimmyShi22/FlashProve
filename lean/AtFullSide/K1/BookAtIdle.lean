-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/BookAtIdle.lean: the shared "sending" (the kind K1): THE BOOK's SIDE AT THE FIFTY SENDERS
THAT LEND NOTHING (each link's reads and digits). In scope, where the gate accepts, the book that the
maker onlineProverFromPublicFiles returns, at any filling, has the written entries rawAheadW
(AtFullSide/K14/RawAheadWritten.lean); and no spending entry of rawAheadW has an owner at a place of
the kind K1 inside a link but the opening's sender. So at each of the fifty the premise on the book of
handIn_at_return (Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean) holds AT THE MAKER's OWN BOOK, at
every order of places. Public data alone: entries, addresses. The definition and the two long evaluations lie
in files of their own (BookAtIdleWants.lean, BookAtIdleSeg.lean); the rest are theorems.

  lendsOk          (BookAtIdleWants.lean) the test on an entry: it spends nothing, or its owner stands at a place of another
                   kind, or outside the links, or is the opening's sender
  wants_lend, seg_lend, short_lend   three evaluations in Lean's kernel: the test accepts the three
                   pieces of rawAheadW; ahead_lend: so it accepts rawAheadW
  lend_bite        the test can fail: at a spending entry whose owner is a link's reads' sender
  ahead_at_return  the returned book's entries are rawAheadW
  later_place      a job behind the opening stands at a place of the kind K1, inside a link, that is
                   not the opening's
  clear_at_later   THE PREMISE AT THE FIFTY, at the returned book

Limits. fresh at such a sender says little: no coin of it is spoken of. Nothing on the opening's
sender or on W's, which lend. The written list rests on prints held by Lean's kernel against their
makers (the limits of AtFullSide/K14/RawAheadWritten.lean and BookWholeWritten.lean). The full size
alone; the format's second hash function alone. Options are raised in front of the evaluations. In the side
library, because it imports files of it. No property of the protocol is claimed.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawEntriesKit
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.Desc.ProofFile.Honest.K1.Sim.AtFill
import AtFullSide.K1.BookAtIdleSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst Pub Ground)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim
open AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
/-- The test accepts the eight written pieces. -/
theorem short_lend : rawShortW.all lendsOk = true := by
  decide +kernel

/-- **The test can fail**: at a spending entry whose owner is a link's reads' sender. -/
theorem lend_bite :
    lendsOk ⟨"x", ⟨⟨1, some 3, 4, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨1, some 3, 8, .K3⟩, 0⟩, true⟩ =
      false := by
  decide

/-- **The test accepts rawAheadW.** -/
theorem ahead_lend : rawAheadW.all lendsOk = true :=
  rawAll_whole _ wants_lend seg_lend short_lend

section
variable {W₀ Rc Tr X₀ X : Type}

/-- **IN SCOPE, WHERE THE GATE ACCEPTS: THE BOOK THAT THE MAKER RETURNS, AT ANY FILLING, HAS THE
WRITTEN ENTRIES.** -/
theorem ahead_at_return {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.B.ahead = rawAheadW := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z hS hR hL (P5J.owed_of_live hL)
  obtain ⟨B, hB, hAh⟩ := bookWhole_returns_written_ahead
  have e : A.B = B := Except.ok.inj
    ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans (ProofFile.Honest.K14.bookWhole_same_at_made hB h))
  rw [e]
  exact hAh

end

/-- **A job behind the opening**: its place is of the kind K1, inside a link, and not the
opening's. -/
theorem later_place (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (Zp : Pub) (G : Ground)
    {J : SendJob (PlaceIn Inst) Unit}
    (hJ : J ∈ (lotJobs (X := Unit) (lotNo o Zp) (lotData S) Zp G).tail) :
    J.P.place.kind = .K1 ∧ J.P.place.link ≠ none ∧ J.P.place ≠ ⟨1, some 0, 1, .K1⟩ := by
  have hm : placeHalf (V := Unit) (id : PlaceIn Inst → PlaceIn Inst) J ∈
      (dataSideNo (V := Unit) (X := Unit) S (id : PlaceIn Inst → PlaceIn Inst) o).halves Zp G := by
    show _ ∈ lotHalves id (lotNo o Zp) (lotData S) Zp G
    rw [lotHalves_eq]
    exact List.mem_map.2 ⟨J, List.mem_of_mem_tail hJ, rfl⟩
  refine ⟨FirstFill.k1_kind S id o Zp G _ hm, FirstFill.k1_linked S id o Zp G _ hm, fun e => ?_⟩
  have hn := jobPlaces_nodup (X := Unit) (lotNo o Zp) (lotData S) Zp G
  rw [List.map_append] at hn
  have hn' : ((⟨1, some 0, 1, .K1⟩ : Place) ::
      (lotJobs (X := Unit) (lotNo o Zp) (lotData S) Zp G).tail.map (·.P.place)).Nodup :=
    (List.nodup_append.1 hn).1
  exact (List.nodup_cons.1 hn').1 (e ▸ List.mem_map.2 ⟨J, hJ, rfl⟩)

/-- **THE PREMISE ON THE BOOK AT THE FIFTY SENDERS THAT LEND NOTHING, AT THE MAKER's OWN BOOK**, at
every order of places. -/
theorem clear_at_later {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (S : OnBytes.HonestTrace.Sz)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (ord : List Place) :
    ∀ J ∈ (lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G).tail,
      SpendersClearAny J.P J.ride A.B ord ⟨J.P.place, 0⟩ := by
  intro J hJ
  obtain ⟨hk, hl, hne⟩ := later_place OnBytes.secondHashFunction S A.Z A.G hJ
  refine clear_of_no_entry fun e he h1 h2 => ?_
  rw [ahead_at_return hS hL hA] at he
  have ht := List.all_eq_true.1 ahead_lend e he
  unfold lendsOk at ht
  rw [h1, h2] at ht
  have hl' : J.P.place.link.isNone = false := by
    cases hq : J.P.place.link with
    | none => exact absurd hq hl
    | some _ => rfl
  have hne' : ((⟨J.P.place, 0⟩ : Addr) == ⟨⟨1, some 0, 1, .K1⟩, 0⟩) = false := by
    refine beq_eq_false_iff_ne.2 fun e' => hne ?_
    exact congrArg Addr.place e'
  simp [hk, hl', hne'] at ht

end AtFullSide.K1

#print axioms AtFullSide.K1.short_lend
#print axioms AtFullSide.K1.lend_bite
#print axioms AtFullSide.K1.ahead_lend
#print axioms AtFullSide.K1.ahead_at_return
#print axioms AtFullSide.K1.later_place
#print axioms AtFullSide.K1.clear_at_later
