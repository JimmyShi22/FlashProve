-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Law/FactsAtReach.lean: CONDITIONAL: WHAT THE SECOND TIE OF THE PROXIMITY
TEST (kind K12) SPENDS OF THE VERIFIER's STATE IN FRONT OF THE TEST, AT EVERY STATE THAT IS REACHED
BY THE FIRST CHAIN's OWN SUB-PROTOCOLS' STEPS WITHOUT A MARK: under the library's head. Statements
with their proofs: calls; no definition. Over the library alone.

Why. The library has these facts as fields of one structure (FoldFacts,
Johnson/Desc/First/FoldFacts.lean) at a letter for "reached" that must give the reach by the WRAPPED
sub-protocols' steps, in which every shown word is tested to be below the prime
(P5J.atMgR_of_head, Johnson/P5J/StartAtHead.lean). A caller that has the reach by the bare steps
alone cannot call that. The theorems beneath these fields take the bare reach: they are called here.

  facts_of_reach    CONDITIONAL: FactsF (Johnson/Loose/H2K12/AcrossOfSits.lean: the book is in
                    order; the seats are carried; the book fits; the pile's masks) and "the state's
                    codes are the data's", at the closed data P5J.At.foldD Zp cF L, at every border
  left_with_facts   CONDITIONAL: there is one list L at which BOTH hold: the kind's named list of
                    closed facts (K12Left, Johnson/Loose/H2K12/Owed354AtMg.lean, at the closed
                    filling) and facts_of_reach's end at every reached state without a mark

The premises. h: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) · in facts_of_reach: hl: L
is what the library's maker lays of the proof's first chain; hr: the state is reached by the bare
steps; hu: it bears no mark.

THE ROAD. nine_reached (Johnson/Desc/AtSeats/K13NineAtAll.lean) has nine tests at a state that is
reached by the bare steps: four of them are FactsF's fields. Its premise on the sendings:
IM.sends_pinned_paid at the first of the two pins that the head gives (pins_of_head,
Johnson/Loose/H2K12/K12RestOfHead.lean). The codes: Meaning.K2.codes_field
(Johnson/IMR/AtReach.lean). left_with_facts goes as k12Left_at_head
(Johnson/Loose/H2K12/K12AtHead.lean) does, and keeps in hand that its L is what the maker lays.

Limits. Conditional. h is a hypothesis. That any state is reached at a border above 0 is not shown
here. K12Left's field fold still speaks of the wrapped reach: it is handed on as it stands. At the
library's full size and the format's second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.K12AtFree
import Johnson.Desc.AtSeats.K13NineAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K12
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FOUR FACTS AND THE CODES, AT A STATE THAT IS REACHED BY THE BARE STEPS.** CONDITIONAL:
under the hypothesis h; L is what the maker lays of the proof's first chain; the state is reached at
the border number k; it bears no mark. -/
theorem facts_of_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hl : P5J.At.laid? Zp = some L) {k : Nat}
    {a : ProofFile.InstPub × TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (hu : a.2.failed = none) :
    FactsF (P5J.At.foldD Zp cF L) a.2 ∧ a.2.st.codes = (P5J.At.foldD Zp cF L).sent.codes := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc h.laid.planOk
  have hB := IM.sends_pinned_paid O (pins_of_head h).1
    (IM.hp_of_planOk h.scope h.reads O (IM.blocksOk_of_planOk O h.laid.planOk))
  have N := VerifiableInference.Desc.K13.Law.nine_reached h.scope h.reads h.laid.value
    h.laid.planOk O hB hl k a hr hu
  exact ⟨⟨N.book, N.seats, N.fits, N.masks⟩,
    _root_.Meaning.K2.codes_field h.scope h.reads O hp _ id (fun _ _ q => q) k a hr hu⟩

/-- **ONE LIST AT WHICH THE KIND's CLOSED FACTS AND THE FACTS AT REACHED STATES BOTH HOLD.**
CONDITIONAL: under the hypothesis h. -/
theorem left_with_facts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ L, K12Left h h.free (P5J.At.foldD Zp cF L) ∧
      ∀ (k : Nat) (a : ProofFile.InstPub × TS), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a →
        a.2.failed = none →
        FactsF (P5J.At.foldD Zp cF L) a.2 ∧
          a.2.st.codes = (P5J.At.foldD Zp cF L).sent.codes := by
  obtain ⟨hm, hc⟩ := pins_of_head h
  have W : Written354 Zp := written354_of_pins h.scope h.laid.pub hm
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)
  obtain ⟨L, R⟩ := reached_some h W hm hc
  exact ⟨L, k12Left_of_rest (k12Rest_of_pins h h.free R h.free_q₁ hm hc) (lastTypedAt_at_head h),
    fun _ _ hr hu => facts_of_reach h R.listed hr hu⟩

end H2K12

#print axioms H2K12.facts_of_reach
#print axioms H2K12.left_with_facts
