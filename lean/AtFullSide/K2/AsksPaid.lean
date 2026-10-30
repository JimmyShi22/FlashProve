-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/AsksPaid.lean: K2AsksPaid: what the senders in front laid, at every script of the form
S, at a run whose input passes the description's first test and is a typed one.

1. The input of a state of the thread is the run's input w, and it is valid: head_valid.
2. So it is typed, by the premise on w, and its instance is light, by light_of_start.
3. JoinSenders at that input: first_senders at the switch into the group 1, later_senders at every
   switch: at the very jobs of the joined list.
4. The limbs of JoinAsks follow: firstAsks_of_senders, laterAsks_of_senders, symbols_at_join.

The premises are those of K2AsksPaid. The limits of the files called stand.
-/
import AtFullSide.K2.AtTheBaseExchange
import AtFullSide.K2.AtTheBase
import AtFullSide.K2.FirstSenders
import AtFullSide.K2.SymbolsTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName Strs fieldPrimeWord)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- **What the senders in front laid is paid.** -/
theorem k2AsksPaid : K2AsksPaid := by
  intro W₀ I Oh Z D r Zp Np cF x A Bs base hA h O Y X₂ S test item n₁ n₂ b₀ Vd Rd Kp w Said hOk hs₀
    hty
  refine ⟨hs₀, fun p hp => ?_⟩
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hst : ∀ v i y u, (baseLetters h A S.Q test item n₁ n₂ b₀ Vd Rd Kp w).thread.stored v i y = some u →
      ∀ a ∈ u, a < fieldPrimeWord := fun v i y u e => stored_below A.H v.w₀ v.rc i y u e
  have hR4 : ∀ v, (baseLetters h A S.Q test item n₁ n₂ b₀ Vd Rd Kp w).valid v → ReadsLight Zp Bs.G₀ v.x := by
    intro v hv
    have hv' : v = w ∧ Vd v := hv
    obtain ⟨e, hV⟩ := hv'
    rw [e] at hV ⊢
    exact light_of_start h O (hs₀ hV)
  intro blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s' hT hd hS c V Wl r₁ r₂ s₁ t x'
    z S3 Yv rows Gr cd hc hL hW hr hbf Ay ha
  have hval : m.st.input = w ∧ Vd m.st.input := hT.1.2.2.2.2.2.2
  have htyM : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull,
      m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub := by
    have hV := hval.2
    rw [hval.1] at hV ⊢
    exact hty hV
  have hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ m.st.heard.length := by
    have e := drawsFit_length _ _ hT.1.2.1
    rw [e, List.length_append]
    exact Nat.le_add_left _ _
  have S₀ : JoinSenders Zp Bs cF (byNo cF.blocksInOrder (K1.lotJobs (X := Y) S.no (K1.lotData Sz.ref) Zp Bs.G₀ ++
               wJobs (X := Y) S.no S.Dd Zp Bs.G₀)) (rowsAt Zp Bs) (reader I Zp) p k c S.Q
      (baseLetters h A S.Q test item n₁ n₂ b₀ Vd Rd Kp w).valid m.st.input m.st.heard ds (placeIn I Zp) S.own₀ :=
    ⟨fun h1 => ⟨0, Nat.zero_le _, first_senders h O hA S.no S.Dd S.cellsQ S.tokQ (placeIn I Zp) S.own₀
        (reader I Zp) S.rest S.ch S.Jt S.stages S.own₂ S.n₀ S.ok S.codes S.sh S.sh₁ S.rest₂ S.Oth
        S.share _ m.st.input rfl rfl hpS h1 k c m.st.heard ds hlen⟩,
      later_senders h O hA S.no S.Dd S.cellsQ S.tokQ (placeIn I Zp) S.own₀ (reader I Zp) S.rest S.ch
        S.Jt S.stages S.own₂ S.n₀ S.ok S.codes S.sh S.sh₁ S.rest₂ S.Oth S.share _ m.st.input rfl rfl
        hpS k c m.st.heard ds hlen⟩
  exact ⟨htyM, fun h1 => firstAsks_of_senders S₀ h1, laterAsks_of_senders S₀.later,
    symbols_at_join h O hA S.no S.Dd S.cellsQ S.tokQ (placeIn I Zp) S.own₀ S.rest S.ch S.Jt S.stages
      S.own₂ S.n₀ S.ok S.codes S.sh S.sh₁ S.rest₂ S.Oth S.share test item n₁ n₂ b₀ Vd Rd Kp w hOk hst
      hR4 hp hb hP hn hArm hT hd hS hc hW hr hbf Ay htyM S₀⟩

end AtFullSide.K2.Base

-- This line should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.Base.k2AsksPaid
