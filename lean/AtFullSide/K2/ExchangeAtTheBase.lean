-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/ExchangeAtTheBase.lean: the proof of K2Exchange (AtTheBaseExchange.lean of this folder).
Limits: K2Asks is a premise; nothing here says that the thread's sentence holds at any state.
-/
import AtFullSide.K2.AtTheBase
import AtFullSide.K2.AtTheBaseExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName Strs fieldPrimeWord)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt headPlaceAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2PlaceF)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open AtFullSide.K2.Term

/-- **What the row owes is true behind the member**, under K2Asks. -/
theorem k2Exchange : K2Exchange := by
  intro W₀ I Oh Z D r Zp Np cF x A Bs base hA h O Y X₂ S test item n₁ n₂ b₀ Vd Rd Kp w Said hOk K b q
    hb hq
  obtain ⟨p, hp, rfl⟩ := k2_place_at hb hq
  have hZ : A.Z = Zp := by
    obtain ⟨e, -⟩ := atPure_ok hA
    exact Except.ok.inj (e.symm.trans O.pub)
  have hG : A.G = Bs.G₀ := by
    obtain ⟨-, e, -⟩ := atPure_ok hA
    rw [hZ] at e
    exact Option.some.inj (e.symm.trans O.blank)
  refine (exchangeS_iff _ Said).2 fun j hj => ?_
  refine k2_exchange_left (Wj := K1.PlaceIn ProofFile.Inst) (Xj := Y) h O hA S.no S.Dd S.cellsQ
    S.tokQ (placeIn I Zp) S.own₀ S.rest S.ch S.Jt S.stages S.own₂ S.n₀ S.ok S.codes S.sh S.sh₁
    S.rest₂ S.Oth S.share test item n₁ n₂ b₀ Vd Rd Kp w hOk
    (fun v i y u e => stored_below A.H v.w₀ v.rc i y u e)
    (by rw [hZ, hG]; exact k2_hex I OnBytes.secondHashFunction Sz.ref Oh Zp Bs.G₀)
    (by rw [hZ, hG]; exact k2_ho I OnBytes.secondHashFunction Sz.ref Oh Zp Bs.G₀)
    (fun v hv => by
      obtain ⟨rfl, hV⟩ := hv
      exact light_of_start h O (K.start hV))
    (fun _ _ => rfl) K.asks (switchNo p) q hb hq j hj fun ho => ?_
  exfalso
  have hj' : j ∈ [Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
      Item.row p.link .position] := (k2_owes_at hp) ▸ hj
  exact List.any_eq_false.1 k2_asked_no p hp (List.any_eq_true.2 ⟨j, hj', List.contains_iff_mem.2 ho⟩)

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.k2Exchange
