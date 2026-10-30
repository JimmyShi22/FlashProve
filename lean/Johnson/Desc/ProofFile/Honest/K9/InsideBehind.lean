-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/InsideBehind.lean: FOR THE PREMISE hbeh OF Honest/K9/FrontBridge.lean's BRIDGE ("inside
the members' ranges" at the part behind what runs behind the batching): TWO LEMMAS ON WHAT RUNS BEHIND THE BATCHING. The
premise itself is paid at all 25 segments, from K9's seat, at a stand of the frame's own thread at the library's head,
in Honest/K9/TotalExchangeFree.lean (`insideAt_behind_seat`), whose proof calls both. Statements and proofs; no prover
is in this file; no goal is stated.
  `insideAt_runBehind`   what runs behind the batching carries `InsideAt`, where each of its runs keeps what that
      sentence reads of the state (the library's `insF`): AFTER THE LIBRARY's `inRun_of_keeps`
      (Johnson/Desc/First/Link/Law/InRunOfKeeps.lean), whose proof it follows line by line, at one state and without
      that lemma's frame
  `insF_kept`: l < 25, K9's seat: each run behind the batching keeps `insF`: the library's `insF_after_head`, `_layers`,
      `_attention` at our `take_head`, `take_lay`, `take_att` (Honest/K9/K8BehindAt.lean)
WHAT IS NOT CLAIMED. NO MEMBER: that a stand is there is shown by nobody: where there is none `insideAt_behind_seat`'s
sentence is idle. u is a free letter. Both are called by Honest/K9/TotalExchangeFree.lean alone. Nothing on any
property.
GROUND: beneath this file, beside the sealed library, lie 576 files, this one among them: reading copies, all but ours.

-/
import Johnson.Desc.ProofFile.Honest.K9.InsideAtStand
import Johnson.Desc.ProofFile.Honest.K9.K8BehindAt
import Johnson.Desc.ProofFile.Honest.K9.ThrBehind
import Johnson.Desc.ProofFile.Honest.K9.FromYes
import Johnson.Desc.ProofFile.Honest.K9.TotalLay
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.First.Link.Law.InRunOfKeeps
import Johnson.P1K9R.AreadyClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

/-- **What runs behind the batching carries "inside the members' ranges"**, where each of its runs keeps what that
sentence reads of the state. After the library's `inRun_of_keeps`, at one state. -/
theorem insideAt_runBehind {cs : OnBytes.Codes} {ms : List Sound.Mem} {own : List (ℕ × ℕ)} (L : Link S ProofFile.Cl)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, LinkJoin.AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      LinkJoin.insF e₁ = LinkJoin.insF e)
    {s' t : S} {x a : Desc.K9.Part} (hx : Desc.K9.atS.get? s' = some x) (hin : Sound.InsideAt cs ms own x)
    (hr : L.runBehind s' = .ok t) (ha : Desc.K9.atS.get? t = some a) : Sound.InsideAt cs ms own a := by
  have e : LinkJoin.insF t = LinkJoin.insF s' := LinkJoin.runBehind_keep LinkJoin.insF L hq s' t hr
  unfold LinkJoin.insF at e
  obtain ⟨e1, e⟩ := Prod.mk.inj e
  obtain ⟨e2, e⟩ := Prod.mk.inj e
  obtain ⟨e3, e4⟩ := Prod.mk.inj e
  obtain ⟨a1, a2⟩ := LinkJoin.part_reads t a ha
  obtain ⟨x1, x2⟩ := LinkJoin.part_reads s' x hx
  have hL : a.L = x.L := Option.some.inj (a1.symm.trans (e1.trans x1))
  rw [Desc.K9.get_fork t a ha, Desc.K9.get_fork s' x hx] at e4
  have h4 : LinkJoin.sl a.F = LinkJoin.sl x.F := Option.some.inj e4
  obtain ⟨n1, n2⟩ := Prod.mk.inj h4
  refine LinkJoin.insideAt_congr hin (by rw [hL]) (a2.trans (e2.trans x2.symm))
    ((LinkJoin.part_bookOf t a ha).trans (e3.trans (LinkJoin.part_bookOf s' x hx).symm)) fun j hj => ?_
  rw [← n1, ← n2]
  exact hj

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Each run behind the batching keeps what "inside the members' ranges" reads, at all 25 segments**: the library's
three laws by sort, at our own ties of the sort. -/
theorem insF_kept (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l kk Lk p ww)
    (u : HTailF2) :
    ∀ o ∈ Lk.orderAfter, ∀ run, LinkJoin.AtAfter Lk o run → ∀ e e₁, run e = .ok e₁ →
      LinkJoin.insF e₁ = LinkJoin.insF e := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨pC, pD, hC, -⟩ := P1K9.bothPlaces_at_head h l hl
  by_cases h24 : l = 24
  · subst h24
    have hs : IM.subAt 24 = .head := rfl
    obtain ⟨X, -, T⟩ := take_head h O hs Lk p hlk seg drawB kp pC pD hC u
    exact LinkJoin.insF_after_head (hs ▸ seg) T
  · obtain ⟨g, rfl | rfl⟩ := Nat.even_or_odd' l
    · have hg : g < 12 := by omega
      have hs := sub_even g hg
      obtain ⟨p4, X, -, -, A⟩ := take_lay h O (2 * g) hl hs Lk p hlk seg drawB kp pC pD u
      exact LinkJoin.insF_after_layers (hs ▸ seg) A
    · have hg : g < 12 := by omega
      have hs := sub_odd g hg
      obtain ⟨A, X, -, -, T⟩ := take_att h O hg hs Lk p hlk seg drawB kp pC pD hC u
      exact LinkJoin.insF_after_attention (hs ▸ seg) T

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.insideAt_runBehind
#print axioms ProofFile.Honest.K9.insF_kept
