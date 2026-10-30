-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due5.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, FIFTH COUNT: `k03_cond_due5` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due4`
(Johnson/P5J/K03Due4.lean, which does not turn). FROM the head, the filling 𝔏, its three equations
q₁ q₂ q₃ and:
  CLOSED, ON PUBLIC DATA:
    hcalls: the head's calls are seated (one test);
  WHERE A PIECE ACCEPTS:
    Fd: `DigFormsR`: the forms of other runs across an accept of the digits' piece (25);
    Rd: rides at the 25 digits' places.
s₀ and z₀ are idle letters of the condition's own text.

Beside it: `k03_objEnd_at` · `k03_digTests_at`: the masks' three tests at the 25 calls' and the 25
digits' places, from the head · `k03_maskC_at`: the one closed test of the calls' joins, likewise.

PAID HERE BEYOND `k03_cond_due4`: oneC (`H2K5.Door.oneC_at_head`) · tie at the 24
calls (Johnson/P5J/K03TieAt.lean, K03TieHead.lean, over three kinds' ties of the names) · the
masks' three tests, ×50 (hB: Johnson/P5J/K03MaskBAt.lean; hTests and h6:
Johnson/P2LawR/MasksAtHead.lean) · the head's model, from hcalls
(Johnson/P5J/K03HeadModelHead.lean; it reads no accept: it binds every reached state without a mark
on the promise in front of the head's calls) · the item formsInT l pc
"objects" behind the lookup on the calls at all 25 (Johnson/P5J/K03ObjInAt.lean, at both runs that
the name stands for), its two named facts behind the accept by Johnson/P5J/K03MaskLeanAt.lean and
Johnson/P5J/K03MergeIdleAt.lean, K03MergeIdleHeadAt.lean. (The same joins, as named theorems that
end in the ledger's fields: Johnson/P5J/K03OthersPubPaid.lean [not in this library].)

SO AT THE 25 CALLS' PLACES NOTHING IS LEFT BUT ONE CLOSED TEST (hcalls).

Limits: all of the above are premises; no member is known. "From the head" moves tests into the
head; whether there is a head is not said here. At secondHashFunction alone. Nothing on soundness by itself;
nothing on hiding.


-/
import Johnson.P5J.K03Due4
import Johnson.P5J.K03ObjInAt
import Johnson.P5J.K03MaskLeanAt
import Johnson.P5J.K03MaskBAt
import Johnson.P2LawR.MasksAtHead
import Johnson.P5J.K03MergeIdleAt
import Johnson.P5J.K03MergeIdleHeadAt
import Johnson.P5J.K03TieAt
import Johnson.P5J.K03TieHead
import Johnson.P5J.K03HeadModelHead
import Johnson.Desc.First.Att.Door.Law.K5OneOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (attAt layAt digAt lookAt tlAt idxAt attAt_shape
  attAt_letters layAt_letters lay_letters)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open _root_.Meaning (linkTieB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **The masks' three tests at the 25 calls' places, from the head.** -/
theorem k03_objEnd_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      ObjEndR (h.toAtMg.𝔇 h.𝔇) (k3K l false) l y L (msgsOfChain Zp.made.proof.1) :=
  fun L hL l hl y hk =>
    ⟨k03_hB_calls h l hl y hk, by
      rw [lookAt_link hk]
      exact h.toAtMg.hTests_calls hL hl, h.toAtMg.h6_at_head⟩

/-- **The one closed test of the calls' joins (K03OthersPubPaid.lean [not in this library]), from the head.** -/
theorem k03_maskC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y, lookAt (At.X Zp) l false = some y →
      h.maskC L y l = true :=
  fun L hL l hl y hk => (k03_objEnd_at h L hL l hl y hk).hTests

/-- **The masks' three tests at the 25 digits' places, from the head.** -/
theorem k03_digTests_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ L, At.laid? Zp = some L → ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      DigTestsR (h.toAtMg.𝔇 h.𝔇) l y ((At.foldD Zp cF L).ownAt l 3) L
        (msgsOfChain Zp.made.proof.1) :=
  fun L hL l hl y _ hy =>
    ⟨k03_hB_digits h l hl y (k03_look_dig hy), by
      rw [lookAt_link (k03_look_dig hy)]
      exact h.toAtMg.hTests_digits hL hl, h.toAtMg.h6_at_head⟩

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, FIFTH COUNT.** -/
theorem k03_cond_due5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (hcalls : VerifiableInference.Desc.Kinds.Head.Law.AtFold.callsSeatedC (At.arr Zp)
      (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp) (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent
      (h.toAtMg.𝔇 h.𝔇).l3.rad x.link ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (Fd : ∀ l < 25, ∀ sub, linksFull[l]? = some sub →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigFormsR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l sub q b')
    (Rd : ∀ l < 25, ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
          (k3K l true) q b') :
    h.K3Cond 𝔏 := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  have P := k03_planR_at h (k03_digRow_at h.toAtMg) (k03_headRow_at h.toAtMg)
  have Oc := k03_objEnd_at h
  have Mk : ∀ l (hl : l < 25) y (_ : lookAt (At.X Zp) l false = some y),
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
      K03MaskAt h l q b' := fun l hl y hk =>
    k03_maskAt_lean h 𝔏 q₁ q₂ q₃ R.fold hl hk (Oc L R.listed l hl y hk).hTests
  refine k03_cond_due4 h 𝔏 q₁ q₂ q₃ s₀ z₀ (fun l hl => H2K5.Door.oneC_at_head h hl) ?_ ?_ Oc
    (k03_digTests_at h) ?_ ?_ Fd Rd ?_
  · intro l hl y A tl hy
    have hodd := attAt_odd hy
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    obtain ⟨hxl, -, htl, -⟩ := attAt_letters h.scope h.reads h.pubOne (by omega) hy
    rw [htl, hxl]
    exact k03_tie_head h hl
  · intro l hl y tl hy ht
    obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
    obtain ⟨hev, h24⟩ := layAt_even hp4 hN hy
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    have hg : g < 12 := by omega
    obtain ⟨-, hxl⟩ := layAt_letters h.scope h.reads h.pubOne hg hy
    rw [hxl, lay_letters h.scope h.reads h.pubOne hg ht]
    exact k03_tie_even h hg
  · intro l hl q hq b' hb'
    rcases Nat.mod_two_eq_zero_or_one l with he | he
    · obtain ⟨y, tl, hy, -, -, -⟩ := P.lay l hl he
      have hk := k03_look_lay h (by omega) hy
      exact k03_objIn_calls h 𝔏 q₁ q₂ q₃ hl hk (k03_shape_lay hy) q hq b' hb'
        (Mk l (by omega) y hk q hq b' hb')
        (k03_mergeAt_calls h 𝔏 q₁ q₂ q₃ l hl y hk q hq b' hb')
    · obtain ⟨y, A, tl, hy, -⟩ := P.att l hl he
      have hk := k03_look_att h (by omega) hy
      exact k03_objIn_calls h 𝔏 q₁ q₂ q₃ hl hk (attAt_shape hy) q hq b' hb'
        (Mk l (by omega) y hk q hq b' hb')
        (k03_mergeAt_calls h 𝔏 q₁ q₂ q₃ l hl y hk q hq b' hb')
  · intro q hq b' hb'
    have hk := k03_look_head h
    exact k03_objIn_head h 𝔏 q₁ q₂ q₃ q hq b' hb'
      (Mk 24 (by omega) x hk q hq b' hb')
      (k03_mergeAt_head_calls h 𝔏 q₁ q₂ q₃ x hk q hq b' hb')
  · intro q hq b' hb'
    exact ⟨k03_head_model_head h hcalls K3Lot.ofForm (At.seats Zp) s₀ q b'⟩

end P5J

#print axioms P5J.k03_objEnd_at
#print axioms P5J.k03_maskC_at
#print axioms P5J.k03_digTests_at
#print axioms P5J.k03_cond_due5
-- Five payers of "from the head", asked here by
-- name once more, so that a print of this file bears their own answers.
#print axioms P5J.pins_of_laid
#print axioms P5J.AtMg.pins
#print axioms P5J.AtMg.fence
#print axioms LPFD.asks_rest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tests_of_pin
