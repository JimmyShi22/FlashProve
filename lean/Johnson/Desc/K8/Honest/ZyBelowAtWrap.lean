-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ZyBelowAtWrap.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's
BLOCKS, EACH WITH THE TEST ON WORDS IN FRONT (`Sound.below`, Johnson/Desc/Sound/ChainRule.lean),
REACH IN FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN THE GOALS'
SCOPE: EVERY COORDINATE OF zy, AS THE TEST's DATA HOLD WHAT THE DIGITS' LOOKUP HAS HEARD, HAS ITS
WORDS BELOW THE PRIME. It is the sentence on which `weights_of_below` and `allFront_of_two`
(Johnson/Desc/K8/Honest/WeightsAtReach.lean, HeldInScope.lean) still hung. Lemmas; none of the
library's goals.

  **`zy_behind_digits`** behind a yes of the seated lookup on the digits, at rounds that pass the
                   library's test on words okRoundsE
  **`zy_below_at_wrap`** at a state reached by the wrapped blocks, l < 24: for every x in g.zy: okE
                   x
  `zy0_below_at_wrap` so okE (g.zy.getD j zeroE), at every j
By: `block_words` (Johnson/Desc/K8/Honest/LookBelow.lean) · the library's `Sound.below_yes` and
`Sound.okWords_of_view` (Johnson/Desc/Sound/PieceYes.lean), `okRoundsE_take`, `theStated_yes_digits`
(Johnson/Desc/First/Look/K3DigitsSeatedYes.lean), `quietAt_tl`, `piece_digits`, IM.k3_of,
IM.yes_alone, `reach_pred`, `stepYes_decide`. KIN IN THE LIBRARY: Johnson/Top/H/K3PieceHears.lean
makes the same two calls at the lookup's block's decide, to the library's okRoundsE.
WRITTEN A FURTHER TIME: the walk of `zy_below_at_wrap` is that of `slot_at_batch`
(Johnson/Desc/K8/Honest/SlotAtReach.lean), so of the library's `leftOn_digits_behind`, over the
wrapped list.
ONE DEVICE STANDS IN IT, as in SlotAtReach.lean: `attribute [-instance] Inst.Model.Scl.ref`.
KIN, AND FIRST: that the words of every coordinate of zy lie below the prime where the rounds'
sampled words do is shown, on another road (the structure that the challenges alone make), behind an
accepting step of the member at the lookup on the digits, at all 25 segments, under the library's
`P5J.AtMgA` and one premise more, in Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean
(`digits_points_link`, `ok_zy_at`, `ok_layBack`).
Limits. AT THE WRAPPED FAMILY ALONE: at the family that the bare blocks reach the sentence can fail
(WeightsAtReach.lean says why). `Sound.below` is a device of the proof and runs nowhere; the
decision that runs makes the same test once, on all that is shown. NOTHING AT THE HEAD's SEGMENT:
there one block more stands between the lookup's member and the batching's. IN SCOPE ALONE: under an
opening of the description and its test on its plan; the first chain. Nothing says that any state is
reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.LookBelow
import Johnson.Desc.K8.Honest.SlotAtReach
import Johnson.Desc.Sound.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (theStated_yes_digits okRoundsE okRoundsE_take)
open VerifiableInference.Desc.LinkJoin (quietAt_tl piece_digits)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE DIGITS, at rounds whose drawn words lie below the
prime: so do the words of every coordinate of zy.** -/
theorem zy_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c)
    (hb : okRoundsE rs = true) :
    ∃ g, c.tl?.bind (·.heard) = some g ∧ ∀ x ∈ g.zy.toList, OnBytes.okE x = true := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨g, hg, hz⟩ := block_words (K3.seatDigits claim) (K3.seatDigits_reads claim) a.piece laid
    sent P' [] s s' _ gs' hyes (okRoundsE_take _ n hb)
  have hg' : s'.tl?.bind (·.heard) = some g := hg
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact ⟨g, hg', hz⟩
  · exact ⟨g, by rw [quietAt_tl X i f hf s' c hfs]; exact hg', hz⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE THAT THE WRAPPED BLOCKS REACH IN FRONT OF THE BATCHING OF A SEGMENT
l < 24.** -/
theorem zy_below_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    {g : Forest.Heard} (ht : s.tl? = some tl) (hg : tl.heard = some g) :
    ∀ x ∈ g.zy.toList, OnBytes.okE x = true := by
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (Keeps.planOk_blocks _ hOk).1
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  have h1 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + IM.k3Ix l true + 2 + 1) (z, s) := by
    rw [i3]
    exact h
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  obtain ⟨z', s₀, s'', b₀, e, hr, hb, hy⟩ := reach_pred h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  rw [List.getElem?_map, hf] at hb
  obtain rfl : Sound.below b = b₀ := Option.some.inj hb
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨hv, hd₀⟩ := Sound.below_yes b _ _ _ _ hd
  have hw : okRoundsE rs = true := Sound.okWords_of_view _ hv
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s₀ _ rs gs).1 hd₀).1
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨g', hg', hz⟩ := zy_behind_digits _ _ _ _ _ _ b' e3 hOk' l rfl hpc s₀ _ rs gs hd' hw
  rw [ht] at hg'
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  exact hz

/-- So of the coordinate that the weights read. -/
theorem zy0_below_at_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    {g : Forest.Heard} (ht : s.tl? = some tl) (hg : tl.heard = some g) (j : Nat) :
    OnBytes.okE (g.zy.getD j zeroE) = true := by
  have k := zy_below_at_wrap hS hR O hOk hl h ht hg
  by_cases hj : j < g.zy.size
  · have e : g.zy.getD j zeroE = g.zy[j] := by simp [Array.getD, hj]
    rw [e]
    exact k _ (Array.getElem_mem_toList hj)
  · have e : g.zy.getD j zeroE = zeroE := by simp [Array.getD, hj]
    rw [e]
    rfl

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.zy_behind_digits
#print axioms VerifiableInference.Desc.First.K8.Honest.zy_below_at_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.zy0_below_at_wrap
