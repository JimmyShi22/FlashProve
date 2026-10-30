-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHeadNums.lean: `goodW_head_shares` (Honest/K9/GoodHeadWrap.lean) AT THE FULL SIZE's
WRITTEN NUMBERS. One statement with its proof; no definition; no goal is stated.
  `goodW_head_nums` b := 1995 · e := 2168 · lk := 18 · first := 3531 · n := the seat's w.2.2.filled (= 3570). Six of the
      seven premises on numbers are paid by `numbers_head` and `filled_head` (Honest/K9/HeadNumbers.lean) and omega; the
      seventh, sv + 1 = 2168, is on a letter of the state and stays. SO THE SIX ARE MET TOGETHER AT THESE NUMERALS
WHAT IS NOT CLAIMED. K6's eight premises, `MergeLive 18 3531 sv s`, Kp, JC, JD at any state. That lk = 18 or
first = 3531 are the plan's: they come in with `MergeLive`, from whoever brings it. NO MEMBER. Called by
Honest/K9/GoodHeadHanded.lean alone. At the full size and the format's second hash function alone, as h. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodHeadWrap
import Johnson.Desc.ProofFile.Honest.K9.HeadNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.ForkMerge.Live (MergeLive)
open ProofFile.Honest.K3.Good.Live (Clause KeysClear BitsClear PinsClear)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **`goodW_head_shares` AT THE WRITTEN NUMBERS OF THE FULL SIZE**: of its seven premises on numbers six are paid, by
`numbers_head` and `filled_head`; the seventh, `sv + 1 = 2168`, is on a letter of the state and stays. -/
theorem goodW_head_nums (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2)
    {pC pD : First.Look.P} (hC : Look.placeAt (P5J.At.X Zp) 24 false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) 24 true = some pD) (Kp : S → Prop) {sv : ℕ}
    (kDraw : ∀ t y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide t [⟨[], drawnOne y⟩] [] = .ok t₁ →
      Kp t → Kp t₁)
    (kHand : ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z → Kp z.2)
    (kLive : ∀ j, 1995 ≤ j → j + 1 < 2168 → ∃ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z →
      Desc.K9H.liveAt z.1 j = true)
    (kPlain : ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run → ∀ m t z,
      run m t = .ok z → ∀ j, Desc.K9H.plainAt z.1 j = true)
    (kUn : ∀ j, 2168 ≤ j → ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run →
      ∀ m t z, Kp t → run m t = .ok z → Desc.K9H.unnamedAt z.1 j = true)
    (kKeys : ∀ t, Kp t → ∀ j < 1995, KeysClear (Kinds.Head.callerKeys
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp)))
      (Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)))) t j)
    (kBits : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, BitsClear rd t j)
    (kPins : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, PinsClear rd t j)
    (esv : sv + 1 = 2168) (s : S) (hI : MergeLive 18 3531 sv s) (K : Kp s) (JC : Clause pC s.lookHeard?)
    (JD : Clause pD (s.tl?.bind (·.heard))) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s w.2.2.filled := by
  obtain ⟨f0, fD, hsC, hsD, spC, spD, eC, eD⟩ := numbers_head h hC hD
  rw [filled_head h Sd]
  exact goodW_head_shares h Sd u spC spD Kp kDraw kHand kLive kPlain kUn kKeys kBits kPins f0 eC (by omega) fD.symm esv
    (by omega) (by omega) s hI K JC JD

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodW_head_nums
