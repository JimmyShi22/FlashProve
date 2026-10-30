-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHeadLook.lean: `HeadLive` (Honest/K9/GoodHead.lean) WITH ITS FIRST TWO CLAUSES
PAID, FOR AN INVARIANT OF TWO PARTS: the twin, at the output head's segment, of `lookLive_of_readers`
(Honest/K9/GoodAttLook.lean). One statement with its proof, ON THE VERIFIER's TEXT; no definition; no goal is stated.
  `headLive_of_readers` J := Kp ∧ Jr. Kp: a LETTER, a predicate on states, carried: across K9's draw
      (kDraw) and across every run of the order (kHand): two premises. Jr: a clause on two readings of the state,
      lookHeard? and numOf u: these rest at the draw (`draw_look`, `draw_num`) and at all eleven runs
      (`fieldRun_head_at` at `fieldRests_lookHeard`; the sealed `run_head` at `rests_num`): paid here. The other three
      clauses of `HeadLive` (live · plain · unnamed) stand as premises, each with Kp and Jr in hand
WHAT IS NOT CLAIMED. `HeadLive` at any state: K0 and h0 (Kp and Jr at s) are premises; so are kDraw, kHand and the three
clauses. NO MEMBER. Called by Honest/K9/GoodHeadWrap.lean alone. At the full size and the format's second hash function alone,
as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodHead
import Johnson.Desc.ProofFile.Honest.K9.GoodAttLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.ForkMerge.Live (MergeLive)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **`HeadLive` with "start" and "hand" paid**, for an invariant that is a letter `Kp`, which its own house carries
across the draw and the runs, joined with a clause `Jr` on two readings that rest. -/
theorem headLive_of_readers (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2)
    (lk first sv n : ℕ) (s : S) (Kp : S → Prop)
    (kDraw : ∀ t y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide t [⟨[], drawnOne y⟩] [] = .ok t₁ →
      Kp t → Kp t₁)
    (kHand : ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z → Kp z.2)
    (Jr : Option Forest.Heard → Option HTailF2 × Option (Array HFun) × Option ℕ → Prop)
    (K0 : Kp s) (h0 : Jr s.lookHeard? (numOf u s))
    (live : ∀ j < n, j ≠ sv → (j < first ∨ first + 2 * lk + 2 < j) → ∃ o ∈ Lk.order, ∀ run, At Lk o run →
      ∀ m t z, MergeLive lk first sv t → Kp t → Jr t.lookHeard? (numOf u t) → run m t = .ok z →
        Desc.K9H.liveAt z.1 j = true)
    (plain : ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run →
      ∀ m t z, MergeLive lk first sv t → Kp t → Jr t.lookHeard? (numOf u t) → run m t = .ok z →
        ∀ j, Desc.K9H.plainAt z.1 j = true)
    (un : ∀ o ∈ [(2, "objects"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"), (7, "objects"),
        (5, "K8.equations"), (3, "logits")], ∀ run, At Lk o run →
      ∀ m t z, MergeLive lk first sv t → Kp t → Jr t.lookHeard? (numOf u t) → run m t = .ok z →
        Desc.K9H.unnamedAt z.1 (first + 2 * lk + 2) = true) :
    HeadLive Lk p lk first sv n s := by
  have hm : 24 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs : IM.subAt 24 = .head := rfl
  obtain ⟨X, _, Wh⟩ := LPFK9.headOwesC_24 h O hs Lk p hlk seg drawB kp
  have W := Wh (fun _ => False) (((First.Look.placeAt (P5J.At.X Zp) 24 false).map (·.lm)).getD 0) 0 0 0
    (fun _ _ _ => 0) u u (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl
  refine ⟨⟨fun e => Kp e ∧ Jr e.lookHeard? (numOf u e), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro y t₁ ht
    obtain ⟨a, ha⟩ := draw_open p s t₁ y ht
    refine ⟨kDraw s y t₁ ht K0, ?_⟩
    show Jr t₁.lookHeard? (numOf u t₁)
    rw [draw_look p s t₁ y ht, draw_num u p s t₁ y a ha ht]
    exact h0
  · intro o ho run hr m t z _ hJ hz
    refine ⟨kHand o ho run hr m t z hJ.1 hz, ?_⟩
    show Jr z.2.lookHeard? (numOf u z.2)
    rw [fieldRun_head_at h O hs Lk p hlk seg drawB kp u fieldRests_lookHeard o ho run hr m t z.1 z.2 hz,
      (run_head (rests_num u) W.seg (take_of_headOwesC W) W.k3f).1 o ho run hr m t z.1 z.2 hz]
    exact hJ.2
  · intro j hj h1 h2
    obtain ⟨o, ho, H⟩ := live j hj h1 h2
    exact ⟨o, ho, fun run hr m t z hM hJ hz => H run hr m t z hM hJ.1 hJ.2 hz⟩
  · exact fun o ho run hr m t z hM hJ hz => plain o ho run hr m t z hM hJ.1 hJ.2 hz
  · exact fun o ho run hr m t z hM hJ hz => un o ho run hr m t z hM hJ.1 hJ.2 hz

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.headLive_of_readers
