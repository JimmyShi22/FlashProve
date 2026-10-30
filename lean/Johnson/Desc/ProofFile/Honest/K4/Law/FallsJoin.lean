-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FallsJoin.lean: CONDITIONAL.

What is here. K4's OWN FALL DOES NOT READ TWO FIELDS OF ITS PUBLIC DATA, AND SO THE LOT's LIST OF
FALLS LIES IN EVERY LIST THAT HOLDS THE FALL AT THE WRITTEN PLACES (at most twelve), WHATEVER STANDS
IN THESE TWO FIELDS. A fall (`Fall`, Honest/Side.lean) is a test at which a member may reject an
honest run. (1) `k4Fall` (Honest/K4/Part.lean) at two public data that agree in P, hp, g, link and
piece is one structure: the count of rounds in front (r0) and the segment's number (seg) are not
read: by unfolding. General. (2) under h : AtMgA, at the ground `ProofFile.blankBy ProofFile.pureRoad.links Zp`:
let fs be a list of falls which, for each group g below 12 whose plan hp the ground has, holds
`k4Fall` at the public data with P := the ground's layers, hp, g, link := 2 g, piece := 3, seg := 2
g and r0 := r0 g, FOR ANY FUNCTION r0 (hk). Then fs holds every fall of the lot's own list
(`k4LotFalls`, Honest/K4/LotFalls.lean). That end is, as it stands, the hypothesis hs of
`coin_of_falls` and `hf_of_falls` (Law/LotFallsLaws.lean) and hfs of `hf_falls_head`
(Law/DescAtPure.lean). The hypothesis hs of `k4_accepted_falls` (Law/FillFalls.lean) and
`k4_accepted_falls_at` (Law/TopsAt.lean) stands at the maker's public part and ground:
`k4LotFalls_sub_atPure` (Law/FallsJoinAt.lean) has the end there. By the library's `IM.k4_seated`
and `IM.k4_seated_scope` (Johnson/IMR/K4Seat.lean) and `k4LotFalls_of_mem`.

Not shown here. hk: THAT ANY LIST HOLDS THESE FALLS: whoever lays the list; no such list is imported
here. EVERY LONGER LIST OF FALLS IS THE WEAKER WAY: a statement that excuses a run wherever a fall
of the list speaks says less at a longer list. That the ground has a plan at each group below 12.
That the lot's own list has twelve members, or any. THE HALF DOES READ r0 (`ptsOf`,
Johnson/Desc/K4/Honest/Front.lean; `k4LookAt`, Honest/K4/Look.lean) AND seg (`k4Wit`): (1) speaks of
the fall alone. THE SECOND FALL, on the free slots behind the batching, is not spoken of. EACH
FALL's SHARE IS A STATED NUMBER: no bound is shown. THAT h CAN HOLD: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). hG ASKS NOTHING BEYOND
h: at h's opening the ground that is made of the public part is there (`IM.Open.blank`). (2): THE
FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one: its imports reach modules under Johnson/Goal/, as
those of Law/SeatedHead.lean do. Which modules it imports in all has not been counted.
No property is claimed.

  `k4Fall_blind`   **the fall reads neither r0 nor seg.**
  `k4LotFalls_sub`   **the lot's falls lie in every list that holds the fall at the written
      places.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LotFallsLaws
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- **THE FALL READS NEITHER r0 NOR seg**: at two public data that agree in the five other fields it
is one structure. -/
theorem k4Fall_blind {S : Type} (P : Layer.Pub) (hp : Layer.HPlan2) (g link piece a a' s s' : ℕ) :
    (k4Fall ⟨P, hp, g, link, piece, a, s⟩ : Fall S) = k4Fall ⟨P, hp, g, link, piece, a', s'⟩ :=
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, hG and hk. **THE LOT's FALLS LIE IN EVERY LIST THAT HOLDS THE FALL AT THE
WRITTEN PLACES**, at every function r0. -/
theorem k4LotFalls_sub {S : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {fs : List (Fall S)} (r0 : ℕ → ℕ)
    (hk : ∀ g, g < 12 → ∀ hp, G₀.W.G[g]? = some hp →
      (k4Fall ⟨G₀.W.layers, hp, g, 2 * g, 3, r0 g, 2 * g⟩ : Fall S) ∈ fs) :
    ∀ f ∈ k4LotFalls Zp G₀, f ∈ fs := by
  intro f hf
  obtain ⟨x, Q, hx, hQ, -, rfl⟩ := k4LotFalls_of_mem hf
  obtain ⟨eP, -, -, ehp⟩ := IM.k4_seated h.laid.pub hG hx
  obtain ⟨hg, el, ep, -⟩ := IM.k4_seated_scope h.scope h.reads h.laid.pub hG hx
  unfold k4PubOf at hQ
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
  have e := hk x.2.g hg x.2.hp ehp
  rw [← eP, ← el, ← ep] at e
  rw [k4Fall_blind x.2.P x.2.hp x.2.g x.2.link x.2.piece a (r0 x.2.g) (2 * x.2.g) x.2.link]
  exact e

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fall_blind
#print axioms ProofFile.Honest.K4.k4LotFalls_sub
