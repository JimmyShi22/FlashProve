-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WtBack.lean: THE FIELD "wt" OF WHAT IS LEFT OF THE SMALLNESS TEST's FIELD "blind" AT
THE CLOSED CONSTANT OF THE COMPOSED MEANING (`BlindOwes`, Johnson/P1K8R/BlindJoin.lean): THE
SENTENCE "weights" GOES BACK OVER THE DRAW. From the head `P5J.AtMgA` alone. So `BlindOwes` at
each of the 25 links is left with ONE premise: the fence. A joining of other files' theorems.
What the sentence is. The head lays `h.𝔇.wt` := `P5J.At.wt Zp cF Z.lay` (Johnson/P5J/MgAtAll.lean,
LettersAt4.lean) := the output head's `wtK6` (Johnson/Desc/Kinds/Law/WtK6.lean):
fun m a _ w => m = 24 → InRange w.cells → WeightAt X a.2 ‹cells off w› ‹a mask off w›. It reads no
string; the witness is one on both sides. So the field asks: WeightAt at the state behind a draw's
yes gives WeightAt at the state in front.
  `head_of_heard`: behind a draw's yes, where the head's seat's reader "heard" answers, the state
    stands in the head's segment.
  `weightAt_back`: **the sentence goes back over the draw**: by `alike_of_drawn`
    (Johnson/Desc/Kinds/Law/K6TlBlind.lean), `KeptW.of_alike` and `weightAt_kept`
    (Johnson/Desc/Kinds/Law/WeightAtSame.lean): "heard" answers behind because the sentence holds
    there.
  `wt_back_at`: **the field, to the letter, at every l and base.**
  `blindOwes_of_fence`: **at each l ≤ 24: the fence gives `BlindOwes h l base`.**
Limits. At `OnBytes.secondHashFunction` alone (the head's). The fence is shown nowhere here. A member of the
head `AtMgA` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). The
other premises here follow from the head; no file joins them to a member. Nothing on soundness or on
hiding.

-/
import Johnson.P1K8R.BlindOwesAt
import Johnson.Desc.Kinds.Law.WeightAtSame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf sampledIn openSets start)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept alike_of_drawn)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- Behind a draw's yes, where "heard" answers, the state stands in the head's segment. -/
theorem head_of_heard (hS : Model.Head.Shape) (iU3 : ℕ) {s t : S} (hd : Drawn s t)
    (hh : ∃ H, (seatAt hS iU3).heard t = some H) : ∃ o, t.here = .head o := by
  obtain ⟨H, e⟩ := hh
  revert e
  refine drawn_ind (motive := fun _ t => (seatAt hS iU3).heard t = some H →
    ∃ o, t.here = .head o) ?_ ?_ ?_ hd
  · intro s a mm f _ e
    exact nomatch e
  · intro s a mm f _ e
    exact nomatch e
  · intro s a mm f _ _ _
    exact ⟨_, rfl⟩

/-- **The sentence "weights" goes back over the draw.** -/
theorem weightAt_back (W : Verify.Public) {s t : S} (hd : Drawn s t) {c : _} {m : _}
    (H : WeightAt W t c m) : WeightAt W s c m := by
  have hh : ∃ Hh, (seatAt W.hS (Law.readsOf W)).heard t = some Hh := by
    obtain ⟨_, Hh, _, e2, _⟩ := H
    exact ⟨Hh, e2⟩
  obtain ⟨_, a⟩ := alike_of_drawn hd (Or.inr (head_of_heard _ _ hd hh))
  exact (weightAt_kept W (KeptW.of_alike a) hh c m).2 H

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD "wt", TO THE LETTER.** -/
theorem wt_back_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (l base : ℕ) :
    ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt l (z, t) y' w →
      h.𝔇.wt l (z, s) y w := by
  intro z s t y y' w hd _ H
  have H' : VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp) (P5J.At.arr Zp)
      (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 l (z, t) y' w := H
  show VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp) (P5J.At.arr Zp)
      (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 l (z, s) y w
  intro h24 hr
  exact weightAt_back _ hd (H' h24 hr)

/-- **AT EACH OF THE 25 LINKS: THE FENCE GIVES `BlindOwes`.** -/
theorem blindOwes_of_fence (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    (base : ℕ)
    (hf : ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf l]?.getD []), y.1 < base) : BlindOwes h l base :=
  blindOwes_all h hl base (wt_back_at h l base) hf

end

end P1K8T

#print axioms P1K8T.head_of_heard
#print axioms P1K8T.weightAt_back
#print axioms P1K8T.wt_back_at
#print axioms P1K8T.blindOwes_of_fence
