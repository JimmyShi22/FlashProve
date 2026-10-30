-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkBat.lean: FOR "THE FORM BEHIND" AT THE BATCHING: NO MARK BEHIND, AND THE PROMISE's
FIVE Bools THAT READ THE VERIFIER's STATE, HANDED ON BY EVERY YES OF THE SEATED BATCHING's STEP, UNDER THE LIBRARY's
HEAD AND K9's SEAT, AT ALL 25 SEGMENTS. No thread, no prover, no string is in this file. Statements and proofs ON THE
VERIFIER's TEXT; no goal is stated.
  `linkShare_seated`   the library's `LinkShare Lk p` (the runs' share of a link) at K9's seat, under the head: by the
      library's `share_layers_at`, `share_att_at`, `share_head_at` with the four seating facts off the seat
      (Honest/K9/SeatTied.lean)
  `mark_behind_bat`   behind a yes of the seated batching's step no mark of failure stands (the clause `K9Keeps`' own)
  **`hands_bat`**   `IM.Hands (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) ft (14 l + nAt l + 2) ‹the
      seated batching›`: all six fields: the library's `LPFK9.HandsAt.batch_E` with its three premises paid: the share
      as above; the plan's two counts by `P5J.k9_counts_at`. base: any test that answers alike at any two states (by
      reading, no theorem, the library's `mgBase.pub` is one: it answers false everywhere)
  **`xk_behind_bat`**   so: a yes of the step from s to s', no mark at s (none at s' is `mark_behind_bat`'s), `IM.XK …
      (EW …) b s = true` ⊢ `IM.XK … (EW …) (b + 1) s' = true`
E IS THE PROMISE's PUBLIC TEST (`EW`): five Bools; "in order" is not among them. By the frame's word these
five are enough at its thread; the step from its own test in front to this one is not made here
(Honest/K9/XkFront.lean, under four equations).
WHAT IS NOT CLAIMED. That a yes is there. XK at any state. The like at "the one equation" and "the segment is shut".
`samplesHeld` (Honest/K9/XkSamples.lean). pubP. No member. `linkShare_seated` is called also by
Honest/K9/XkSamples.lean, `batch_number` by XkClose.lean; `hands_bat` here alone; `mark_behind_bat` here and by
Honest/K9/XkAtHead.lean; `xk_behind_bat` by that file alone. `batch_number` is a near twin of the library's
`P5J.batchAt_W` and `LPFK9.batchAt_full`, which end in the hearing kinds' length; it stands at `P5J.fullLinks`:
`P5J.At.links` is that by unfolding, not by a rewrite. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.LPFK9R.SharesAtE
import Johnson.LPFK9R.ShareAtMg
import Johnson.P5J.K09Counts
import Johnson.P1K2R.DebtsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (LinkShare batchAt)
open LPFK9.HandsAt (EW batch_E)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- The runs' share of a link, at K9's seat. -/
theorem linkShare_seated (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp l kk Lk p w) : LinkShare Lk p := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases hs : IM.subAt l with
  | layers => exact LPFK9.share_layers_at h O l hl hs Lk p hlk seg drawB kp
  | attention => exact LPFK9.share_att_at h O l hl hs Lk p hlk seg drawB kp
  | head => exact LPFK9.share_head_at h O l hl hs Lk p hlk seg drawB kp

/-- No mark behind a yes of the seated batching's step. -/
theorem mark_behind_bat {c : Chain S Claim} {Zq : ProofFile.Pub} {l kk : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Zq l kk Lk p w) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s s') : s'.failed = none := by
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact (k9Keeps_of_step Sd ft s s' rs cols n hstep).mark

/-- The number of the batching, in the two forms. -/
theorem batch_number : ∀ l < 25, batchAt P5J.fullLinks P5J.At.ps l = 14 * l + IM.nAt l + 2 := by decide +kernel

/-- **The seated batching hands the promise's five Bools on.** -/
theorem hands_bat (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp l kk Lk p w) {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) :
    IM.Hands (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) ft (14 * l + IM.nAt l + 2)
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  have C := (P5J.k9_counts_at h l hl).1
  rw [batch_number l hl, P1K2.ps_written] at C
  exact batch_E h.𝔇.pubD base z hb hl Lk p (linkShare_seated h hl Sd) C.1 C.2

/-- **XK behind the batching's yes, from XK in front.** -/
theorem xk_behind_bat (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp l kk Lk p w) {P : Type} (base : First.Pub → P × S → Bool) (z : P)
    (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 2) s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 2 + 1) s' = true :=
  ((hands_bat h hl Sd base z hb ft).fenced (Fk := fun _ _ => True)).step trivial hy h0
    (mark_behind_bat Sd ft hy) hx

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.linkShare_seated
#print axioms ProofFile.Honest.K9.mark_behind_bat
#print axioms ProofFile.Honest.K9.batch_number
#print axioms ProofFile.Honest.K9.hands_bat
#print axioms ProofFile.Honest.K9.xk_behind_bat
