-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendFull.lean: THEOREMS. **The four tests that the law of a sending asks (SendAsks: KeySendAtDesc.lean) HOLD, BY EVALUATION IN LEAN's KERNEL, at the written sizes of a key file of full size (keyFull)
and the planner's radii as closed numerals; and so at K1's numbers of the key file's three sendings wherever the one-time chain's public values are the written ones.**
OBJECT. Layer A: the closed terms fullIdx | fullMsg | fullW. Layer B: parIdx X | parMsg X | parW X msg (KeySendAtDesc.lean).
USER. The top in scope (KeySendScope.lean, over the five equations five_in_scope, Johnson/RunOne/Law/KeyInScope.lean); through it seat_idx | seat_msg | seat_w, and whoever calls below_send | cond_idx … at these numbers.
LETTERS. Layer A: none. Layer B: X, and the equations as premises.
THE RADII. 6130 · 3131959 · 3138896: by Johnson/Top/H/KeyRadiiAtPlan.lean: maskRadiusOf keyW1 (radius_masks) · radiusOf keyR1 = eRng1 (radius_R1) · radiusOf keyW1 = eOwn1 (radius_W1): the upper end of the planner's distance for the group, times the code's
length, rounded down. radii_are says so here, by these three lemmas.
  asksB_reads                     the four tests read of K1's numbers the codes, the parts and the work alone
  fullIdx | fullMsg | fullW       K1's numbers at the written sizes; what the tests do not read is laid blank
  w_there · one_sampled           W's message is there; at each place JUST ONE message is sampled, the first: the tests are not empty
  asks_full_idx | _msg | _w       **SendAsks 129 at the three closed terms**
  below_128_not · share_not       controls: belowB 128 is false at all three; shareB 200 is false at all three
  asks_idx | asks_msg | asks_w    layer B
What is not claimed. That the radii at which the proximity tests' laws certify closeness are these. One size. Shares of one round's challenges at one place. Nothing on soundness.

-/
import Johnson.RunOne.KeySendAsksB
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Top.H.KeyRadiiAtPlan

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params Johnson.Pack Johnson.RunOne.KeySendErr
open VerifiableInference.Desc.K1 (Par shapeAt shapesOf sampledAt)
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

/-- The four tests read of K1's numbers the codes, the parts and the work alone. -/
theorem asksB_reads (K : Nat) (Q Q' : Par) (rad : Nat → Nat) (hc : Q.codes = Q'.codes) (hp : Q.parts = Q'.parts) (hw : Q.work = Q'.work) :
    asksB K Q rad = asksB K Q' rad := by
  cases Q
  cases Q'
  simp only at hc hp hw
  subst hc hp hw
  rfl

/-- K1's numbers at the written sizes: what the tests do not read is laid blank. -/
def fullPar (what : String) (msg : Array OracleNotice) : Par :=
  { place := ⟨1, none, 0, .K1⟩, codes := keyFull.codes, gp := { samples := 0, firstTree := 0 }, work := 0, parts := [(what, msg)], groups := [] }

def fullIdx : Par := fullPar "the index masks" #[keyFull.once.input]
def fullMsg : Par := fullPar "the lookups' own message and what rides with it" (Wf.messageOf keyFull.ranges.x)
def fullW : Par := fullPar "W and what rides with it" ((linMessageW keyFull.once.shape).getD #[])

/-- The three radii are the planner's. -/
theorem radii_are : Lk6.AtPlan.maskRadiusOf keyW1 = 6130 ∧ Lk6.AtPlan.radiusOf keyR1 = 3131959 ∧ Lk6.AtPlan.radiusOf keyW1 = 3138896 :=
  ⟨Lk6.AtPlan.radius_masks.1, Lk6.AtPlan.radius_R1, Lk6.AtPlan.radius_W1⟩

theorem w_there : (linMessageW keyFull.once.shape).isSome = true := by decide +kernel

/-- At each place just one message is sampled: the first. -/
theorem one_sampled :
    ((List.finRange (shapesOf fullIdx).length).filter fun k => decide (sampledAt fullIdx k)).map (·.val) = [0] ∧
    ((List.finRange (shapesOf fullMsg).length).filter fun k => decide (sampledAt fullMsg k)).map (·.val) = [0] ∧
    ((List.finRange (shapesOf fullW).length).filter fun k => decide (sampledAt fullW k)).map (·.val) = [0] := by decide +kernel

theorem seeds_full : fullIdx.seeds = 1 ∧ fullMsg.seeds = 1 ∧ fullW.seeds = 1 := by decide +kernel

theorem below_full : belowB 129 fullIdx = true ∧ belowB 129 fullMsg = true ∧ belowB 129 fullW = true := by decide +kernel

theorem meets_idx : ∀ k, sampledAt fullIdx k → meetsB fullIdx.codes (shapeAt fullIdx k) 6130 = true := by decide +kernel
theorem meets_msg : ∀ k, sampledAt fullMsg k → meetsB fullMsg.codes (shapeAt fullMsg k) 3131959 = true := by decide +kernel
theorem meets_w : ∀ k, sampledAt fullW k → meetsB fullW.codes (shapeAt fullW k) 3138896 = true := by decide +kernel

theorem share_idx_full : shareB 129 fullIdx (fun _ => 6130) = true := by
  simp only [shareB, badOwn, Nat.choose_two_right]
  decide +kernel
theorem share_msg_full : shareB 129 fullMsg (fun _ => 3131959) = true := by
  simp only [shareB, badOwn, Nat.choose_two_right]
  decide +kernel
theorem share_w_full : shareB 129 fullW (fun _ => 3138896) = true := by
  simp only [shareB, badOwn, Nat.choose_two_right]
  decide +kernel

/-- **The four tests at the written sizes and the planner's radii.** -/
theorem asks_full_idx : SendAsks 129 fullIdx (fun _ => 6130) := ⟨seeds_full.1, meets_idx, share_idx_full, below_full.1⟩
theorem asks_full_msg : SendAsks 129 fullMsg (fun _ => 3131959) := ⟨seeds_full.2.1, meets_msg, share_msg_full, below_full.2.1⟩
theorem asks_full_w : SendAsks 129 fullW (fun _ => 3138896) := ⟨seeds_full.2.2, meets_w, share_w_full, below_full.2.2⟩

/-- Controls: the tests can say no at these very terms. -/
theorem below_128_not : belowB 128 fullIdx = false ∧ belowB 128 fullMsg = false ∧ belowB 128 fullW = false := by decide +kernel
theorem share_not : shareB 200 fullIdx (fun _ => 6130) = false ∧ shareB 200 fullMsg (fun _ => 3131959) = false ∧ shareB 200 fullW (fun _ => 3138896) = false := by
  simp only [shareB, badOwn, Nat.choose_two_right]
  decide +kernel

/-! ## Layer B -/

theorem asksB_of {K : Nat} {Q : Par} {rad : Nat → Nat} (a : SendAsks K Q rad) : asksB K Q rad = true := by
  unfold asksB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨a.seeds, a.meets⟩, a.share⟩, a.below⟩

theorem asks_idx {X : Source} (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) :
    SendAsks 129 (parIdx X) (fun _ => 6130) :=
  asks_of_B ((asksB_reads 129 (parIdx X) fullIdx _ hc (by show [(_, #[X.Y.k.oneTime.indexMasks])] = _; rw [hi]; rfl) rfl).trans (asksB_of asks_full_idx))

theorem asks_msg {X : Source} (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) :
    SendAsks 129 (parMsg X) (fun _ => 3131959) :=
  asks_of_B ((asksB_reads 129 (parMsg X) fullMsg _ hc (by show [(_, Wf.messageOf X.Y.k.oneTime.ranges)] = _; rw [hr]; rfl) rfl).trans (asksB_of asks_full_msg))

theorem asks_w {X : Source} (hc : X.Y.k.oneTime.codes = keyFull.codes) (hl : X.Y.k.oneTime.lin = keyFull.once.shape)
    (msg : Array OracleNotice) (hm : linMessageW X.Y.k.oneTime.lin = some msg) : SendAsks 129 (parW X msg) (fun _ => 3138896) := by
  have e : msg = (linMessageW keyFull.once.shape).getD #[] := by rw [← hl, hm]; rfl
  exact asks_of_B ((asksB_reads 129 (parW X msg) fullW _ hc (by show [(_, msg)] = _; rw [e]; rfl) rfl).trans (asksB_of asks_full_w))

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.asksB_reads
#print axioms Johnson.RunOne.KeySendGood.radii_are
#print axioms Johnson.RunOne.KeySendGood.w_there
#print axioms Johnson.RunOne.KeySendGood.one_sampled
#print axioms Johnson.RunOne.KeySendGood.asks_full_idx
#print axioms Johnson.RunOne.KeySendGood.asks_full_msg
#print axioms Johnson.RunOne.KeySendGood.asks_full_w
#print axioms Johnson.RunOne.KeySendGood.below_128_not
#print axioms Johnson.RunOne.KeySendGood.share_not
#print axioms Johnson.RunOne.KeySendGood.asks_idx
#print axioms Johnson.RunOne.KeySendGood.asks_msg
#print axioms Johnson.RunOne.KeySendGood.asks_w
