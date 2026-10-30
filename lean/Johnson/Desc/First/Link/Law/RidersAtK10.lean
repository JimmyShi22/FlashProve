-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RidersAtK10.lean: OF THE PREMISES OF k10_ride
(RidersLight.lean) THREE ARE PAID AT THE WRITTEN FULL LIST AND THE MEANT READERS. Tests with code on
the written list, evaluated by decide +kernel; theorems with their proofs.

  k10At            K10's 25 numbers in the written full list: three behind each segment's batching
  k10Kinds_full    BY THE KERNEL: at these numbers stand places of the kind K10, of segment l
  k10B_full, riders_k10   BY THE KERNEL: **every rider at these 25 is of a sort in lightRider and is
                   not the digits' part**
  light_fails_at_eq   a test that fails, by the kernel: one place in front (the one equation's) a
                   rider is of no sort in lightRider (the segment's rows ride there)
  noWo_fails_at_k10   a second: WITHOUT "wo" the test is FALSE at K10's 25: "wo l" rides at the
                   layers' and the head's segments
  read3_k10        **Read3 𝔇 low (R10 F base)** where the reader of the request and the decoder read
                   the public part alone and the reader of the samples is smpNamed cs seats: the
                   third by k10_smpNamed (Close/Law/OracleAsksK10.lean)
  k10_ride_full    hs at linksFull, the written list and k ∈ k10At, from: hstep · hidx · the three
                   "meant" premises · HeadOpen · lowItem at every rider

ridersAt, rider_mem, notDigitsB, batchIx, plF are FifthTieRiders.lean's.

Limits. THE THREE "MEANT" PREMISES ARE ON A LETTER 𝔇: by report each is by
definition at the closed constant: NOT HELD HERE. HeadOpen and lowItem (the plan's numbers) stay.
Facts on the table at the written full list alone. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.RidersLight
import Johnson.Desc.First.Link.Law.FifthTieRiders
import Johnson.Desc.First.Close.Law.OracleAsksK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start)
open VerifiableInference.Desc.First.Close (K10Step Behind k10_smpNamed)
open Johnson.Desc.First.Walk.Tied
open _root_.Run (ckP)

/-- K10's numbers. -/
def k10At : List ℕ := (List.range 25).map fun l => batchIx l + 3

/-- A test with code: what stands there. -/
def k10KindsB : Bool :=
  (List.range 25).all fun l =>
    (plF[batchIx l + 3]?).any fun p => p.kind == KindName.K10 && p.link == some l

set_option maxRecDepth 1000000 in
theorem k10Kinds_full : k10KindsB = true := by decide +kernel

/-- The test at the 25. -/
def k10B : Bool := k10At.all fun k => (ridersAt k).all fun i => lightRider i && notDigitsB i

set_option maxRecDepth 1000000 in
theorem k10B_full : k10B = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One place in front a rider is of no such sort. -/
theorem light_fails_at_eq : (eqAt.all fun k => (ridersAt k).all lightRider) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Without "wo" the test fails at K10's 25. -/
theorem noWo_fails_at_k10 :
    (k10At.all fun k => (ridersAt k).all fun i => lightRider i && !isWo i) = false := by
  decide +kernel

theorem k10At_le {k : ℕ} (hk : k ∈ k10At) : k ≤ plF.length := by
  rw [length9]
  unfold k10At at hk
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hk
  have hl' : l < 25 := List.mem_range.1 hl
  unfold batchIx
  split <;> omega

/-- **AT K10's 25 PLACES.** -/
theorem riders_k10 {k : ℕ} (hk : k ∈ k10At) {i : Item}
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i)
    (hn : ¬ insQ linksFull plF k i) : lightRider i = true ∧ notOwn ownDigits i := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 k10B_full k hk) i
    (rider_mem (k10At_le hk) ho hn)
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨h1, notOwn_of_B h2⟩

section
variable {Xi Pz Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi Pz Tok rows cols nR X)
  (Mg : Meaning Pz (Wit (CellsQ rows cols) Tok MsgT)) {F : Frame}

/-- **The three readers answer alike over K10's step, at the meant readers.** -/
theorem read3_k10 (low : ℕ → Prop) (base : ℕ)
    (hreq : ∀ z (s s' : S), 𝔇.H.req (z, s) = 𝔇.H.req (z, s'))
    (hdec : ∀ c z (s s' : S), 𝔇.decT c (z, s) = 𝔇.decT c (z, s'))
    {seats : List (ℕ × ℕ)} (hsmp : 𝔇.smp = smpNamed 𝔇.cs seats) :
    Read3 𝔇 low (R10 F base) := by
  refine ⟨fun a y b y' h => ?_, fun a y b y' h c => ?_, fun a y b y' h x _ _ => ?_⟩
  · obtain ⟨za, sa⟩ := a
    obtain ⟨zb, sb⟩ := b
    obtain rfl : zb = za := h.1
    exact hreq _ _ _
  · obtain ⟨za, sa⟩ := a
    obtain ⟨zb, sb⟩ := b
    obtain rfl : zb = za := h.1
    exact hdec _ _ _ _
  · obtain ⟨za, sa⟩ := a
    obtain ⟨zb, sb⟩ := b
    obtain rfl : zb = za := h.1
    rw [hsmp]
    exact (k10_smpNamed 𝔇.cs seats zb h.2.1 x.1 x.2).symm

/-- **hs AT THE WRITTEN FULL LIST AND K10's 25 NUMBERS.** -/
theorem k10_ride_full (Nu : Numbers) (Rch : ℕ → (Pz × S) × F.E.Str → Prop) {k : ℕ}
    (hk : k ∈ k10At) (base : ℕ)
    (q₀ : Piece (ckP .two) F (Pz × S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, q₀.ior.red.out a τ = some b →
      b.1.1 = a.1.1 ∧ K10Step a.1.2 b.1.2 ∧ Behind F base (strsOf F a.2) (strsOf F b.2))
    (hidx : ∀ a, onQ Nu (mgAll 𝔇 Mg) linksFull plF (fun a => a) k a → Rch k a → IndexFree a.1.2)
    (hreq : ∀ z (s s' : S), 𝔇.H.req (z, s) = 𝔇.H.req (z, s'))
    (hdec : ∀ c z (s s' : S), 𝔇.decT c (z, s) = 𝔇.decT c (z, s'))
    {seats : List (ℕ × ℕ)} (hsmp : 𝔇.smp = smpNamed 𝔇.cs seats)
    (hH : HeadOpen 𝔇 (fun i => openAfter (insQ linksFull plF) (outsQ linksFull plF)
      (· ∈ start linksFull) k i ∧ ¬ insQ linksFull plF k i) (R10 F base))
    (hlow : ∀ i, openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i →
      ¬ insQ linksFull plF k i → lowItem Nu (· < base) i) :
    ∀ a τ b w i, onQ Nu (mgAll 𝔇 Mg) linksFull plF (fun a => a) k a → Rch k a →
      a.1.2.failed = none → q₀.ior.red.out a τ = some b →
      onQ Nu (mgAll 𝔇 Mg) linksFull plF (fun a => a) (k + 1) b →
      openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i →
      ¬ insQ linksFull plF k i →
      meansQ Nu (mgAll 𝔇 Mg) (fun a => a) i b w → meansQ Nu (mgAll 𝔇 Mg) (fun a => a) i a w :=
  k10_ride 𝔇 Mg Nu linksFull plF Rch k base q₀ hstep hidx
    (read3_k10 𝔇 (· < base) base hreq hdec hsmp) hH
    (fun i ho hn => ⟨(riders_k10 hk ho hn).1, (riders_k10 hk ho hn).2, hlow i ho hn⟩)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k10Kinds_full
#print axioms VerifiableInference.Desc.LinkJoin.k10B_full
#print axioms VerifiableInference.Desc.LinkJoin.light_fails_at_eq
#print axioms VerifiableInference.Desc.LinkJoin.noWo_fails_at_k10
#print axioms VerifiableInference.Desc.LinkJoin.riders_k10
#print axioms VerifiableInference.Desc.LinkJoin.read3_k10
#print axioms VerifiableInference.Desc.LinkJoin.k10_ride_full
