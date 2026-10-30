--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/RoundsWritten.lean: the rounds "RNG" of the smallness test's first half: THE
WRITTEN ERROR AT EXACT INTEGERS: at every place the written count is a share of at most 2⁻¹ ^ (the
place's number of combinations) of the written round's verifier messages, with no work and with the
sampler's weight counted; and at each of the 25 rounds "RNG" of the library's written list of the
full-size proof file's first chain it is a share of at most 2⁻¹ ^ 128.

LawRounds.lean holds the proved block's error against the price that the planner books. Here nothing
of the planner is evaluated. The block's error is a number by definition: `eps Λ` is card (Dr s) / 2
^ s.tau (Cb/Pv/Tail/Block.lean). A written round that draws matrix entries alone has just card (Dr
s) typed values, and its sampler has no bias to price (`Run.exAll` is 0). So the bound holds with
room 0. Definitions, and theorems with their proofs.

Main names:
  `typed_le`: the typed count is at most 2⁻¹ ^ s.tau of the written round's typed values.
  `rng_below`: one written round that draws the matrix's entries alone and asks no work: the typed
    count times the sampler's weight is at most 2⁻¹ ^ s.tau of the written verifier messages
    (`below_round_div_ex`, OnBytes/Slice/RatesEx.lean).
  `rngMaps`: ONE NAMED READING of such a round (`Maps`, OnBytes/Flat/CarrySMaps.lean): the prover's
    message goes to the empty message, the typed values to the matrix (`matOf`,
    OnBytes/Tie/Pv/Tail/CarryRng.lean). `rngMaps_ok`, `rngMaps_heldEx`: it is in order, and
    `Maps.HeldEx` (Johnson/Flat/ReadingEx.lean) holds of it at 2⁻¹ ^ s.tau.
  `entry_at`, `only_at`: under `AtWritten` (Member.lean) a written round with x's entry and kind
    asks no work and draws just s.columns * s.tau matrix entries.
  `K08Written`, `k08Written`: the closed statement at the written rounds; its proof.
  `K08WrittenMember`, `k08WrittenMember`: at two settings, for each of the three sorts of size, its
    premises are met together.

Limits. A BOUND ON A COUNT: that the count bounds a prover's chance is the block's own law
(`HoleAt`, Cb/Pv/Tail/Block.lean; `block_good`, Law.lean). IT PRICES ONE ROUND OF ONE REQUEST: no
sum over the 25 rounds, none over several requests. THE ROUND PINS THE PRODUCT columns * tau ALONE
(`place_half_tau`, MemberTeeth.lean): the level 128 comes from the premise that the setting gives
128 combinations, with `AtWritten.tau`; the setting is a letter under that equation; it holds at the
default setting (`default_combinations`) and at the library's written setting `keySet`
(`keySet_combinations`), which is the setting of the written records of the code switch
(Johnson/G/SwitchPricesLit.lean: `setLit`); that a made plan's setting is that one is not shown.
That the written list is what the planner makes of the public files is not shown (the list's own
head). That a file's chain has such a written round at this kind's place is not shown. The member is
made up in all that the round does not pin (`madeUpPar`, the sizes `sizeAt`, the library's letters
`symL`, at the one field Cb.Gl.E). `OnlyTrits` is a proposition, so the reading `rngMaps s d h` does
not hang on which h is given. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Desc.First.K8.Member
import Johnson.Desc.First.K8.LawRounds
import OnBytes.Flat.CountsHeld
import Johnson.Flat.ReadingEx
import OnBytes.Tie.Pv.Tail.RngView
import Cb.Pv.Tail.InLink
import OnBytes.Tie.Pv.KeyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member
open VerifiableInference.Number (isSmall)
open VerifiableInference.Number.Written (written_shape)
open OnBytes.Params (Setting rngCombinations)
open Johnson.G (dryProofFull)
open Iop Prob Cb.Pv.Tail OnBytes OnBytes.Slice OnBytes.Maker OnBytes.Flat OnBytes.G4
  OnBytes.Tie.Pv.Tail
open _root_.Run (PQ.RD ckP Vals exAll bsRound)
open _root_.Run.PQ (uL)
open scoped ENNReal

/-! ### One round, at every size -/

theorem card_Dr (s : Size) : Fintype.card (Dr s) = 4 ^ (s.columns * s.tau) :=
  card_drawn (Dr s) (smallOf s default) ⟨flatPort s⟩

/-- **The typed count is at most 2⁻¹ ^ tau of the written round's typed values.** -/
theorem typed_le (s : Size) (d : PQ.RD) (h : OnlyTrits d (s.columns * s.tau)) :
    ((Fintype.card (Dr s) / 2 ^ s.tau : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ s.tau * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) := by
  have hN : Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) = Fintype.card (Dr s) := by
    rw [card_vals_all, h, card_Dr]
    simp [nVals]
  rw [hN]
  have h1 : Fintype.card (Dr s) / 2 ^ s.tau * 2 ^ s.tau ≤ Fintype.card (Dr s) :=
    Nat.div_mul_le_self _ _
  have h2 : ((Fintype.card (Dr s) / 2 ^ s.tau : ℕ) : ℝ≥0∞) * 2 ^ s.tau ≤
      (Fintype.card (Dr s) : ℝ≥0∞) := by exact_mod_cast h1
  calc ((Fintype.card (Dr s) / 2 ^ s.tau : ℕ) : ℝ≥0∞)
      = ((Fintype.card (Dr s) / 2 ^ s.tau : ℕ) : ℝ≥0∞) * 2 ^ s.tau * (2 : ℝ≥0∞)⁻¹ ^ s.tau := by
        rw [mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow,
          mul_one]
    _ ≤ (Fintype.card (Dr s) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ s.tau := mul_le_mul' h2 le_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ s.tau * (Fintype.card (Dr s) : ℝ≥0∞) := mul_comm _ _

/-- What the bias and the work make of the share: nothing. -/
theorem price_eq (d : PQ.RD) {n : ℕ} (h : OnlyTrits d n) (hw : d.entry.work = 0) (c : ℝ≥0∞) :
    kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) = c := by
  have e : exAll (Fmt.dsOf d.entry d.kind) = 0 := by
    rw [h]
    rfl
  rw [e, hw, pow_zero, pow_zero, one_mul, div_one]

/-- **One written round.** -/
theorem rng_below (s : Size) (d : PQ.RD) (h : OnlyTrits d (s.columns * s.tau))
    (hw : d.entry.work = 0) (hlog : d.entry.logN ≤ 64) :
    ((Fintype.card (Dr s) / 2 ^ s.tau * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ s.tau * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have b := below_round_div_ex d hlog _ _ (typed_le s d h)
  rw [price_eq d h hw] at b
  exact b

/-- The reading of a written round that draws a matrix's entries alone: the prover's message goes to
the empty message; the typed values go to the matrix (`matOf`). -/
def rngMaps (s : Size) (d : RDT) (h : OnlyTrits (toRD d) (s.columns * s.tau)) :
    Maps [d] [IOR.drawRound (Dr s)] :=
  .step ⟨fun _ => ((), ()), matOf s (toRD d) h⟩ .nil

theorem rngMaps_ok (s : Size) (d : RDT) (h : OnlyTrits (toRD d) (s.columns * s.tau))
    (hlog : d.entry.logN ≤ 64) : (rngMaps s d h).OK :=
  ⟨⟨matOf_inj s (toRD d) h, hlog⟩, trivial⟩

theorem rngMaps_heldEx {K : Type} {s : Size} (Λ : Letters K s) (d : RDT)
    (h : OnlyTrits (toRD d) (s.columns * s.tau)) (hw : d.entry.work = 0) :
    (rngMaps s d h).HeldEx ((2 : ℝ≥0∞)⁻¹ ^ s.tau) (eps Λ) :=
  ⟨⟨(2 : ℝ≥0∞)⁻¹ ^ s.tau, typed_le s (toRD d) h, le_of_eq (price_eq (toRD d) h hw _)⟩, trivial⟩

/-! ### At the written rounds -/

/-- Under `AtWritten`: x's entry, written out. -/
theorem entry_at {st : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored} (A : AtWritten st p x) :
    x.1.entry = { name := "RNG", trits := columns p * p.tau } ∧ x.1.kind = .entries := by
  obtain ⟨a, b, -⟩ := written_shape A.mem A.small
  have e : x.1.entry = { name := "RNG", trits := x.1.entry.trits } := a
  rw [A.columns]
  exact ⟨e, b⟩

/-- A written round with x's entry and kind draws just the sizes' matrix entries. -/
theorem only_at {st : Setting} {p : Par} {x : Fmt.Round × List Fmt.Stored} (A : AtWritten st p x)
    {s : Size} (hf : Fits p s) (d : PQ.RD) (he : d.entry = x.1.entry) (hk : d.kind = x.1.kind) :
    OnlyTrits d (s.columns * s.tau) ∧ d.entry.work = 0 ∧ d.entry.logN ≤ 64 := by
  obtain ⟨e, k⟩ := entry_at A
  have e' : d.entry = { name := "RNG", trits := columns p * p.tau } := he.trans e
  have o := onlyTrits_of d (by rw [e']) (by rw [e']) (by rw [e']) (hk.trans k)
  rw [e'] at o
  rw [columns_eq hf, hf.tau]
  exact ⟨o, by rw [e'], by rw [e']; exact Nat.zero_le _⟩

/-- **The rounds "RNG" of the written first chain: the written error, at exact integers.** -/
def K08Written : Prop :=
  ∀ (st : Setting), rngCombinations st .request = 128 →
  ∀ (x : Fmt.Round × List Fmt.Stored) (p : Par), AtWritten st p x →
  ∀ (K : Type) (s : Size), Fits p s → ∀ (Λ : Letters K s),
    x.1.entry.work = 0 ∧
    ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [x.1.entry] ∧
    (∀ d : PQ.RD, d.entry = x.1.entry → d.kind = x.1.kind →
      Err.Below (Held.cnts (uL (ckP .two) [d]) (Held.wsOf [d] [true]) (R Λ).shape (eps Λ))
        ((2 : ℝ≥0∞)⁻¹ ^ 128)) ∧
    ∀ d : RDT, d.entry = x.1.entry → d.kind = x.1.kind →
      ∃ h : OnlyTrits (toRD d) (s.columns * s.tau),
        (rngMaps s d h).OK ∧ (rngMaps s d h).HeldEx ((2 : ℝ≥0∞)⁻¹ ^ 128) (eps Λ) ∧
          (rngMaps s d h).carry.Fits (eps Λ) ((rngMaps s d h).err (eps Λ)) ∧
          Err.Below ((rngMaps s d h).err (eps Λ)) ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- **A member**, at the default setting and at the library's written setting `keySet`
(OnBytes/Tie/Pv/KeyStages.lean), for each of the three sorts of size. -/
def K08WrittenMember : Prop :=
  ∀ st ∈ [({} : Setting), Cb.Pv.Tower.keySet], ∀ n ∈ [3083008, 1311744, 2649984],
    ∃ (x : Fmt.Round × List Fmt.Stored) (p : Par) (s : Size),
      x.1.entry.trits = n ∧ rngCombinations st .request = 128 ∧ AtWritten st p x ∧ Fits p s ∧
        Nonempty (Letters Cb.Gl.E s) ∧ (∃ d : PQ.RD, d.entry = x.1.entry ∧ d.kind = x.1.kind) ∧
        ∃ d : RDT, d.entry = x.1.entry ∧ d.kind = x.1.kind

theorem k08Written : K08Written := by
  intro st h128 x p A K s hf Λ
  have ht : s.tau = 128 := (hf.tau.trans A.tau).trans h128
  have hp : (2 : ℝ≥0∞)⁻¹ ^ s.tau = (2 : ℝ≥0∞)⁻¹ ^ 128 := by rw [ht]
  obtain ⟨e, -⟩ := entry_at A
  refine ⟨by rw [e], ?_, ?_, ?_⟩
  · have hS : ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(rngRound {} (smallOf s default)).entry] :=
      List.Forall₂.cons (rngIs_toAll Cb.Gl.E Cb.Gl.F (round_is _ _ ⟨flatPort s⟩ {}))
        List.Forall₂.nil
    have e2 : (rngRound {} (smallOf s default)).entry = x.1.entry := by
      rw [e, ← columns_eq hf, ← hf.tau]
      rfl
    rw [e2] at hS
    exact hS
  · intro d he hk
    obtain ⟨o, hw, hl⟩ := only_at A hf d he hk
    have b := rng_below s d o hw hl
    rw [hp] at b
    exact ⟨b, trivial⟩
  · intro d he hk
    obtain ⟨o, hw, hl⟩ := only_at A hf (toRD d) he hk
    have ok := rngMaps_ok s d o hl
    have hx := rngMaps_heldEx Λ d o hw
    rw [hp] at hx
    exact ⟨o, ok, hx, (rngMaps s d o).fits ok (eps Λ), (rngMaps s d o).below_err_ex ok (eps Λ) hx⟩

/-- The library's written setting gives 128 combinations. -/
theorem keySet_combinations : rngCombinations Cb.Pv.Tower.keySet .request = 128 := by decide

/-- Sizes of which `sizeAt` keeps nothing that the round reads. -/
def restSize : Size := ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0⟩

theorem k08WrittenMember : K08WrittenMember := by
  intro st hst n hn
  have h128 : rngCombinations st .request = 128 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl
    · exact default_combinations
    · exact keySet_combinations
  have hb : settingB st = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl
    · exact default_setting
    · decide
  obtain ⟨x, e, A, -⟩ := exists_both hb hn
  exact ⟨x, madeUpPar (n / 128 - 1), sizeAt _ restSize, e, h128, A, fits_sizeAt _ restSize,
    ⟨symL Cb.Gl.E _⟩,
    ⟨⟨x.1.entry, x.1.kind, [], none, []⟩, rfl, rfl⟩,
    ⟨⟨⟨x.1.entry, x.1.kind, [], [], []⟩, []⟩, rfl, rfl⟩⟩

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.rng_below
#print axioms VerifiableInference.Desc.First.K8.Member.rngMaps_heldEx
#print axioms VerifiableInference.Desc.First.K8.Member.k08Written
#print axioms VerifiableInference.Desc.First.K8.Member.k08WrittenMember
