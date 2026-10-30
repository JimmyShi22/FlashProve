-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RoundsLit.lean: the row K01_rounds' clause "Err.Below e (2⁻¹ ^ 128) at its own
stretch", at all 119 written sendings of the seven plans at the full size (46 at the small one): at
every place with a record's codes and messages the written errors of the sending's piece, at the
kind's own count errPort at the record's radii, are shares of at most 2^-128 of the written
challenges.

A joint of the following files. Johnson/Desc/K1/Law/CondRow.lean and CondLit.lean: at every place P
with a record's codes and messages: condPort P (radFrom P r.l) and sampledList P (radFrom P r.l) =
r.l. K1/Law/LitPow.lean: seeds_one; pow_full | pow_small: at
every place whose codes and sampled list are an element of the written list, at one seed: the
comparison of natural numbers at 128, by one evaluation in Lean's kernel over the whole list.
K1/Law/PowB.lean: errPort_eNat: errPort is the computed number eNat; powB_send | powB_open: from the
comparison: Err.Below of the piece's errors.
  pack_full, pack_small: each record's codes and sampled list are an element of PackLit's list:
      evaluations in Lean's kernel (decide +kernel)
  PaidAt P rad: condPort, one seed, errPort P rad = eNat P rad, powB P rad 128, and Err.Below at
      2^-128 of sendPiece's and of openPiece's errors at the count errPort P rad, at every written
      round of seeds with the place's own entry
  paid_of: from condPort, the codes and the sampled list
  k01_rounds_full, k01_rounds_small: at every record and every place with its codes and messages
  paid_of_placeOk, paid_key_at_scope: so at every place that is tied to a record; all nineteen of a
      key file at every three public files in the scope of the goals
  K01RoundsStatement, k01RoundsStatement: as one closed proposition, at the full size

HOW MANY BITS ARE WORK, as the row asks: no work: the comparison holds without the place's bits of
work; where a place bears some, they come on top.

What is not claimed. That the written sendings are the parameters at a description's own places
(K01_sits). One count a round. The round behind the seeds draws nothing. A sending whose answers
ride in a later round of another kind: openPiece's form covers the piece; what that later round
draws is the other kind's. What the heads of the files named do not claim. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K01KeyAt
import Johnson.Desc.K1.Law.LitPow
import Johnson.Desc.K1.Law.PowB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open Johnson.G (packFullLit packSmallLit sendsFullLit)
open scoped ENNReal

theorem pack_full : (litFull.all fun r => decide ((r.cs, r.l) ∈ packFullLit)) = true := by
  decide +kernel

theorem pack_small : (litSmall.all fun r => decide ((r.cs, r.l) ∈ packSmallLit)) = true := by
  decide +kernel

/-- **What is had at a place and radii.** -/
def PaidAt (P : Par) (rad : Nat → Nat) : Prop :=
  condPort P rad = true ∧ P.seeds = 1 ∧ errPort P rad = eNat P rad ∧ powB P rad 128 = true ∧
  (∀ (T Cl W : Type) (F : Frame) (b : Block T Cl) (base : Nat) (d₁ d₂ : RDT),
    d₁.entry = seedEntry P → d₁.kind = .seeds →
      Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates (errPort P rad)).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128)) ∧
  ∀ (T Cl W : Type) (F : Frame) (b : Block T Cl) (base : Nat) (d₁ : RDT) (ds : List RDT)
    (back : List Fmt.RoundView), d₁.entry = seedEntry P → d₁.kind = .seeds →
      Err.Below (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates (errPort P rad)).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem paid_of (P : Par) (rad : Nat → Nat) (hc : condPort P rad = true)
    (hp : PowAt P rad 128) : PaidAt P rad := by
  have h1 := seeds_one P rad hc
  have hb : powB P rad 128 = true := decide_eq_true hp
  exact ⟨hc, h1, errPort_eNat P h1 rad, hb,
    fun T Cl W F b base d₁ d₂ he hk => powB_send P h1 rad 128 hb b base d₁ d₂ he hk,
    fun T Cl W F b base d₁ ds back he hk => powB_open P h1 rad 128 hb b base d₁ ds back he hk⟩

/-- **At all 119 written sendings of the full size.** -/
theorem k01_rounds_full (r : SendRow) (hr : r ∈ litFull) (P : Par) (hat : r.At P) :
    PaidAt P (radFrom P r.l) := by
  obtain ⟨hc, hl⟩ := ((k01_full r hr).2).1 P hat
  have hx : (r.cs, r.l) ∈ packFullLit := of_decide_eq_true (List.all_eq_true.1 pack_full r hr)
  exact paid_of P _ hc (pow_full P _ (r.cs, r.l) hx hat.1 hl (seeds_one P _ hc))

/-- **At all 46 of the small size.** -/
theorem k01_rounds_small (r : SendRow) (hr : r ∈ litSmall) (P : Par) (hat : r.At P) :
    PaidAt P (radFrom P r.l) := by
  obtain ⟨hc, hl⟩ := ((k01_small r hr).2).1 P hat
  have hx : (r.cs, r.l) ∈ packSmallLit := of_decide_eq_true (List.all_eq_true.1 pack_small r hr)
  exact paid_of P _ hc (pow_small P _ (r.cs, r.l) hx hat.1 hl (seeds_one P _ hc))

/-- **The row K01_rounds' clause on Err.Below**, at the written numbers of the full size. -/
def K01RoundsStatement : Prop :=
  litFull.length = 119 ∧ ∀ r ∈ litFull, ∀ P : Par, r.At P → PaidAt P (radFrom P r.l)

theorem k01RoundsStatement : K01RoundsStatement := ⟨litFull_length, k01_rounds_full⟩

/-! ## At the places that are tied to a record -/

/-- A place that is tied to a record (PlaceOk) is paid at the record's radii. -/
theorem paid_of_placeOk {f c k : Nat} {P : Par} (h : PlaceOk f c k P) :
    ∃ y, (litAt sendsFullLit packFullLit f c)[k]? = some y ∧ PaidAt P (radFrom P y.2.l) := by
  obtain ⟨y, hy, hat, -⟩ := h
  exact ⟨y, hy, k01_rounds_full y.2 (litAt_mem (List.mem_of_getElem? hy)) P hat⟩

/-- **All nineteen sendings of a key file, at every three public files in the scope of the goals**,
from a planner that returns. -/
theorem paid_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    {c k : Nat} (hc : c ∈ [0, 1, 2]) {L : List (List OracleNotice)}
    (hL : keySent p.chains.made.sized.key c = some L) {s : List OracleNotice}
    (hk : L[k]? = some s) (P : Par) (h1 : P.codes = p.chains.made.sized.key.codes)
    (h2 : P.sent.toList = s) :
    ∃ y, (litAt sendsFullLit packFullLit 0 c)[k]? = some y ∧ PaidAt P (radFrom P y.2.l) :=
  paid_of_placeOk (k01_key_at_scope hZ hp hc hL hk P h1 h2)

end VerifiableInference.Desc.K1
