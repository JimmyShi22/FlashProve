-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/SeedBS.lean: A WIRE OF THE RECORD (OutOfDomainSampleQueryLayout, Cms.lean) WITH S.OK AND S.Law EXISTS AT
EVERY OBJECT WITH RECORDS whose three shapes are not empty and whose records are countable.
  OutOfDomainSampleQueryLayout.ofBS, seedLaw_ofBS: from a sampler of the library's kind (Iop.BS: φ on b blocks, w bounds
    its fibres) that is Good κ' (Iop/Draw.lean:134):
    the law holds at κ' · c as soon as the record clause's count eR is at most c · |OutOfDomainSeed|.
  bsSeed, bsSeed_good: such a sampler for ANY finite set of seeds: the binary value of k blocks
    modulo |OutOfDomainSeed|, read as a seed through a numbering
    (BS.modN, BS.map): Good (1 + 2^-e) if |OutOfDomainSeed| · 2^e ≤ 2^(lam k).
  exists_seedW: the two together, with an injective code and fixed plain parts.
DECLARED: THIS IS AN EXISTENCE. bsSeed is not the programs' way of drawing a seed (coordinate by
coordinate); the code of exists_code writes the number of a record IN UNARY (a list of that many
zero digests): lawful for S.OK, of no use to a program. Both can be replaced by any other sampler
that is Good and any other injective code: the theorems take them as letters.

-/
import Johnson.RecCompile.Wire
import Iop.DrawProofs

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}

/-- The wire of the record from a sampler of the library's kind: the seed is φ of the first b of the
K blocks. -/
def OutOfDomainSampleQueryLayout.ofBS [decS : DecidableEq L.OutOfDomainSeed] (K : ℕ) (bs : BS lam L.OutOfDomainSeed) (t0 t1 : Tag)
    (pl : (t : Tag) → PlainPart (shapeOf L.carrierC t) (annOf L.carrierC t))
    (code : L.Rec → List (Dig lam)) : OutOfDomainSampleQueryLayout lam K L :=
  ⟨t0, t1, pl, fun u => bs.φ (firstBlocks lam K bs.b u), code, decS⟩

theorem seedLaw_ofBS [DecidableEq L.OutOfDomainSeed] {K : ℕ} {bs : BS lam L.OutOfDomainSeed} {κ' c : ℝ≥0∞} (hg : bs.Good κ') (hK : bs.b ≤ K)
    (t0 t1 : Tag) (pl : (t : Tag) → PlainPart (shapeOf L.carrierC t) (annOf L.carrierC t))
    (code : L.Rec → List (Dig lam)) {eR : ℕ} (hrcd : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (h : (eR : ℝ≥0∞) ≤ c * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞)) :
    (OutOfDomainSampleQueryLayout.ofBS K bs t0 t1 pl code).Law (κ' * c) := by
  intro y
  have h1 : pr (unif (Fin K → Dig lam)) {a | L.hasCollisionAt y (bs.φ (firstBlocks lam K bs.b a))} =
      pr ((unif (Fin K → Dig lam)).map (firstBlocks lam K bs.b)) {a | L.hasCollisionAt y (bs.φ a)} := by
    rw [pr_map]; rfl
  show pr (unif (Fin K → Dig lam)) {a | L.hasCollisionAt y (bs.φ (firstBlocks lam K bs.b a))} ≤ κ' * c
  rw [h1, show (unif (Fin K → Dig lam)).map (firstBlocks lam K bs.b) = unif (Fin bs.b → Dig lam)
    from map_firstBlocks_unif (Dig lam) (fun _ => false) bs.b K hK]
  refine (pr_unif_le_iff _ _).2 ?_
  have hr := hg.ratio
  rw [Nat.card_eq_fintype_card] at hr
  calc
    ((cnt fun a => L.hasCollisionAt y (bs.φ a) : ℕ) : ℝ≥0∞) ≤
        ((cnt (fun s => L.hasCollisionAt y s) * bs.w : ℕ) : ℝ≥0∞) :=
      Nat.cast_le.2 (cnt_comp_le bs.φ hg.fib fun s => L.hasCollisionAt y s)
    _ ≤ ((eR * bs.w : ℕ) : ℝ≥0∞) := Nat.cast_le.2 (Nat.mul_le_mul_right _ (hrcd y))
    _ = (eR : ℝ≥0∞) * (bs.w : ℝ≥0∞) := by push_cast; rfl
    _ ≤ c * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞) * (bs.w : ℝ≥0∞) := mul_le_mul' h le_rfl
    _ = c * ((bs.w : ℝ≥0∞) * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞)) := by ring
    _ ≤ c * (κ' * (Fintype.card (Fin bs.b → Dig lam) : ℝ≥0∞)) := mul_le_mul' le_rfl hr
    _ = κ' * c * (Fintype.card (Fin bs.b → Dig lam) : ℝ≥0∞) := by ring

/-- A sampler for any finite set of seeds: the value of k blocks modulo the number of seeds. -/
def bsSeed (lam : ℕ) (L : HolographicProtocol I X) (k : ℕ) : BS lam L.OutOfDomainSeed :=
  (BS.modN lam (Fintype.card L.OutOfDomainSeed) k Fintype.card_pos).map (Fintype.equivFin L.OutOfDomainSeed).symm

theorem bsSeed_good (L : HolographicProtocol I X) (k e : ℕ) (he : Fintype.card L.OutOfDomainSeed * 2 ^ e ≤ 2 ^ (lam * k)) :
    (bsSeed lam L k).Good (1 + (2 ^ e : ℝ≥0∞)⁻¹) :=
  BS.map_good _ (BS.modN_good lam _ k Fintype.card_pos e he)

theorem exists_code (lam : ℕ) (α : Type) [Countable α] :
    ∃ code : α → List (Dig lam), Function.Injective code := by
  obtain ⟨f, hf⟩ := exists_injective_nat α
  exact ⟨fun r => List.replicate (f r) default, fun a b h =>
    hf (by simpa using congrArg List.length h)⟩

/-- a fixed plain part of a shape that is not empty -/
def pbDflt : (s : Shape) → (A : RoundSplits s) → s ≠ [] → PlainPart s A
  | [], _, h => absurd rfl h
  | r :: _, (a, _), _ => .inl (.inl (a.plain r.dPlain).1)

/-- A wire of the record with S.OK and S.Law exists. -/
theorem exists_seedW (L : HolographicProtocol I X) [Countable L.Rec] (hT : L.offline.shape ≠ [])
    (hL : L.link.shape ≠ []) (hB : L.onlineBatch.loc.shape ≠ []) (K k e eR : ℕ) (c : ℝ≥0∞) (hk : k ≤ K)
    (he : Fintype.card L.OutOfDomainSeed * 2 ^ e ≤ 2 ^ (lam * k))
    (hrcd : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (h : (eR : ℝ≥0∞) ≤ c * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞)) :
    ∃ S : OutOfDomainSampleQueryLayout lam K L, S.OK ∧ S.Law ((1 + (2 ^ e : ℝ≥0∞)⁻¹) * c) := by
  classical
  obtain ⟨code, hc⟩ := exists_code lam L.Rec
  let pl : (t : Tag) → PlainPart (shapeOf L.carrierC t) (annOf L.carrierC t) := fun t =>
    match t with
    | .test => pbDflt _ _ hT
    | .link => pbDflt _ _ hL
    | .onl => pbDflt _ _ hB
  exact ⟨OutOfDomainSampleQueryLayout.ofBS K (bsSeed lam L k) .onl .test pl code, ⟨hc⟩,
    seedLaw_ofBS (bsSeed_good L k e he) hk .onl .test pl code hrcd h⟩

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.exists_seedW
