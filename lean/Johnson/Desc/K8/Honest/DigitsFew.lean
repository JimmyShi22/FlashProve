-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DigitsFew.lean: THE SMALLNESS TEST: THE COUNT FOR ITS TEST `selfDigits` ("no
digit's weight on the pieces' rows of the digits' array is 0":
Johnson/Desc/First/TailClaims/SelfTests.lean). Definitions with code, a statement and its proof. No
prover. Lemmas; none of the library's goals.

ZZ: the digits' array. nb: the number of blocks of its rows; mz: the rows of cells of all matrices.
The test asks the entries 0 .. mz - 1 of row b and mz .. 2 mz - 1 of row nb + b, b < nb. The first
of the first four claims of "K8.equations" lays its runs there (K9L.four8,
Johnson/Desc/First/Batch/Law/K8Four.lean). The reads' row is 2 nb and the ties' row 2 nb + 1: so the
ties and reads lay nothing on these rows.
  `digitsLaid tl F`   with code, on public numbers and the arrays' frame: ZZ is no matrix's array of
      symbols and not what a read's vector's array reads as; each row nb + b begins at column 0
  `digitsLive tl`   with code, ON WHAT THE LOOKUP HAS HEARD, in front of the batching: at every
      entry that the test asks the first of the four claims has a coefficient other than 0
      (`liveAt`, Johnson/Desc/K8/Honest/CoefCode.lean)
  `digitsNo s`   the state holds data and a ledger at which `selfDigits` says no
  **`digits_few`**   IF both tests say yes, g meets `Gathers` at s and the plan's number of claims
      is at most d + 1: THEN at most 2 * (nb * mz) * d field elements are challenges at which batch
      says yes and, behind it, `selfDigits` says no
By: `entries_few` (EntriesFew.lean) · `noneZero_no`, `live_ne` (CoefCode.lean).
Limits. `digitsLive` IS A PREMISE ON CHALLENGES DRAWN IN FRONT: how often it fails is counted
nowhere here. `Gathers` and `digitsLaid` are premises. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.EntriesFew
import Johnson.Desc.K8.Honest.CoefCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- On public numbers and the arrays' frame. -/
def digitsLaid (tl : HTailF2) (F : Fork) : Bool :=
  ((List.range tl.NM).all fun mu => tl.gtTree.getD mu 0 != tl.ix.ZZ) &&
    (tl.ix.U.getD 0 none).getD 0 != tl.ix.ZZ && (tl.ix.U.getD 2 none).getD 0 != tl.ix.ZZ &&
    (List.range tl.zzBlocks).all fun b =>
      ((F.trees.getD tl.ix.ZZ {}).rows.getD (tl.zzBlocks + b) {}).L0 == 0

/-- On what the lookup has heard. -/
def digitsLive (tl : HTailF2) : Bool :=
  match tl.heard with
  | some g =>
    (List.range tl.zzBlocks).all fun b => (List.range tl.mz).all fun u =>
      ((K9L.four8 tl g)[0]?).any fun cl =>
        liveAt cl tl.ix.ZZ b u && liveAt cl tl.ix.ZZ (tl.zzBlocks + b) (tl.mz + u)
  | none => false

/-- `selfDigits` says no at the state. -/
def digitsNo (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => !selfDigits q.1 q.2
  | none => false

/-- The entries that the test asks. -/
def digitsEn (nb mz : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range nb ×ˢ Finset.range mz) ∪
    (Finset.range nb ×ˢ Finset.range mz).image fun e => (nb + e.1, mz + e.2)

theorem digitsEn_card (nb mz : ℕ) : (digitsEn nb mz).card ≤ 2 * (nb * mz) := by
  unfold digitsEn
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.range nb ×ˢ Finset.range mz).card = nb * mz := by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  have h2 := Finset.card_image_le (s := Finset.range nb ×ˢ Finset.range mz)
    (f := fun e : ℕ × ℕ => (nb + e.1, mz + e.2))
  omega

/-- **The count.** -/
theorem digits_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hP : digitsLaid tl F = true)
    (hL : digitsLive tl = true) (hG : Gathers p g s tl funs nf nb a)
    (hd : F.planClaimsF ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch digitsNo s [chiAt x] = true) ≤
      2 * (tl.zzBlocks * tl.mz) * d := by
  simp only [digitsLaid, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hP
  obtain ⟨⟨⟨p2, p3⟩, p4⟩, p5⟩ := hP
  have hrow : ∀ e ∈ digitsEn tl.zzBlocks tl.mz, e.1 < 2 * tl.zzBlocks := by
    intro e he
    unfold digitsEn at he
    rcases Finset.mem_union.1 he with h | h
    · have := Finset.mem_range.1 (Finset.mem_product.1 h).1
      omega
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 h
      have := Finset.mem_range.1 (Finset.mem_product.1 he').1
      show tl.zzBlocks + e'.1 < _
      omega
  have hoff : ∀ e ∈ digitsEn tl.zzBlocks tl.mz, OffAt tl tl.ix.ZZ e.1 := fun e he =>
    ⟨fun h => by
        have h1 := hrow e he
        have h2 : 2 * tl.zzBlocks + 1 = e.1 := h.2
        omega,
      fun h => by
        have h1 := hrow e he
        have h2 : 2 * tl.zzBlocks = e.1 := h.2
        omega,
      fun mu hmu h => p2 mu hmu h.1, p3, p4⟩
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch digitsNo s [chiAt x] = true
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₁ := hx₀
    unfold askBehind at hx₁
    simp only [List.map_cons, List.map_nil] at hx₁
    cases hbt : batch s [⟨[], chiAt x₀⟩] with
    | error e =>
      rw [hbt] at hx₁
      exact absurd hx₁ (by simp)
    | ok t' =>
      obtain ⟨-, -, g₀, -, -, hg₀, -, -, h4, -⟩ :=
        behind_plain p g batch s t' tl F funs nf nb a hb hs hG x₀ hbt
      refine (entries_few p g batch s tl F funs nf nb d a hb hs hG tl.ix.ZZ
        (digitsEn tl.zzBlocks tl.mz) digitsNo hoff ?_ ?_ ?_ hd).trans
        (Nat.mul_le_mul_right d (digitsEn_card _ _))
      · intro t'' tl' G h1 heq hno
        obtain ⟨n₀, F₁, F₂, k8, geq⟩ := heq
        have hix : tl'.ix = tl.ix :=
          eq_same (fun u : HTailF2 => u.ix) geq (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        have hbl : tl'.zzBlocks = tl.zzBlocks :=
          eq_same (fun u : HTailF2 => u.zzBlocks) geq (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        have hmz : tl'.mz = tl.mz :=
          eq_same (fun u : HTailF2 => u.mz) geq (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        unfold digitsNo at hno
        rw [h1] at hno
        have hno' : selfDigits tl' G = false := by simpa using hno
        unfold selfDigits at hno'
        obtain ⟨b, hb', hr'⟩ := List.all_eq_false.1 hno'
        rw [hbl] at hb'
        rw [hix, hbl, hmz] at hr'
        have hb'' := List.mem_range.1 hb'
        have hr'' : (noneZero (weightsOf G tl.ix.ZZ b) 0 tl.mz &&
            noneZero (weightsOf G tl.ix.ZZ (tl.zzBlocks + b)) tl.mz tl.mz) = false := by
          simpa using hr'
        rcases Bool.and_eq_false_iff.1 hr'' with h | h
        · obtain ⟨u, hu, hz⟩ := noneZero_no _ 0 _ (Or.inl (Nat.zero_le _)) h
          rw [Nat.zero_add] at hz
          exact ⟨(b, u), Finset.mem_union_left _ (Finset.mem_product.2
            ⟨Finset.mem_range.2 hb'', Finset.mem_range.2 hu⟩), hz⟩
        · have hfn : tl.mz ≤ (weightsOf G tl.ix.ZZ (tl.zzBlocks + b)).size ∨ 0 < tl.mz := by
            rcases Nat.eq_zero_or_pos tl.mz with h0 | h0
            · left
              rw [h0]
              exact Nat.zero_le _
            · exact Or.inr h0
          obtain ⟨u, hu, hz⟩ := noneZero_no _ _ _ hfn h
          exact ⟨(tl.zzBlocks + b, tl.mz + u), Finset.mem_union_right _ (Finset.mem_image.2
            ⟨(b, u), Finset.mem_product.2 ⟨Finset.mem_range.2 hb'', Finset.mem_range.2 hu⟩,
              rfl⟩), hz⟩
      · intro e he
        unfold digitsEn at he
        rcases Finset.mem_union.1 he with h | h
        · right
          obtain ⟨h1, h2⟩ := Finset.mem_product.1 h
          exact Finset.mem_union_left _ (Finset.mem_product.2 ⟨h1, Finset.mem_range.2
            (Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.1 h2))⟩)
        · left
          obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 h
          exact p5 e'.1 (Finset.mem_range.1 (Finset.mem_product.1 he').1)
      · intro e he
        unfold digitsLive at hL
        rw [hg₀] at hL
        simp only [List.all_eq_true, List.mem_range] at hL
        refine ⟨nf + 0, by omega, ?_⟩
        unfold digitsEn at he
        cases hcl : (K9L.four8 tl g₀)[0]? with
        | none =>
          exfalso
          rcases Finset.mem_union.1 he with h | h
          · obtain ⟨h1, h2⟩ := Finset.mem_product.1 h
            have h5 := hL e.1 (Finset.mem_range.1 h1) e.2 (Finset.mem_range.1 h2)
            rw [hcl] at h5
            cases h5
          · obtain ⟨e', he', -⟩ := Finset.mem_image.1 h
            obtain ⟨h1, h2⟩ := Finset.mem_product.1 he'
            have h5 := hL e'.1 (Finset.mem_range.1 h1) e'.2 (Finset.mem_range.1 h2)
            rw [hcl] at h5
            cases h5
        | some cl =>
          rw [h4 0 cl hcl]
          rcases Finset.mem_union.1 he with h | h
          · obtain ⟨h1, h2⟩ := Finset.mem_product.1 h
            have h5 := hL e.1 (Finset.mem_range.1 h1) e.2 (Finset.mem_range.1 h2)
            rw [hcl, Option.any_some, Bool.and_eq_true] at h5
            exact live_ne cl tl.ix.ZZ e.1 e.2 h5.1
          · obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 h
            obtain ⟨h1, h2⟩ := Finset.mem_product.1 he'
            have h5 := hL e'.1 (Finset.mem_range.1 h1) e'.2 (Finset.mem_range.1 h2)
            rw [hcl, Option.any_some, Bool.and_eq_true] at h5
            exact live_ne cl tl.ix.ZZ (tl.zzBlocks + e'.1) (tl.mz + e'.2) h5.2
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.digitsEn_card
#print axioms VerifiableInference.Desc.First.K8.Honest.digits_few
