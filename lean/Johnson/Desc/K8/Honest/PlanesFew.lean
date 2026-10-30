-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesFew.lean: THE SMALLNESS TEST: THE COUNT FOR ITS TEST `selfPlanes` ("no
weight on the three rows of the array of the counts' bits is 0":
Johnson/Desc/First/TailClaims/SelfTests.lean). Definitions with code, a statement and its proof. No
prover. Lemmas; none of the library's goals.

BZ: the array of the bits of the lookup's counts. Three of the first four claims of "K8.equations"
lay one run each on its rows 0, 1, 2 (K9L.four8, Johnson/Desc/First/Batch/Law/K8Four.lean).
  `planesLaid tl`   with code, on public numbers: BZ is not the digits' array, no matrix's array of
      symbols, and not what a read's vector's array reads as
  `planesLive tl`   with code, ON WHAT THE LOOKUP HAS HEARD, in front of the batching: at every
      entry u < bzColumns of row r < 3 the claim number 1 + r of the four has a coefficient other
      than 0 (`liveAt`, Johnson/Desc/K8/Honest/CoefCode.lean)
  `planesNo s`   the state holds data and a ledger at which `selfPlanes` says no
  **`planes_few`**   IF tl passes both tests, g meets `Gathers` at s and the plan's number of claims
      is at most d + 1: THEN at most 3 * bzColumns * d field elements are challenges at which batch
      says yes and, behind it, `selfPlanes` says no
By: `entries_few` (EntriesFew.lean) · `noneZero_no`, `live_ne` (CoefCode.lean).
Limits. `planesLive` IS A PREMISE ON CHALLENGES DRAWN IN FRONT: how often it fails is counted
nowhere here; nor which of the heard values make a coefficient 0. `Gathers` and `planesLaid` are
premises. No number is evaluated.
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

/-- On public numbers. -/
def planesLaid (tl : HTailF2) : Bool :=
  tl.ix.ZZ != tl.ix.BZ && ((List.range tl.NM).all fun mu => tl.gtTree.getD mu 0 != tl.ix.BZ) &&
    (tl.ix.U.getD 0 none).getD 0 != tl.ix.BZ && (tl.ix.U.getD 2 none).getD 0 != tl.ix.BZ

/-- On what the lookup has heard. -/
def planesLive (tl : HTailF2) : Bool :=
  match tl.heard with
  | some g =>
    (List.range 3).all fun r => (List.range tl.bzColumns).all fun u =>
      ((K9L.four8 tl g)[1 + r]?).any fun cl => liveAt cl tl.ix.BZ r u
  | none => false

/-- `selfPlanes` says no at the state. -/
def planesNo (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => !selfPlanes q.1 q.2
  | none => false

/-- **The count.** -/
theorem planes_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hP : planesLaid tl = true)
    (hL : planesLive tl = true) (hG : Gathers p g s tl funs nf nb a)
    (hd : F.planClaimsF ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch planesNo s [chiAt x] = true) ≤
      3 * tl.bzColumns * d := by
  simp only [planesLaid, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range] at hP
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
  have hoff : ∀ r, OffAt tl tl.ix.BZ r := fun r =>
    ⟨fun h => p1 h.1, fun h => p1 h.1, fun mu hmu h => p2 mu hmu h.1, p3, p4⟩
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch planesNo s [chiAt x] = true
  · -- the four claims' coefficients are a's values: read off at one yes
    obtain ⟨x₀, hx₀⟩ := hne
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
      have hc : (Finset.range 3 ×ˢ Finset.range tl.bzColumns).card = 3 * tl.bzColumns := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]
      rw [← hc]
      refine entries_few p g batch s tl F funs nf nb d a hb hs hG tl.ix.BZ _ planesNo
        (fun e _ => hoff e.1) ?_ ?_ ?_ hd
      · intro t'' tl' G h1 heq hno
        obtain ⟨n₀, F₁, F₂, k8, geq⟩ := heq
        have hix : tl'.ix = tl.ix :=
          eq_same (fun u : HTailF2 => u.ix) geq (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        have hf9 : tl'.f9 = tl.f9 :=
          eq_same (fun u : HTailF2 => u.f9) geq (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        unfold planesNo at hno
        rw [h1] at hno
        have hno' : selfPlanes tl' G = false := by simpa using hno
        unfold selfPlanes at hno'
        obtain ⟨r, hr, hr'⟩ := List.all_eq_false.1 hno'
        have hcols : tl'.bzColumns = tl.bzColumns := by
          unfold HTailF2.bzColumns
          rw [hf9]
        rw [hix, hcols] at hr'
        obtain ⟨u, hu, hz⟩ := noneZero_no _ 0 _ (Or.inl (Nat.zero_le _)) (by simpa using hr')
        rw [Nat.zero_add] at hz
        exact ⟨(r, u), Finset.mem_product.2 ⟨Finset.mem_range.2 (List.mem_range.1 hr),
          Finset.mem_range.2 hu⟩, hz⟩
      · intro e he
        right
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
        exact Finset.mem_product.2 ⟨h1, Finset.mem_range.2
          (Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_range.1 h2))⟩
      · intro e he
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
        unfold planesLive at hL
        rw [hg₀] at hL
        simp only [List.all_eq_true, List.mem_range] at hL
        have h5 := hL e.1 (Finset.mem_range.1 h1) e.2 (Finset.mem_range.1 h2)
        refine ⟨nf + (1 + e.1), by have := Finset.mem_range.1 h1; omega, ?_⟩
        cases hcl : (K9L.four8 tl g₀)[1 + e.1]? with
        | none =>
          rw [hcl] at h5
          cases h5
        | some cl =>
          rw [hcl, Option.any_some] at h5
          rw [h4 (1 + e.1) cl hcl]
          exact live_ne cl tl.ix.BZ e.1 e.2 h5
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planes_few
