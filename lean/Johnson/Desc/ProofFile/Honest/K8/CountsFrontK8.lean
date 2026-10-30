-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean: THE SMALLNESS TEST: THE SENTENCE `CountsFront`
OF THE ITEM "totalB" AT THE BATCHING's MEMBER (Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean,
another house's file of definitions): the counts that the block behind the batching asks beside the
number of claims hold AT THE STATE IN FRONT OF THE BATCHING: OFF THE STAND's OWN YES, GENERAL IN THE
THREAD: the batching's yes holds the gatherer's; in it the run "K8.equations" said yes at some
state; its first lines test these counts there (Johnson/Desc/K8/Honest/EqFront.lean); and what the
counts read is the same at that state and in front of the draw. Lemmas; none of the library's goals.

  `map_blank`   a reading of the test's data that does not see the fourteen written fields is the
                   same at two states whose blanked data are the same
  `forall₂_left`   of two lists tied member by member: each member of the first has its partner
  `NumRun Lk u`, `NumDraw p u`   TWO NAMED PREMISES, IN THE OTHER HOUSE's OWN WORDS: every run that
                   the order names leaves the library's `K9L.numOf u`
                   (Johnson/Desc/First/Batch/Law/RowsRide.lean) · so does the draw
  `K8At Lk k pW`   A NAMED PREMISE ON THE LINK: the kind's entry stands in the order, and the run
                   that the link's blocks state there says yes only where the kind's own block's run
                   says the same yes
  `FoldOnce Lk p T b`   A NAMED PREMISE AT THE OUTPUT HEAD ALONE: at a stand the matrix is counted
                   as drawn once
  **`counts_front`**   NumRun → NumDraw → K8At → (at the head: FoldOnce) → CountsFront Lk p T b w
Limits. FOUR PREMISES, NONE PAID HERE: the first two are the other house's to pay; the third is a
fact on the seat; the fourth is paid nowhere: no line of the run tests it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalBehind
import Johnson.Desc.K8.Honest.EqFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.K8.Honest (counts_of_run)
open ProofFile.Honest.K9 (BatStand CountsFront counts_ride gathered gather_ran ran_inv claimsRunOf
  RunUnder k8Entry drawnOne)

/-- A reading that does not see the written fields is the same where the blanked data are. -/
theorem map_blank {β : Type} (u : HTailF2) (f : HTailF2 → β) (hf : ∀ t, f (blank u t) = f t)
    {a b : S} (h : a.tl?.map (blank u) = b.tl?.map (blank u)) : a.tl?.map f = b.tl?.map f := by
  have e := congrArg (Option.map f) h
  rw [Option.map_map, Option.map_map] at e
  have e2 : (f ∘ blank u) = f := funext hf
  rw [e2] at e
  exact e

/-- Each member of the first of two lists that are tied member by member has its partner. -/
theorem forall₂_left {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, a, ha => absurd ha List.not_mem_nil
  | _, _, .cons h t, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, h⟩
    · exact forall₂_left t a ha'

/-- Every run that the order names leaves what the library's sentence on numbers reads. -/
def NumRun (Lk : Link S Claim) (u : HTailF2) : Prop :=
  ∀ o ∈ Lk.order, ∀ run, LinkJoin.At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
    K9L.numOf u e₁ = K9L.numOf u e

/-- So does the draw. -/
def NumDraw (p : Desc.K9.Where) (u : HTailF2) : Prop :=
  ∀ s x t₁,
    (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      K9L.numOf u t₁ = K9L.numOf u s

/-- The kind's entry stands in the order; the run there is under the kind's own block's. -/
def K8At (Lk : Link S Claim) (k : Desc.K9.SegSort) (pW : K8.ParW) : Prop :=
  k8Entry k ∈ Lk.order ∧ ∀ run, claimsRunOf Lk.hear (k8Entry k) = some run →
    ∃ runK, ("K8.equations", runK) ∈ (K8.whole pW).claims ∧ RunUnder run runK

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (Lk : Link S Claim) (p : Desc.K9.Where)
  (T : Thread Bk S Claim V W X Pb) (b : Nat)

/-- At a stand the matrix is counted as drawn once. -/
def FoldOnce : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    (s.tl?.map (·.foldDrawn == 1)).getD false = true

/-- **The counts but the first, at the state in front of the batching.** -/
theorem counts_front (u : HTailF2) (w : Desc.K9.SegSort × Nat × Desc.K9.TWhere) (pW : K8.ParW)
    (hN : NumRun Lk u) (hD : NumDraw p u) (hK : K8At Lk w.1 pW)
    (hF : w.1 = .head → FoldOnce Lk p T b) : CountsFront Lk p T b w := by
  intro κ s m En ds y cols s' x z G hS
  have hg := hS.bat.gathered
  cases hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] with
  | error e => simp [gathered, hd] at hg
  | ok t₁ =>
    cases hy : claimsInBy Lk.each Lk.hear Lk.order t₁ with
    | error e => simp [gathered, hd, hy] at hg
    | ok yy =>
      obtain ⟨ls, -, hR⟩ := gather_ran Lk.each Lk.hear Lk.order t₁ yy hy
      obtain ⟨hAll, -⟩ := ran_inv Lk.hear (fun e => K9L.numOf u e = K9L.numOf u s) Lk.order 0 t₁ ls
        yy.2 (fun o ho run hr n t zz hI hz => (hN o ho run hr n t zz.1 zz.2 hz).trans hI)
        (hD s x t₁ hd) hR
      obtain ⟨l, run, n, e, zz, hr, hI, hz, -⟩ := forall₂_left hAll (k8Entry w.1) hK.1
      obtain ⟨runK, h8, hu⟩ := hK.2 run hr
      have hI' : K9L.numOf u e = K9L.numOf u s := hI
      have e1 : e.tl?.map (blank u) = s.tl?.map (blank u) := congrArg (·.1) hI'
      have e2 : e.funs? = s.funs? := congrArg (·.2.1) hI'
      have hc := counts_of_run pW runK h8 n e zz.2 zz.1 (hu n e zz hz) w.1 w.2.1 fun hh => by
        rw [map_blank u (fun t => t.foldDrawn == 1) (fun _ => rfl) e1]
        exact hF hh κ s m En ds y cols s' x z G hS
      exact counts_ride u w e s e1.symm e2.symm hc

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.map_blank
#print axioms ProofFile.Honest.K8.forall₂_left
#print axioms ProofFile.Honest.K8.counts_front
