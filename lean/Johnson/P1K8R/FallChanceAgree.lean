-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallChanceAgree.lean: THE SMALLNESS TEST: THE CHANCES OF
Johnson/P1K8R/FallChanceAll.lean AND FallChanceBlocks.lean FOR EVERY FUNCTION front WHOSE VALUES ON
EACH FIBRE OVER THE BATCHING's ROUND AGREE. Lemmas; none of the library's goals. No prover stands in
them; nothing on completeness, soundness or hiding. An assembly: no new argument.

The law is that of Johnson/Desc/K8/Honest/ChanceOfCounts.lean: ι a finite type of rounds, A i round
i's challenges, the list f : ∀ i, A i uniform. j: the batching's round. Why. These files' theorems
ask of front that it does not read round j's challenge. A function that is read off a whole run need
not meet that (Johnson/Desc/K8/Honest/FreeOfAgree.lean). Here that premise is replaced by `Agree j
front`: on each fibre over round j (the lists that differ at round j alone) all the values "some s"
of front are one s; every other letter, the event and the bound are theirs.
  **`fall_chance_agree`**, **`fall_chance_blocks_agree`**, **`fall_chance_sampled_agree`**   the
      statements of `fall_chance_all`, `fall_chance_blocks`, `fall_chance_sampled`, with that one
      premise replaced
By: `free_of_agree`; then the named theorem itself at the function that it gives; Prob.pr_mono.
Limits: those of FallChanceAll.lean and FallChanceBlocks.lean: front IS STILL A LETTER: that any run
of a prover gives a function that meets `Agree`, (reach) and (bound) is not shown.

-/
import Johnson.P1K8R.FallChanceBlocks
import Johnson.Desc.K8.Honest.FreeOfAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open Iop
open scoped ENNReal

/-- `fall_chance_all`, for a front whose values agree on each fibre over round j. -/
theorem fall_chance_agree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
        (_ : ∀ x, Prob.cnt (fun a => el a = x) ≤ w)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : Agree j front)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn.elems = [Slice.ofE (el (f j))] ∧ b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_all hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j el w hw front hagree hreach d hd
  obtain ⟨front', hfree, hover, hfrom⟩ := free_of_agree j front hagree
  refine (Prob.pr_mono _ fun f hf => ?_).trans (hall j el w hw front' hfree
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hreach _ zs ha) d
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hd _ zs ha))
  obtain ⟨zs, hz, hrest⟩ := hf
  exact ⟨zs, hover f zs hz, hrest⟩

/-- `fall_chance_blocks`, for such a front. -/
theorem fall_chance_blocks_agree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (k : Fmt.Kind) (_ : k ≠ .seeds) (_ : k ≠ .sealed)
        (view : A j → (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (_ : Function.Injective view)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : Agree j front)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn = Run.drawnOf .two (K9.entry p) k
                ((Run.bsRound .two (K9.entry p) k).φ (view (f j))) ∧
              b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d * (Run.bsRound .two (K9.entry p) k).w : ℕ) : ℝ≥0∞) /
            Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_blocks hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j k h5 h6 view hview front hagree hreach d hd
  obtain ⟨front', hfree, hover, hfrom⟩ := free_of_agree j front hagree
  refine (Prob.pr_mono _ fun f hf => ?_).trans (hall j k h5 h6 view hview front' hfree
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hreach _ zs ha) d
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hd _ zs ha))
  obtain ⟨zs, hz, hrest⟩ := hf
  exact ⟨zs, hover f zs hz, hrest⟩

/-- `fall_chance_sampled`, for such a front. -/
theorem fall_chance_sampled_agree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (k : Fmt.Kind) (_ : k ≠ .seeds) (_ : k ≠ .sealed)
        (view : A j → (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (_ : Function.Injective view)
        (_ : Fintype.card (A j) =
          Fintype.card (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : Agree j front)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn = Run.drawnOf .two (K9.entry p) k
                ((Run.bsRound .two (K9.entry p) k).φ (view (f j))) ∧
              b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          kapSl 128 ^ Run.exAll (Fmt.dsOf (K9.entry p) k) *
            (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d : ℕ) : ℝ≥0∞) /
            (Nat.card (Run.Ch .two (K9.entry p) k) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_sampled hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j k h5 h6 view hview hcard front hagree hreach d hd
  obtain ⟨front', hfree, hover, hfrom⟩ := free_of_agree j front hagree
  refine (Prob.pr_mono _ fun f hf => ?_).trans (hall j k h5 h6 view hview hcard front' hfree
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hreach _ zs ha) d
    (fun f zs hz => by
      obtain ⟨a, ha⟩ := hfrom f zs hz
      exact hd _ zs ha))
  obtain ⟨zs, hz, hrest⟩ := hf
  exact ⟨zs, hover f zs hz, hrest⟩

end P1K8

#print axioms P1K8.fall_chance_agree
#print axioms P1K8.fall_chance_blocks_agree
#print axioms P1K8.fall_chance_sampled_agree
