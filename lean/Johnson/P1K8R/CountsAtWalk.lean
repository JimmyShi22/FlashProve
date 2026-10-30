-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CountsAtWalk.lean: THE SMALLNESS TEST: THE LOCAL COUNTS OF ITS TWO TESTS AT THE
BATCHING's ROUND, AT THE VERIFIER's STATE THAT THE HONEST SIDE's WALK HOLDS IN FRONT OF THE BATCHING
(`ChainProgress`, Johnson/Desc/ProofFile/Honest/Walk.lean; `ChainProgress.Tied`,
Johnson/Desc/ProofFile/Honest/Law/WalkFold.lean). LEMMAS; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding. An assembly: no new argument.

l < 25. Kd := 14 l + 6, or 343 at the head's: the member that hears the draw. K := 14 l + 9, or 347:
the batching's.
  `fold_of_tied`   general: a walk that is tied, has asked just the first M members and holds the
      verifier's state s': the verifier's fold over these members, at the rounds laid and the walk's
      columns, returns s'
  **`front_at_walk`**, **`front_at_walk_blocks`**   in the goals' scope; at such a walk with M = K,
      at first tree 0: sz fits; the round laid at the draw's number shows a typed matrix's list at
      which `deadT` is silent: the bounds of `front_of_fold` and `front_of_fold_blocks`
      (Johnson/P1K8R/LiveOfFold.lean) for `k8Front s'`
  **`units_at_walk`**, **`units_at_walk_blocks`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25
      SEGMENTS (`RowsAsked Z`): at such a walk from the chain's start ProofFile.startS Z zp: the bounds of
      `units_of_fold` and `units_of_fold_blocks` for `unitsT b nU s'`
Limits. That a walk is tied and has asked just these members are premises. What remembers down the
chain that `deadT` was silent is not built. `RowsAsked Z` IS A PREMISE of the last two, which bound
ONE of the tests on the ledger's weights. No number is evaluated.
-/
import Johnson.P1K8R.LiveOfFold
import Johnson.Desc.ProofFile.Honest.Law.WalkFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open ProofFile.Honest (ChainProgress Lay roundsOf)
open ProofFile.Honest.K8 (rnds k8Front)
open Iop
open scoped ENNReal

/-- A tied walk's verifier's state is the fold's end over the members asked. -/
theorem fold_of_tied {T Cl W Y : Type} (L : Lay) (bs : List (Block T Cl)) (s₀ s' : T)
    (z : ChainProgress T Cl W Y) (M : ℕ) (ht : ChainProgress.Tied L bs (some s₀) z.todo z)
    (htodo : z.todo = bs.drop M) (hown : z.own = []) (hv : z.ver = some s') :
    ∃ r c', foldBlocks L.firstTree (bs.take M) s₀ (roundsOf z.laid) z.cols = .ok (s', r, c') := by
  obtain ⟨done, front, e1, e2, -, -, e5⟩ := ht
  have hd : done = bs.take M := by
    have h1 : done ++ bs.drop M = bs.take M ++ bs.drop M := by
      rw [List.take_append_drop, ← htodo]
      exact e1.symm
    exact List.append_cancel_right h1
  rw [hown, List.append_nil] at e2
  rw [hv, hd, ← e2] at e5
  have e5' : some s' =
      (foldBlocks L.firstTree (bs.take M) s₀ (roundsOf z.laid) z.cols).toOption.map (·.1) := e5
  cases hf : foldBlocks L.firstTree (bs.take M) s₀ (roundsOf z.laid) z.cols with
  | error x =>
    rw [hf] at e5'
    cases e5'
  | ok y =>
    obtain ⟨t, r, c'⟩ := y
    rw [hf] at e5'
    obtain rfl : s' = t := Option.some.inj e5'
    exact ⟨r, c', rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W Y : Type}

/-- **The first test's local count at the walk's state: at typed challenges.** -/
theorem front_at_walk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (L : Lay) (s₀ s' : S) (z : ChainProgress S Claim W Y) (sz : Size) (r₀ : Fmt.RoundView) (d₂ : RDT),
        L.firstTree = 0 → ChainProgress.Tied L c.blocksInOrder (some s₀) z.todo z →
        z.todo = c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) → z.own = [] →
        z.ver = some s' → Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        (roundsOf z.laid)[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? =
          some r₀ →
        (∃ β : Dr sz, r₀.drawn.trits.toArray = listOf β) → deadT sz [r₀.drawn] = false →
        OneElem d₂.entry d₂.kind →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d₂]) |
            (k8Front s' (drawnT (_root_.Run.ck .two) [d₂] ρ)).isSome = true} ≤
          ((sz.columns * (sz.tau - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨Xl, hXl, h⟩ := front_of_fold hS hR O hl
  refine ⟨Xl, hXl, ?_⟩
  intro L s₀ s' z sz r₀ d₂ hft ht htodo hown hv hfit hr₀ hβ hdead h₂
  obtain ⟨r, c', hf⟩ := fold_of_tied L c.blocksInOrder s₀ s' z _ ht htodo hown hv
  rw [hft] at hf
  exact h s₀ s' _ r _ c' sz r₀ d₂ hf hfit hr₀ hβ hdead h₂

/-- **The same at strings of hash blocks.** -/
theorem front_at_walk_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (L : Lay) (s₀ s' : S) (z : ChainProgress S Claim W Y) (sz : Size) (r₀ : Fmt.RoundView) (d₂ : RDT),
        L.firstTree = 0 → ChainProgress.Tied L c.blocksInOrder (some s₀) z.todo z →
        z.todo = c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) → z.own = [] →
        z.ver = some s' → Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        (roundsOf z.laid)[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? =
          some r₀ →
        (∃ β : Dr sz, r₀.drawn.trits.toArray = listOf β) → deadT sz [r₀.drawn] = false →
        OneElem d₂.entry d₂.kind → d₂.entry.logN ≤ 64 →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d₂]) |
            (k8Front s' (drawnT (_root_.Run.ckP .two) [d₂] ρ)).isSome = true} ≤
          kapSl 128 ^ 3 * ((sz.columns * (sz.tau - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨Xl, hXl, h⟩ := front_of_fold_blocks hS hR O hl
  refine ⟨Xl, hXl, ?_⟩
  intro L s₀ s' z sz r₀ d₂ hft ht htodo hown hv hfit hr₀ hβ hdead h₂ hl₂
  obtain ⟨r, c', hf⟩ := fold_of_tied L c.blocksInOrder s₀ s' z _ ht htodo hown hv
  rw [hft] at hf
  exact h s₀ s' _ r _ c' sz r₀ d₂ hf hfit hr₀ hβ hdead h₂ hl₂

/-- **The second test's local count at the walk's state: at typed challenges.** -/
theorem units_at_walk (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (Xk : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some Xk ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (L : Lay) (zp : ProofFile.InstPub) (s' : S) (z : ChainProgress S Claim W Y), L.firstTree = 0 →
        ChainProgress.Tied L c.blocksInOrder (some (ProofFile.startS Z zp)) z.todo z →
        z.todo = c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) → z.own = [] →
        z.ver = some s' →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ Xk) s' (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
          (((ProofFile.k8NU Bs.G₀ Xk).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, Xk, hb, hp, hX, h⟩ := units_of_fold hE hS hR O hl
  refine ⟨b, p, Xk, hb, hp, hX, ?_⟩
  intro d he h5 h6 L zp s' z hft ht htodo hown hv
  obtain ⟨r, c', hf⟩ := fold_of_tied L c.blocksInOrder _ s' z _ ht htodo hown hv
  rw [hft] at hf
  exact h d he h5 h6 zp s' _ r _ c' hf

/-- **The same at strings of hash blocks.** -/
theorem units_at_walk_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (Xk : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some Xk ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (L : Lay) (zp : ProofFile.InstPub) (s' : S) (z : ChainProgress S Claim W Y), L.firstTree = 0 →
        ChainProgress.Tied L c.blocksInOrder (some (ProofFile.startS Z zp)) z.todo z →
        z.todo = c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) → z.own = [] →
        z.ver = some s' →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ Xk) s' (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
          kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ Xk).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, Xk, hb, hp, hX, h⟩ := units_of_fold_blocks hE hS hR O hl
  refine ⟨b, p, Xk, hb, hp, hX, ?_⟩
  intro d he h5 h6 L zp s' z hft ht htodo hown hv
  obtain ⟨r, c', hf⟩ := fold_of_tied L c.blocksInOrder _ s' z _ ht htodo hown hv
  rw [hft] at hf
  exact h d he h5 h6 zp s' _ r _ c' hf

end

end P1K8

#print axioms P1K8.fold_of_tied
#print axioms P1K8.front_at_walk
#print axioms P1K8.front_at_walk_blocks
#print axioms P1K8.units_at_walk
#print axioms P1K8.units_at_walk_blocks
