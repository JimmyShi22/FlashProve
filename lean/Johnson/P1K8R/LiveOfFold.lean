-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveOfFold.lean: THE SMALLNESS TEST: THE STATE THAT THE VERIFIER's OWN FOLD
(`foldBlocks`) RETURNS OVER THE MEMBERS IN FRONT OF A SEGMENT's BATCHING, AGAINST THE MATRIX THAT
THE DRAW's ROUND SHOWS; AND THE LOCAL COUNTS OF THE TWO TESTS AT EVERY SUCH STATE. LEMMAS; NONE OF
THE LIBRARY's GOALS. No run, no prover. Nothing on completeness, soundness or hiding. An assembly:
no new argument.

l < 25. Kd := 14 l + 6, or 343 at the head's: the member that hears the draw. K := 14 l + 9, or 347:
the batching's.
  `fold_rest`   general: a fold that returns leaves over the rounds behind those of its members
  **`live_of_fold`**   in the goals' scope; Xl the built segment; FROM WHATEVER STATE: where the
      fold over the first K members returns s', sz fits the place's parameters, and the round that
      stands at the draw's number among the rounds handed in shows the list of the typed matrix β:
      s' holds data tl that read β; `allLive tl = false` just if some column of β is all 0; cols tl
      = sz.columns
  **`state_of_fold`**   so, where that round shows a typed matrix's list at which `deadT` is silent:
      tl is all live, cols tl = sz.columns, tl.tau = sz.tau
  **`front_of_fold`**, **`front_of_fold_blocks`**   at every such s': d₂ a round's data that draws
      one field element and nothing else: the measure (Iop.prRho: each of that one round's messages
      weighs the same) of the messages at which `k8Front s'` says something of the challenge that
      the message bears is at most columns * (tau - 1) / p ^ 3 at Run.ck .two, and kapSl 128 ^ 3
      times that at Run.ckP .two
  **`units_of_fold`**, **`units_of_fold_blocks`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25
      SEGMENTS (`RowsAsked Z`): where the fold from the chain's start returns s': the bounds of
      `units_gate_p3` and `units_gate_blocks` for `unitsT b nU s'`
By: `matrix_at_batch` (Johnson/P1K8R/MatrixAtBatch.lean) · `draw_member` (LocalFalls.lean) ·
fold_split, reach_of_fold (Johnson/Top/H0/Walk/Reach.lean) · foldBlocks_cons_yes
(Johnson/Desc/LinkLaw2.lean) · `dead_iff` · `k8Front_few`, `k8Front_elems` · `prRho_elem_le` ·
`card_one_elem`, `blocks_el`, `blocks_bound`.
Limits. That a fold returns, and that sz fits, are premises. `RowsAsked Z` IS A PREMISE of the last
two, which bound ONE of the tests on the ledger's weights. The uniform law on one round's messages
is named, not derived. No number is evaluated.
-/
import Johnson.P1K8R.LocalFalls
import Johnson.P1K8R.UnitsBlocks
import Johnson.Desc.K8.Honest.DeadTest
import Johnson.Desc.ProofFile.Honest.K8.FrontAtList
import Johnson.Desc.LinkLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold fold_split)
open ProofFile.Honest.K8 (allLive cols rnds rnds_append k8Front k8Front_few k8Front_elems TypedAt)
open Iop
open scoped ENNReal

/-- A fold that returns leaves over the rounds behind those of its members. -/
theorem fold_rest {T Cl : Type} (ft : ℕ) : ∀ (l : List (Block T Cl)) (s t : T)
    (rs r : List Fmt.RoundView) (cols c : List Desc.OpenedColumn),
    foldBlocks ft l s rs cols = .ok (t, r, c) → r = rs.drop (rnds l) ∧ rnds l ≤ rs.length
  | [], s, t, rs, r, cols, c, h => by
    unfold foldBlocks at h
    injection h with h
    obtain ⟨-, h2⟩ := Prod.mk.inj h
    obtain ⟨h3, -⟩ := Prod.mk.inj h2
    exact ⟨by simp [rnds, h3], by simp [rnds]⟩
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨s', k, hle, -, h'⟩ := foldBlocks_cons_yes h
    obtain ⟨e1, e2⟩ := fold_rest ft l s' t _ r _ c h'
    have hc : rnds (b :: l) = b.rounds.length + rnds l := by
      show rnds ([b] ++ l) = _
      rw [rnds_append]
      simp [rnds]
    rw [List.length_drop] at e2
    refine ⟨?_, by omega⟩
    rw [e1, List.drop_drop, hc]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The fold's end against the matrix that the draw's round shows.** -/
theorem live_of_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (s₀ s' : S) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn) (sz : Size) (β : Dr sz)
        (r₀ : Fmt.RoundView),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) s₀ rs cs =
          .ok (s', r, c') →
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        rs[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some r₀ →
        r₀.drawn.trits.toArray = listOf β →
        ∃ tl, s'.tl? = some tl ∧ TypedAt sz β tl ∧
          (allLive tl = false ↔ ∃ (μ : Fin sz.NM) (c₁ : Fin (sz.k μ)), ∀ u, (β μ u c₁).val = 0) ∧
          cols tl = sz.columns := by
  have hx : (l, if l = 24 then 5 else 4, if l = 24 then 3 else 2) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨b8, Xl, hf8, hXl, hmat⟩ := matrix_at_batch hS hR O _ hx
  obtain ⟨b8', hf8', h1⟩ := draw_member hS hR O hl
  obtain rfl : b8 = b8' := Option.some.inj (hf8.symm.trans hf8')
  refine ⟨Xl, hXl, ?_⟩
  intro s₀ s' rs r cs c' sz β r₀ hfold hfit hr₀ hβ
  have hK : 14 * l + (if l = 24 then 11 else 9) =
      14 * l + (if l = 24 then 5 else 4) + 2 + (1 + (if l = 24 then 3 else 2)) := by
    split_ifs <;> omega
  obtain ⟨hlt, hbe⟩ := List.getElem?_eq_some_iff.1 hf8'
  have hcut : c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)) =
      c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2) ++
        (b8 :: (c.blocksInOrder.drop (14 * l + (if l = 24 then 5 else 4) + 3)).take
          (if l = 24 then 3 else 2)) := by
    rw [hK, List.take_add, List.drop_eq_getElem_cons hlt, hbe, Nat.add_comm 1,
      List.take_succ_cons]
  rw [hcut] at hfold
  obtain ⟨s₆, r₁, c₁, g1, g2⟩ := fold_split 0 _ _ _ _ _ _ hfold
  obtain ⟨e1, -⟩ := fold_rest 0 _ _ _ _ _ _ _ g1
  obtain ⟨s₇, k, -, g3, g4⟩ := foldBlocks_cons_yes g2
  have htake : r₁.take b8.rounds.length = [r₀] := by
    rw [h1, e1]
    obtain ⟨hlt', hre⟩ := List.getElem?_eq_some_iff.1 hr₀
    rw [List.drop_eq_getElem_cons hlt', hre]
    rfl
  rw [htake] at g3
  exact hmat 0 s₆ s₇ r₀ c₁ k _ _ _ sz β hfit g3 hβ g4

/-- **Where the mark is silent the fold's end is all live.** -/
theorem state_of_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (s₀ s' : S) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn) (sz : Size) (r₀ : Fmt.RoundView),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) s₀ rs cs =
          .ok (s', r, c') →
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        rs[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some r₀ →
        (∃ β : Dr sz, r₀.drawn.trits.toArray = listOf β) → deadT sz [r₀.drawn] = false →
        ∃ tl, s'.tl? = some tl ∧ allLive tl = true ∧ cols tl = sz.columns ∧
          tl.tau = sz.tau := by
  obtain ⟨Xl, hXl, h⟩ := live_of_fold hS hR O hl
  refine ⟨Xl, hXl, ?_⟩
  intro s₀ s' rs r cs c' sz r₀ hfold hfit hr₀ hβ hdead
  obtain ⟨β, hβ⟩ := hβ
  obtain ⟨tl, t1, tT, t2, t3⟩ := h s₀ s' rs r cs c' sz β r₀ hfold hfit hr₀ hβ
  refine ⟨tl, t1, ?_, t3, tT.tau⟩
  cases hl' : allLive tl with
  | true => rfl
  | false =>
    have hd : deadB sz (listOf β) = true := (dead_iff β).2 (t2.1 hl')
    have hd' : deadT sz [r₀.drawn] = true := by
      show deadB sz r₀.drawn.trits.toArray = true
      rw [hβ]
      exact hd
    rw [hd'] at hdead
    cases hdead

end

/-- The count of the first test at data that are all live, over one round's typed messages. -/
theorem front_live (s' : S) (tl : HTailF2) (hts : s'.tl? = some tl) (hlive : allLive tl = true)
    (d₂ : RDT) (h₂ : OneElem d₂.entry d₂.kind) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d₂]) |
        (k8Front s' (drawnT (_root_.Run.ck .two) [d₂] ρ)).isSome = true} ≤
      ((cols tl * (tl.tau - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have k := prRho_elem_le (_root_.Run.ck .two) d₂ (elOf d₂.entry d₂.kind) 1 (elOf_one _ _ h₂)
    (fun a => by
      show (_root_.Run.drawnOf .two d₂.entry d₂.kind a).elems = _
      rw [shows_chi _ _ h₂]
      rfl)
    (fun dr => (k8Front s' [dr]).isSome = true)
    (fun x => (k8Front s' [chiAt x]).isSome = true)
    (fun dr x hq hx => by
      have e := k8Front_elems s' dr (chiAt x) hx
      show (k8Front s' [chiAt x]).isSome = true
      rw [← e]
      exact hq) _ (k8Front_few s' tl hts hlive)
  rw [Nat.mul_one] at k
  rw [← card_one_elem d₂.entry d₂.kind h₂]
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans k
  obtain ⟨a, u⟩ := ρ
  exact ⟨_, rfl, hρ⟩

/-- The same over one round's strings of hash blocks. -/
theorem front_live_blocks (s' : S) (tl : HTailF2) (hts : s'.tl? = some tl)
    (hlive : allLive tl = true) (d₂ : RDT) (h₂ : OneElem d₂.entry d₂.kind)
    (hl₂ : d₂.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d₂]) |
        (k8Front s' (drawnT (_root_.Run.ckP .two) [d₂] ρ)).isSome = true} ≤
      kapSl 128 ^ 3 * ((cols tl * (tl.tau - 1) : ℕ) : ℝ≥0∞) /
        ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have k := prRho_elem_le (_root_.Run.ckP .two) d₂
    (fun u => elOf d₂.entry d₂.kind ((_root_.Run.bsRound .two d₂.entry d₂.kind).φ u))
    (_root_.Run.bsRound .two d₂.entry d₂.kind).w (blocks_el _ _ h₂ hl₂)
    (fun a => by
      show (_root_.Run.drawnOf .two d₂.entry d₂.kind
        ((_root_.Run.bsRound .two d₂.entry d₂.kind).φ a)).elems = _
      rw [shows_chi _ _ h₂]
      rfl)
    (fun dr => (k8Front s' [dr]).isSome = true)
    (fun x => (k8Front s' [chiAt x]).isSome = true)
    (fun dr x hq hx => by
      have e := k8Front_elems s' dr (chiAt x) hx
      show (k8Front s' [chiAt x]).isSome = true
      rw [← e]
      exact hq) _ (k8Front_few s' tl hts hlive)
  refine ((Prob.pr_mono _ fun ρ hρ => ?_).trans k).trans (blocks_bound _ _ h₂ hl₂ _)
  obtain ⟨a, u⟩ := ρ
  exact ⟨_, rfl, hρ⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The first test's local count at every state that the fold and the mark's silence let in.** -/
theorem front_of_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (s₀ s' : S) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn) (sz : Size) (r₀ : Fmt.RoundView)
        (d₂ : RDT),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) s₀ rs cs =
          .ok (s', r, c') →
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        rs[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some r₀ →
        (∃ β : Dr sz, r₀.drawn.trits.toArray = listOf β) → deadT sz [r₀.drawn] = false →
        OneElem d₂.entry d₂.kind →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d₂]) |
            (k8Front s' (drawnT (_root_.Run.ck .two) [d₂] ρ)).isSome = true} ≤
          ((sz.columns * (sz.tau - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨Xl, hXl, h⟩ := state_of_fold hS hR O hl
  refine ⟨Xl, hXl, ?_⟩
  intro s₀ s' rs r cs c' sz r₀ d₂ hfold hfit hr₀ hβ hdead h₂
  obtain ⟨tl, hts, hlive, hc, ht⟩ := h s₀ s' rs r cs c' sz r₀ hfold hfit hr₀ hβ hdead
  rw [← hc, ← ht]
  exact front_live s' tl hts hlive d₂ h₂

/-- **The same at strings of hash blocks.** -/
theorem front_of_fold_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ (s₀ s' : S) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn) (sz : Size) (r₀ : Fmt.RoundView)
        (d₂ : RDT),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) s₀ rs cs =
          .ok (s', r, c') →
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        rs[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some r₀ →
        (∃ β : Dr sz, r₀.drawn.trits.toArray = listOf β) → deadT sz [r₀.drawn] = false →
        OneElem d₂.entry d₂.kind → d₂.entry.logN ≤ 64 →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d₂]) |
            (k8Front s' (drawnT (_root_.Run.ckP .two) [d₂] ρ)).isSome = true} ≤
          kapSl 128 ^ 3 * ((sz.columns * (sz.tau - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨Xl, hXl, h⟩ := state_of_fold hS hR O hl
  refine ⟨Xl, hXl, ?_⟩
  intro s₀ s' rs r cs c' sz r₀ d₂ hfold hfit hr₀ hβ hdead h₂ hl₂
  obtain ⟨tl, hts, hlive, hc, ht⟩ := h s₀ s' rs r cs c' sz r₀ hfold hfit hr₀ hβ hdead
  rw [← hc, ← ht]
  exact front_live_blocks s' tl hts hlive d₂ h₂ hl₂

/-- **The second test's local count at every state that the fold from the start lets in.** -/
theorem units_of_fold (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (zp : ProofFile.InstPub) (s' : S) (rs r : List Fmt.RoundView) (cols c' : List Desc.OpenedColumn),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) (ProofFile.startS Z zp) rs
          cols = .ok (s', r, c') →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ X) s' (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate_p3 hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 zp s' rs r cols c' hfold
  exact h d he h5 h6 zp s' (reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cols c'
    hfold)

/-- **The same at strings of hash blocks.** -/
theorem units_of_fold_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (zp : ProofFile.InstPub) (s' : S) (rs r : List Fmt.RoundView) (cols c' : List Desc.OpenedColumn),
        foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) (ProofFile.startS Z zp) rs
          cols = .ok (s', r, c') →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ X) s' (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
          kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate_blocks hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 zp s' rs r cols c' hfold
  exact h d he h5 h6 zp s' (reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cols c'
    hfold)

end

end P1K8

#print axioms P1K8.fold_rest
#print axioms P1K8.live_of_fold
#print axioms P1K8.state_of_fold
#print axioms P1K8.front_live
#print axioms P1K8.front_live_blocks
#print axioms P1K8.front_of_fold
#print axioms P1K8.front_of_fold_blocks
#print axioms P1K8.units_of_fold
#print axioms P1K8.units_of_fold_blocks
