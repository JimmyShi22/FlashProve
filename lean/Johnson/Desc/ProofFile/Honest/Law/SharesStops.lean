-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesStops.lean: the stops' shares, at `honestBatchProverOfFile`
(Honest/StratC.lean). Suppose that each part's gate for the first stop fires, over its own rounds'
typed messages, with probability at most the part's number, at every list of challenges heard before
the part's own. Then the probability of the set `Bad` of `honestBatchProverOfFile`'s one-slot form (`one`) is at
most the sum of the parts' numbers (`bad_held`). The same holds for the second stop and `Hid`, at
each input (`hid_held`), and so for the abort set (`withheld`): for each private input and instance,
the set `Bad ∪ Hid w x` of verifier's messages (`withheld_held`). The numbers are the stated shares'
values (`Odds.val`, Honest/Law/SharesHeld.lean).

What this is. Conditional lemmas about the stops of Honest/Frame.lean and the library's own
probability (`Iop.prRho`). No run and no coin occurs in them. None of the library's goals.
Probabilities are over the verifier's messages, drawn uniformly (`Iop.prRho`), at a fixed private
input and instance.

Trivially met. A stated share of 1 of 1 satisfies the hypothesis at every stop; at shares that add
up to 1 or more the bounds say nothing.

  1  `stop_bare`, `stop_lastBare`   sub-protocols without a prover's side; the first chain without
     its last sub-protocol
  2  `isSome_or'`, `hid_or`   the two values of the parameter `sp`
  3  `StopsFit`   what is asked of the description, the prover and the data: tests and counts
  4  `bad_held`, `hid_held`, `withheld_held`   the three main lemmas

Limits.
  * The first chain's sealing round has no typed message (its challenge is the fixed empty one). A
    prover's side at that sub-protocol would have stops that no gate counts. That there is none is a
    hypothesis (`StopsFit.bare`), an executable test.
  * The hypotheses `ChainHeld` are stated gate by gate (Honest/Law/SharesChain.lean).
  * The sums are sums of the gates' numbers in the library's ℝ≥0∞. That they are the value of
    `statedShares` is not proved.
  * The numbers are fixed to the stated shares' values. At a kit at which several typed challenges
    are shown as one value, a share that is stated as an exact quotient of a count may not be what
    the probability gives. Then the hypothesis fails, and the share has to be stated anew.
  * The kit C of verifier's messages is a parameter. How a probability over its typed challenges
    follows from a count of what they show depends on the kit, and is not treated here.
  * Nothing here asks that a share's denominator is not 0 (`Odds.ok`): at such a share `Odds.val` is
    read all the same.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesFile
import Johnson.Desc.ProofFile.Honest.Law.StopsC
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 S Cl V W Y : Type}

/-! ## 1 Sub-protocols without a prover's side -/

theorem stop_bare (v : Option V) (hs : List (Placed V W Y)) : ∀ (bs : List (Block S Cl))
    (loc ds : List Fmt.Drawn), (∀ b ∈ bs, (hs.find? fun h => h.place == b.place) = none) →
    chainStopAt v bs hs loc ds = none
  | [], _, _, _ => rfl
  | b :: bs, loc, ds, h => by
    show ((hs.find? fun g => g.place == b.place).bind fun g =>
      rowStopAt v g.parts loc (ds.take b.rounds.length)).or
        (chainStopAt v bs hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length)) = none
    rw [h b List.mem_cons_self, stop_bare v hs bs _ _ (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    rfl

/-- A chain whose last sub-protocol has no prover's side stops where the sub-protocols before it
stop. -/
theorem stop_lastBare (v : Option V) (hs : List (Placed V W Y)) (pre : List (Block S Cl))
    (e : Block S Cl) (he : (hs.find? fun h => h.place == e.place) = none)
    (loc dr tail : List Fmt.Drawn) (hl : dr.length = (pre.flatMap (·.rounds)).length) :
    chainStopAt v (pre ++ [e]) hs loc (dr ++ tail) = chainStopAt v pre hs loc dr := by
  rw [chainStopAt_append, stop_bare v hs [e] _ _ (fun b hb => by
    rw [List.mem_singleton.1 hb]
    exact he), List.take_left' hl]
  cases chainStopAt v pre hs loc dr <;> rfl

/-! ## 2 The two values of `sp` -/

theorem isSome_or' (a b : Option Why) (h : (a.or b).isSome = true) :
    a.isSome = true ∨ b.isSome = true := by
  cases a with
  | none => exact Or.inr h
  | some _ => exact Or.inl rfl

theorem hid_or (a b : Option Why) (h : (a.or b == some Why.hid) = true) :
    (a == some Why.hid) = true ∨ (b == some Why.hid) = true := by
  cases a with
  | none => exact Or.inr h
  | some _ => exact Or.inl h

/-! ## 3 What is asked of the description, the prover and the data -/

/-- **The counts fit.** `pre₁`, `e₁`: the first chain's sub-protocols before its last, and the last,
which is meant to hold the sealing round; its number of rounds is not asked here. A structure of
hypotheses: executable tests and counts. -/
structure StopsFit (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (D : WholeD)
    (pre₁ : List (Block F.S₁ F.Cl)) (e₁ : Block F.S₁ F.Cl) : Prop where
  cut : F.first.blocksInOrder = pre₁ ++ [e₁]
  bare : (H.first.find? fun h => h.place == e₁.place) = none
  l₁ : D.ds₁.length = (pre₁.flatMap (·.rounds)).length
  l₂ : D.ds₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length
  l₃ : D.ds₃.length = (F.second.blocksInOrder.flatMap (·.rounds)).length
  f₁ : HalvesFit H.first pre₁
  f₂ : HalvesFit H.shared F.shared.blocksInOrder
  f₃ : HalvesFit H.second F.second.blocksInOrder

/-! ## 4 The three main lemmas -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
  [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)
  {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl}

/-- **The first stops' shares add up to a bound on `Bad`.** -/
theorem bad_held (Sf : StopsFit F H D pre₁ e₁)
    (h₁ : ChainHeld (·.isSome) (none : Option (Local W₀ Rc Xi Tr)) (·.badShare.val) H.first C pre₁
      D.ds₁)
    (h₂ : ChainHeld (·.isSome) (none : Option Empty) (·.badShare.val) H.shared C F.shared.blocksInOrder
      D.ds₂)
    (h₃ : ChainHeld (·.isSome) (none : Option (Local W₀ Rc Xi Tr)) (·.badShare.val) H.second C
      F.second.blocksInOrder D.ds₃) :
    Iop.prRho (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad ≤
      ((chainGates (·.isSome) (none : Option (Local W₀ Rc Xi Tr)) (·.badShare.val) H.first pre₁
          D.ds₁).map (·.p)).sum +
        (((chainGates (·.isSome) (none : Option Empty) (·.badShare.val) H.shared F.shared.blocksInOrder
          D.ds₂).map (·.p)).sum +
        ((chainGates (·.isSome) (none : Option (Local W₀ Rc Xi Tr)) (·.badShare.val) H.second
          F.second.blocksInOrder D.ds₃).map (·.p)).sum) := by
  refine covered_le C D tF tJ t3 _ _ _ (chain_ds _ _ _ _ _ _ Sf.l₁ Sf.f₁)
    (chain_ds _ _ _ _ _ _ Sf.l₂ Sf.f₂) (chain_ds _ _ _ _ _ _ Sf.l₃ Sf.f₃)
    (fun d₁ _ => d₁ ++ [⟨[], [], [], none⟩]) _ ?_ (gatesHeld_all C _ h₁ [])
    (gatesHeld_all C _ h₂ [])
    (fun _ _ _ _ => gatesHeld_all C _ h₃ _)
  intro ρ hρ
  have hρ' : Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
      (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Bad ∨
      (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).stop0
        (Iop.Rho.sh (chainsOf C D tF tJ t3).ann ρ) = true := hρ
  rw [badC_reads, stop0C_reads] at hρ'
  rcases hρ' with g | g
  · unfold badB at g
    rw [Bool.or_eq_true] at g
    rcases g with g | g
    · left
      have g' : (chainStopAt (none : Option (Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first []
          (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩])).isSome =
          true := g
      rw [Sf.cut, stop_lastBare _ _ _ _ Sf.bare _ _ _ (by rw [drawnT_len, Sf.l₁])] at g'
      exact chain_spoken _ _ _ _ isSome_or' rfl _ _ _ _ Sf.l₁ Sf.f₁ g'
    · right
      right
      exact chain_spoken _ _ _ _ isSome_or' rfl _ _ _ _ Sf.l₃ Sf.f₃ g
  · right
    left
    exact chain_spoken _ _ _ _ isSome_or' rfl _ _ _ _ Sf.l₂ Sf.f₂ g

/-- **The second stops' shares add up to a bound on `Hid`**, at one input. -/
theorem hid_held (Sf : StopsFit F H D pre₁ e₁) (w : W₀ × Rc × Sd) (x : Xi) (z₁ z₃ : ℝ≥0∞)
    (h₁ : ∀ tr, H.trace w.1 x = some tr →
      ChainHeld (· == some Why.hid) (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
        (·.hidShare.val) H.first C pre₁ D.ds₁ ∧
      ((chainGates (· == some Why.hid) (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
        (·.hidShare.val) H.first pre₁ D.ds₁).map (·.p)).sum ≤ z₁)
    (h₃ : ∀ tr, H.trace w.1 x = some tr →
      ChainHeld (· == some Why.hid) (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
        (·.hidShare.val) H.second C F.second.blocksInOrder D.ds₃ ∧
      ((chainGates (· == some Why.hid) (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
        (·.hidShare.val) H.second F.second.blocksInOrder D.ds₃).map (·.p)).sum ≤ z₃) :
    Iop.prRho ((honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x) ≤ z₁ + z₃ := by
  cases htr : H.trace w.1 x with
  | none =>
    refine le_trans (Iop.prRho_empty _ fun ρ hρ => ?_) (zero_le _)
    have hρ' : Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
      (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Hid w x := hρ
    rw [hidC_reads] at hρ'
    unfold hidB at hρ'
    rw [htr] at hρ'
    cases hρ'
  | some tr =>
    obtain ⟨a1, b1⟩ := h₁ tr htr
    obtain ⟨a3, b3⟩ := h₃ tr htr
    have key := covered_le C D tF tJ t3 _ [⟨D.ds₂, fun _ _ => false, 0⟩] _
      (chain_ds _ _ _ _ _ _ Sf.l₁ Sf.f₁) (List.append_nil _) (chain_ds _ _ _ _ _ _ Sf.l₃ Sf.f₃)
      (fun d₁ _ => d₁ ++ [⟨[], [], [], none⟩])
      ((honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x) (fun ρ hρ => by
                       have hρ' : Iop.Rho.lo (chainsOf C D tF tJ t3).ann ρ ∈
                         (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).Hid w x := hρ
                       rw [hidC_reads] at hρ'
                       unfold hidB at hρ'
                       rw [htr] at hρ'
                       have g : (chainStopAt (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr))
                           F.first.blocksInOrder H.first []
                           (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩]) ==
                           some Why.hid ||
                         chainStopAt (Face.own.sees (⟨w.1, w.2.1, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder
                           H.second (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩])
                           (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) == some Why.hid) = true := hρ'
                       rw [Bool.or_eq_true] at g
                       rcases g with g | g
                       · left
                         rw [Sf.cut, stop_lastBare _ _ _ _ Sf.bare _ _ _ (by rw [drawnT_len, Sf.l₁])] at g
                         exact chain_spoken (· == some Why.hid) _ _ _ hid_or rfl _ _ _ _ Sf.l₁ Sf.f₁ g
                       · right
                         right
                         exact chain_spoken (· == some Why.hid) _ _ _ hid_or rfl _ _ _ _ Sf.l₃ Sf.f₃ g)
      (gatesHeld_all C _ a1 [])
      ⟨Iop.prRho_empty _ (fun _ h => by
        have h' : false = true := h
        cases h'), fun _ _ => trivial⟩
      (fun _ _ _ _ => gatesHeld_all C _ a3 _)
    refine le_trans key ?_
    have e0 : (([⟨D.ds₂, fun _ _ => false, 0⟩] : List Gate).map (·.p)).sum = 0 := by simp
    rw [e0, zero_add]
    exact add_le_add b1 b3

/-- **And so for the abort set (`withheld`).** -/
theorem withheld_held (w : W₀ × Rc × Sd) (x : Xi) (zB z : ℝ≥0∞)
    (hb : Iop.prRho (honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad ≤ zB)
    (hz : Iop.prRho ((honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x) ≤ z) :
    Iop.prRho ((honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.withheld w x) ≤ zB + z :=
  le_trans (pr_union_le _ _ _) (add_le_add hb hz)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stop_bare
#print axioms ProofFile.Honest.stop_lastBare
#print axioms ProofFile.Honest.isSome_or'
#print axioms ProofFile.Honest.hid_or
#print axioms ProofFile.Honest.bad_held
#print axioms ProofFile.Honest.hid_held
#print axioms ProofFile.Honest.withheld_held
