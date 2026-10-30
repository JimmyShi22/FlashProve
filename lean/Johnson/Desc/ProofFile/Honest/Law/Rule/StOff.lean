-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/StOff.lean: `StOffAt` (Honest/Law/Rule/OneSim.lean), reduced
to one inclusion (`stOffAt_of`). `StOffAt` says: at a tied pair and a verifier's message whose list
of challenges is such as the rounds can draw, the stored columns that the declared rounds read are
those that the external answers hold. The inclusion, `AsksIn`, says: at a verifier's message whose
list of challenges is such as the rounds can draw, every stored position that the declared rounds
read is below the external string's length and among the positions that the protocol reads of it.

  1  `reads_item`, `asks_item`   a stored read's item is a declared round's
  2  `AsksIn`   the inclusion: a definition, meant as a hypothesis
  3  `stOffAt_of`   the lemma

Limits.
  * The inclusion is a hypothesis here; `asksIn_of` (Honest/Law/BackFile.lean) proves it where the
    description passes its tests on the plan and the data fit it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OneSim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 A stored read's item -/

theorem reads_item (ch ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (i : Nat) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), ∀ q ∈ readsOf ch ft stored tree ds Rs,
    q.item = some i → ∃ d ∈ ds, ∃ s ∈ d.stored, s.item = i
  | [], _, q, hq, _ => by
    simp only [readsOf] at hq
    cases hq
  | _ :: _, [], q, hq, _ => by
    simp only [readsOf] at hq
    cases hq
  | d :: ds, R :: Rs, q, hq, hi => by
    simp only [readsOf] at hq
    rcases List.mem_append.1 hq with hq | hq
    · rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨s, hs, hq⟩ := List.mem_flatMap.1 hq
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
        exact ⟨d, List.mem_cons.2 (Or.inl rfl), s, hs, Option.some.inj hi⟩
      · obtain ⟨o, -, hq⟩ := List.mem_flatMap.1 hq
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
        cases hi
    · obtain ⟨d', hd', s, hs, e⟩ := reads_item ch ft stored tree i ds Rs q hq hi
      exact ⟨d', List.mem_cons_of_mem _ hd', s, hs, e⟩

theorem asks_item (F : FileDescription Xi) (δ : Draws) : ∀ q ∈ storedAsks F δ,
    ∃ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∃ s ∈ d.stored, s.item = q.1 := by
  intro q hq
  unfold storedAsks at hq
  obtain ⟨r, hr, e⟩ := List.mem_filterMap.1 hq
  cases hi : r.item with
  | none =>
    rw [hi] at e
    cases e
  | some i =>
    rw [hi] at e
    have e' : (i, r.pos) = q := Option.some.inj e
    rw [← e']
    unfold allBare bareReads at hr
    rcases List.mem_append.1 hr with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨d, hd, s, hs, es⟩ := reads_item 0 0 _ _ i _ _ r h hi
        exact ⟨d, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hd))), s, hs, es⟩
      · obtain ⟨d, hd, s, hs, es⟩ := reads_item 1 0 _ _ i _ _ r h hi
        exact ⟨d, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hd))), s, hs, es⟩
    · obtain ⟨d, hd, s, hs, es⟩ := reads_item 2 F.lastChainFirstTreeNumber _ _ i _ _ r h hi
      exact ⟨d, List.mem_append.2 (Or.inr hd), s, hs, es⟩

/-! ## 2 The inclusion; the lemma -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool)

/-- At every instance, and at a verifier's message whose list of challenges is such as the rounds
can draw: every stored position that the declared rounds read is below the external string's length
and among the positions that the protocol reads of it. A definition, meant as a hypothesis. -/
def AsksIn : Prop :=
  ∀ (x : Xi) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh), (drawsAt C D tF tJ t3 ρ).due F = true →
    ∀ q ∈ storedAsks F (drawsAt C D tF tJ t3 ρ),
    ∃ h : q.2 < 2 ^ D.a, (⟨q.2, h⟩ : Fin (2 ^ D.a)) ∈ (batchOf C D tF tJ t3 F silent).loc.extReads x
        ρ

variable {C D tF tJ t3 F silent} [Inhabited R3] {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3} {sh : Ky → F.S₂}
  {ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str} {pubJ : R2 → R3 → Xi → TF × TJ × T3}
  {Rel : W₀ → Rc → Xi → Prop}

/- `AsksIn` gives `StOffAt`, at every H, J, sh, ext, pubJ and Rel. -/
theorem stOffAt_of (hin : AsksIn C D tF tJ t3 F silent) :
    StOffAt C D tF tJ t3 F silent H J sh ext pubJ Rel := by
  intro w x hv ρ hdue
  unfold storedShown stOff
  refine List.filterMap_congr fun q hq => ?_
  obtain ⟨h, hm⟩ := hin x ρ hdue q hq
  obtain ⟨d, hd, s, hs, es⟩ := asks_item F _ q hq
  rw [dif_pos h, ← es, hv.table d hd s hs q.2 h]
  unfold Iop.InteractiveOracleProof.extAns
  split
  · rfl
  · rename_i hn
    exact absurd hm hn

end

end ProofFile.Honest

#print axioms ProofFile.Honest.reads_item
#print axioms ProofFile.Honest.asks_item
#print axioms ProofFile.Honest.stOffAt_of
