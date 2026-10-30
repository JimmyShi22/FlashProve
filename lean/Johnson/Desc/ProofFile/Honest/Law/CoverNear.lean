-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverNear.lean: AT A BUSY MEMBER ONLY THE FALLS OF ITS OWN GROUP
ARE ASKED FOR. `debt_join_in` (Honest/Law/CoverInside.lean) joins a member's debt from the counted
falls' sentences, and asks of EVERY fall of the chain's list a counted fall whose event holds its
own. The chain's list holds the falls of all segments; at one member b all but a few sit far off:
neither at b nor at a member without a round right behind it (`groupOf`, Honest/Law/CoverNone.lean):
such a fall owes 0 at b's gate (`fallDebt_none`, Honest/Law/CoverJoin.lean). Here the joiner with
that said once: the premise on the events is asked of the falls that sit in b's group alone, and the
far falls add nothing to the number.

WHAT THIS IS. A lemma on definitions of ours: a call of `debt_join_in` at the counted falls with the
far ones laid beside them, each at 0. None of the library's goals.

  `far_of_any`, `debt_join_near`

Limits. Where no fixed challenge stands behind b's own (so not at a chain's last gated member).
Called here at no description. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- The test «it sits in the list's places» says no: it sits at none of them. -/
theorem far_of_any {f : Fall S} {l : List (Block S Cl)}
    (h : (l.any fun d => f.place == d.place) = false) : ∀ d ∈ l, f.place ≠ d.place := by
  intro d hd e
  have h1 := List.any_eq_false.1 h d hd
  rw [e] at h1
  exact h1 (beq_self_eq_true d.place)

/-- **THE JOINER AT A BUSY MEMBER.** As `debt_join_in`; hin is asked of the falls that sit in b's
group alone. -/
theorem debt_join_near (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark)
    (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (bs : List (Block S Cl)) {b : Block S Cl} {t : List (Block S Cl)} {j n : Nat}
    {dsb : List RDT} {last : Bool} {ft : Nat} (hj : bs[j]? = some b)
    (hn : n = ((bs.take j).flatMap (·.rounds)).length) (hlen : dsb.length = b.rounds.length)
    (PM : List Fmt.Drawn → Prop) (P : List Fmt.Drawn → S → Prop) (qM : Mark → ℝ≥0∞)
    (qF : Fall S → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), MarkDebt C mk dsb PM (qM mk))
    (reps : List (Fall S)) (hF : ∀ f ∈ reps, FallDebt C f ft b t dsb [] P (qF f))
    (hin : ∀ f ∈ fs, (∃ d ∈ groupOf b t, f.place = d.place) →
      ∃ g ∈ reps, ∀ fr s' own, P fr s' → localFall [f] ft (b :: t) s' own →
        localFall [g] ft (b :: t) s' own)
    (hPM : ∀ fr, skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → silentQ ms skip bs j fr → PM fr)
    (hfront : ∀ fr a z s', skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → silentQ ms skip bs j fr →
      (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z →
      z.ver = some s' →
      z.todo = b :: t ∧ z.own = [] ∧ (X (fr.take skip)).lay.firstTree = ft ∧ P fr s')
    (hp : ((ms.filter fun m => m.place == b.place).map qM).sum + (reps.map qF).sum ≤ p j) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb [] last := by
  let near : Fall S → Bool := fun f => (groupOf b t).any fun d => f.place == d.place
  let qF' : Fall S → ℝ≥0∞ := fun f => if near f = true then qF f else 0
  have hfar : ∀ f, near f = false → FallDebt C f ft b t dsb [] P (qF' f) := fun f h =>
    fallDebt_none C f ft b t dsb hlen (far_of_any h) P _
  have hF' : ∀ f ∈ reps ++ fs.filter (fun f => !near f),
      FallDebt C f ft b t dsb [] P (qF' f) := by
    intro f hf
    cases hnf : near f with
    | false => exact hfar f hnf
    | true =>
      rcases List.mem_append.1 hf with h1 | h1
      · have e : qF' f = qF f := if_pos hnf
        rw [e]
        exact hF f h1
      · have h2 := (List.mem_filter.1 h1).2
        rw [hnf] at h2
        cases h2
  have hin' : ∀ f ∈ fs, ∃ g ∈ reps ++ fs.filter (fun f => !near f), ∀ fr s' own, P fr s' →
      localFall [f] ft (b :: t) s' own → localFall [g] ft (b :: t) s' own := by
    intro f hf
    cases hnf : near f with
    | false =>
      exact ⟨f, List.mem_append_right _ (List.mem_filter.2 ⟨hf, by rw [hnf]; rfl⟩),
        fun _ _ _ _ h => h⟩
    | true =>
      obtain ⟨d, hd, he⟩ := List.any_eq_true.1 hnf
      obtain ⟨g, hg, h⟩ := hin f hf ⟨d, hd, eq_of_beq he⟩
      exact ⟨g, List.mem_append_left _ hg, h⟩
  have hs1 : (reps.map qF').sum ≤ (reps.map qF).sum := by
    refine List.sum_le_sum fun f _ => ?_
    show (if near f = true then qF f else 0) ≤ qF f
    split
    · exact le_refl _
    · exact zero_le _
  have hs2 : ((fs.filter fun f => !near f).map qF').sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    have h2 := (List.mem_filter.1 hf).2
    have h3 : near f = false := by
      cases hnf : near f with
      | false => rfl
      | true =>
        rw [hnf] at h2
        cases h2
    exact if_neg (by rw [h3]; exact Bool.false_ne_true)
  refine debt_join_in C all fs ms skip X p bs hj hn hlen PM P qM qF' hM
    (reps ++ fs.filter fun f => !near f) hF' hin' hPM hfront ?_
  rw [List.map_append, List.sum_append, hs2, add_zero]
  exact le_trans (add_le_add (le_refl _) hs1) hp

end ProofFile.Honest

#print axioms ProofFile.Honest.far_of_any
#print axioms ProofFile.Honest.debt_join_near
