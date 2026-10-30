-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverInside.lean: A FALL WHOSE EVENT LIES INSIDE ANOTHER FALL's IS
COUNTED ONCE. `debt_join` (Honest/Law/CoverJoin.lean) adds one number for each fall of a chain's
list. Where two owners' falls at one member ask one test of one state, the same event would be
counted twice. Here the joiner with a list of representatives: an owner whose fall's event lies, at
what P lets in, inside that of another owner's fall hands in THAT IMPLICATION in the place of a
count.

WHAT THIS IS. A conditional lemma on definitions and on the library's own measure:
`debt_join`'s proof, cut by program, with one step more. At reps := the whole list and the identity
it says what `debt_join` says. None of the library's goals.

  `debt_join_in`

Limits. As `debt_join`'s. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

section
variable (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)

/-- **THE JOINER, WHERE SOME FALLS' EVENTS LIE INSIDE OTHERS'.** As `debt_join`; reps: the falls
that are counted. hin: each fall of the chain's list has, at what P lets in, its event inside that
of a fall of reps. -/
theorem debt_join_in (bs : List (Block S Cl)) {b : Block S Cl} {t : List (Block S Cl)} {j n : Nat}
    {dsb : List RDT} {tl : List Fmt.Drawn} {last : Bool} {ft : Nat} (hj : bs[j]? = some b)
    (hn : n = ((bs.take j).flatMap (·.rounds)).length) (hlen : dsb.length = b.rounds.length)
    (PM : List Fmt.Drawn → Prop) (P : List Fmt.Drawn → S → Prop) (qM : Mark → ℝ≥0∞)
    (qF : Fall S → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), MarkDebt C mk dsb PM (qM mk))
    (reps : List (Fall S)) (hF : ∀ f ∈ reps, FallDebt C f ft b t dsb tl P (qF f))
    (hin : ∀ f ∈ fs, ∃ g ∈ reps, ∀ fr s' own, P fr s' → localFall [f] ft (b :: t) s' own →
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
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb tl last := by
  intro fr h1 h2 h3 h4
  refine ⟨le_trans ?_ hp, fun _ ρ hm _ => silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn])
    (by rw [drawnT_len, hlen]) h4 hm⟩
  have bM := pr_any_le C dsb (fun (mk : Mark) ρ => (mk.test fr (drawnT C dsb ρ)).isSome = true) qM
    (ms.filter fun m => m.place == b.place) fun mk hmk => hM mk hmk fr (hPM fr h1 h2 h3 h4)
  by_cases hz : ∃ a z s', (X (fr.take skip)).start = some a ∧
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z ∧
      z.ver = some s'
  · obtain ⟨a, z, s', z1, z2, z3⟩ := hz
    obtain ⟨g1, g2, g3, g4⟩ := hfront fr a z s' h1 h2 h3 h4 z1 z2 z3
    have bF := pr_any_le C dsb
      (fun (f : Fall S) ρ => localFall [f] ft (b :: t) s' (drawnT C dsb ρ ++ tl)) qF reps
      fun f hf => hF f hf fr s' g4
    refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _) (add_le_add bM bF))
    intro ρ hρ
    rcases hρ with hm | ⟨a', z', s'', y1, y2, y3, y4⟩
    · exact Or.inl (markOf_mem hm)
    · rw [z1] at y1
      cases y1
      rw [z2] at y2
      cases y2
      rw [z3] at y3
      cases y3
      obtain ⟨f, hf, hr⟩ := runFall_mem y4
      have hl := run_local hr
      rw [g1, g2, g3] at hl
      obtain ⟨g, hg, hgi⟩ := hin f hf
      exact Or.inr ⟨g, hg, hgi fr s' _ g4 hl⟩
  · refine le_trans (le_trans (pr_mono _ ?_) bM) (le_add_right le_rfl)
    intro ρ hρ
    rcases hρ with hm | ⟨a', z', s'', y1, y2, y3, -⟩
    · exact markOf_mem hm
    · exact absurd ⟨a', z', s'', y1, y2, y3⟩ hz


end

end ProofFile.Honest

#print axioms ProofFile.Honest.debt_join_in
