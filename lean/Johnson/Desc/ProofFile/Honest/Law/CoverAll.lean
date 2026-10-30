-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverAll.lean: THE FALLS' NUMBER FROM BOUNDS A MEMBER, AT A FILE.
At one input and one run's coins: where each member's event has at most the member's number as its
measure (`LocalDebts`, Honest/Law/CoverHeld.lean), chain by chain, and no chain's start has met a
fall, the letters Q hold at the starts, `ready` returns R, `StopsFit` holds and pre₁ is not the
empty list, the typed verifier's messages at which the honest run meets a fall (`fallAt`,
Honest/Fall.lean) have at most the sum of the members' numbers as their measure. `falls_held_canon`
(Honest/Law/CoverFile.lean) with its three premises paid by `canon_held`.

WHAT THIS IS. A conditional lemma on our own fold and the library's own measure (`Iop.prRho`), at
one input and one run's coins. None of the library's goals.

MET FOR NOTHING. A number of 1 somewhere. A letter Q that is False at a chain's start. NO LOCAL
BOUND IS SHOWN HERE OF ANY REAL FALL OR MARK. `falls_local` HAS ONE MEMBER: A TOY's
(Honest/Law/ToyLocal.lean, another author's of this folder; not in the sealed library; not built
over the frame as it stands: `falls_le_rowH`: a small row with one fall, in the shared chain, no
stop, under a toy kit).

  1  `at₁_starts`, `at₂_starts`, `at₃_starts`   the three chains' walks start as `canon_held` asks.
     The columns handed stand under «∃»: `canon_held` asks no more. They are `runC`'s own: `[]`,
     `[]`, and the first two chains' columns (`at₁`, `at₂`, `at₃`, Honest/Law/CoverFile.lean);
     `letter_starts` (Honest/Law/CoverLetter.lean) names the first chain's
  2  `falls_local`   the law

Limits. THE FALLS' LAWS STAND AT ONE INPUT AND ONE RUN's COINS k. The library's own forms of
completeness (`Honest.Acc`, Iop/InteractiveOracleProof.lean; `BatchProtocol.Complete`, Iop/Batch.lean) ask acceptance AT EVERY
COIN outside a set of verifier's messages that no coin enters. A bound at each k does not bound {ρ |
at SOME k the run meets a fall}: so these numbers have no seat in these two forms. Where they can
land: in a form that takes a fall's set at each fixed coin and asks ONE NUMBER FOR ALL COINS (the
library's `HonFit`, Johnson/Prover/All/OfHonest.lean: by its authors' word, held by no lemma of
ours); and in a share over the message and the coins together (Honest/Law/SharesMean.lean). The
numbers are letters: NO STATED SHARE OF A FALL OR A MARK IS IN THE LAW. The second chain's debts are
asked at every front that Q₃ lets in; s₃ alone stands at the pairs of the first two chains' typed
messages at which none of their gates has spoken. `StopsFit` is taken whole; of it the three counts
alone are spent. Nothing says that a state in front meets a thread's sentence
(Honest/Law/CoverThread.lean [not in this library; so here read: not proved in this library] joins
that). This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeld
import Johnson.Desc.ProofFile.Honest.Law.RunC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

/-! ## 1 The three chains' walks start as `canon_held` asks -/

section
variable (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
  (R : Ready W₀ Rc Xi Ky Tr X₀ X)

theorem toOption_some {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e with
  | error _ => cases h
  | ok b =>
    cases h
    rfl

theorem at₁_starts (a : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (s₀ : F.S₁)
    (hs : (at₁ F P w₀ rc x R).start = some a) (h0 : (at₁ F P w₀ rc x R).s₀ = some s₀) :
    ∃ (m₀ : Option (Mid (Local W₀ Rc Xi Tr) X)) (front : List OpenedColumn), m₀.isSome = true ∧
      ChainProgress.start (at₁ F P w₀ rc x R).lay F.first.blocksInOrder m₀ (some s₀) front = .ok a := by
  have h0' : some (F.start₁ (F.pub x)) = some s₀ := h0
  cases h0'
  exact ⟨some (R.start₁ P), [], rfl, toOption_some hs⟩

theorem at₂_starts (a : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀) (s₀ : F.S₂)
    (hs : (at₂ F P w₀ rc x R).start = some a) (h0 : (at₂ F P w₀ rc x R).s₀ = some s₀) :
    ∃ (m₀ : Option (Mid (Common W₀ Rc Ky) X₀)) (front : List OpenedColumn), m₀.isSome = true ∧
      ChainProgress.start (at₂ F P w₀ rc x R).lay F.shared.blocksInOrder m₀ (some s₀) front = .ok a := by
  have h0' : some (F.start₂ (F.pub x)) = some s₀ := h0
  cases h0'
  exact ⟨some (R.start₂ P), [], rfl, toOption_some hs⟩

theorem at₃_starts (n₁ : Nat) (base : List Fmt.Drawn)
    (a : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X) (s₀ : F.S₃)
    (hs : (at₃ F P w₀ rc x R n₁ base).start = some a)
    (h0 : (at₃ F P w₀ rc x R n₁ base).s₀ = some s₀) :
    ∃ (m₀ : Option (Mid (Local W₀ Rc Xi Tr) X)) (front : List OpenedColumn), m₀.isSome = true ∧
      ChainProgress.start (at₃ F P w₀ rc x R n₁ base).lay F.second.blocksInOrder m₀ (some s₀) front = .ok a := by
  unfold at₃ at hs h0 ⊢
  cases u1 : (at₁ F P w₀ rc x R).start.bind fun a =>
      (walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ R.first (base.take n₁ ++ [noDraw])
        a).toOption with
  | none =>
    rw [u1] at hs
    cases hs
  | some z₁ =>
    cases u2 : (at₂ F P w₀ rc x R).start.bind fun a =>
        (walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ R.shared (base.drop n₁) a).toOption with
    | none =>
      rw [u1, u2] at hs
      cases hs
    | some z₂ =>
      rw [u1, u2] at hs h0
      simp only at hs h0 ⊢
      obtain ⟨a₁, ha₁, hz₁⟩ := Option.bind_eq_some_iff.1 u1
      obtain ⟨a₂, ha₂, hz₂⟩ := Option.bind_eq_some_iff.1 u2
      have b1 := walk_both _ _ _ a₁ z₁ (start_both _ _ _ _ (toOption_some ha₁))
        (toOption_some hz₁)
      have b2 := walk_both _ _ _ a₂ z₂ (start_both _ _ _ _ (toOption_some ha₂))
        (toOption_some hz₂)
      refine ⟨_, _, ?_, by rw [← h0]; exact toOption_some hs⟩
      cases hv₁ : z₁.ver with
      | none =>
        rw [hv₁] at h0
        cases h0
      | some e₁ =>
        cases hv₂ : z₂.ver with
        | none =>
          rw [hv₁, hv₂] at h0
          cases h0
        | some e₂ =>
          rw [hv₁] at b1
          rw [hv₂] at b2
          obtain ⟨m₁, hm₁⟩ := Option.isSome_iff_exists.1 b1
          obtain ⟨m₂, hm₂⟩ := Option.isSome_iff_exists.1 b2
          rw [hm₁, hm₂]
          rfl

end

/-! ## 2 The law -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {Bk : ProverCoinCounts}
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
  (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (ms₁ ms₂ ms₃ : List Mark) (p₁ p₂ p₃ : Nat → ℝ≥0∞)
  (Q₁ Q₂ Q₃ : Nat → List Fmt.Drawn → Prop) {pre₁ : List (Block F.S₁ F.Cl)}
  {e₁ : Block F.S₁ F.Cl}

/-- **THE FALLS' NUMBER FROM BOUNDS A MEMBER.** s₁, s₂, s₃: no chain's start has met a fall. q₁, q₂:
the letters Q hold at the first two starts; s₃ carries Q₃ at the third start, at the pairs at which
no gate of the first two chains has spoken. d₁, d₂, d₃: the debts, one a member. -/
theorem falls_local (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (s₁ : fellBy F.first.blocksInOrder G.falls₁ (at₁ F (G.prover H) w₀ rc x R) 0 [] = false) (q₁ : Q₁ 0 [])
    (d₁ : LocalDebts C F.first.blocksInOrder G.falls₁ ms₁ 0 (fun _ => at₁ F (G.prover H) w₀ rc x R) p₁
      [noDraw] Q₁ pre₁ 0 0 D.ds₁)
    (s₂ : fellBy F.shared.blocksInOrder G.falls₂ (at₂ F (G.prover H) w₀ rc x R) 0 [] = false) (q₂ : Q₂ 0 [])
    (d₂ : LocalDebts C F.shared.blocksInOrder G.falls₂ ms₂ 0 (fun _ => at₂ F (G.prover H) w₀ rc x R) p₂ []
      Q₂ F.shared.blocksInOrder 0 0 D.ds₂)
    (s₃ : ∀ (a : Iop.Rho (uLT C D.ds₁)) (b : Iop.Rho (uLT C D.ds₂)),
      spoken (gates₁ D G H w₀ rc x R ms₁ p₁ pre₁) [] (drawnT C D.ds₁ a) = false →
      spoken (gates₂ D G H w₀ rc x R ms₂ p₂) [] (drawnT C D.ds₂ b) = false →
      fellBy F.second.blocksInOrder G.falls₃
        (at₃ F (G.prover H) w₀ rc x R D.ds₁.length (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b)) 0 [] =
        false ∧ Q₃ 0 (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b))
    (d₃ : LocalDebts C F.second.blocksInOrder G.falls₃ ms₃ (D.ds₁.length + D.ds₂.length)
      (at₃ F (G.prover H) w₀ rc x R D.ds₁.length) p₃ [] Q₃ F.second.blocksInOrder 0 0 D.ds₃) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R ms₁ p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R ms₂ p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R ms₃ p₃).map (·.p)).sum) := by
  refine falls_held_canon C D tF tJ t3 G H w₀ rc x k R ms₁ ms₂ ms₃ p₁ p₂ p₃ hR Sf hne ?_ ?_ ?_
  · exact canon_held C F.first.blocksInOrder G.falls₁ ms₁ 0 (fun _ => at₁ F (G.prover H) w₀ rc x R) p₁
      [noDraw] Q₁ (fun _ a s₀ => at₁_starts F (G.prover H) w₀ rc x R a s₀) pre₁ 0 0 D.ds₁ [] Sf.l₁
      (Nat.zero_le _) rfl s₁ q₁ d₁
  · exact canon_held C F.shared.blocksInOrder G.falls₂ ms₂ 0 (fun _ => at₂ F (G.prover H) w₀ rc x R) p₂ [] Q₂
      (fun _ a s₀ => at₂_starts F (G.prover H) w₀ rc x R a s₀) F.shared.blocksInOrder 0 0 D.ds₂ [] Sf.l₂
      (Nat.zero_le _) rfl s₂ q₂ d₂
  · intro a b ha hb
    obtain ⟨u1, u2⟩ := s₃ a b ha hb
    have hl : (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b).length = D.ds₁.length + D.ds₂.length := by
      rw [List.length_append, drawnT_len, drawnT_len]
    have t1 : (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b).take (D.ds₁.length + D.ds₂.length) =
        drawnT C D.ds₁ a ++ drawnT C D.ds₂ b := by rw [← hl, List.take_length]
    have t2 : (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b).drop (D.ds₁.length + D.ds₂.length) = [] := by
      rw [← hl, List.drop_length]
    exact canon_held C F.second.blocksInOrder G.falls₃ ms₃ (D.ds₁.length + D.ds₂.length)
      (at₃ F (G.prover H) w₀ rc x R D.ds₁.length) p₃ [] Q₃
      (fun base a s₀ => at₃_starts F (G.prover H) w₀ rc x R D.ds₁.length base a s₀)
      F.second.blocksInOrder 0 0 D.ds₃ _ Sf.l₃ (Nat.le_of_eq hl.symm) (by rw [t2]; rfl)
      (by rw [t1, t2]; exact u1) u2 d₃

end

end ProofFile.Honest

#print axioms ProofFile.Honest.toOption_some
#print axioms ProofFile.Honest.at₁_starts
#print axioms ProofFile.Honest.at₂_starts
#print axioms ProofFile.Honest.at₃_starts
#print axioms ProofFile.Honest.falls_local
