-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Proofs of statements of Johnson/Desc/Sound/SharedOnce.lean.
import Johnson.Desc.Sound.SharedOnce
import Johnson.Desc.Sound.SharedOwnProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem relsOfActs : RelsOfActs := by
  intro S Cl W C F p act act' o' ρ ρ' he
  exact ⟨fun b b' e h => e ▸ h, fun a a' w e h => e ▸ h, fun b b' w e h => e ▸ h, he⟩

/-- The law for N slots gives the clause at the acting part itself. -/
theorem paysN_of_lostBy (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) (N : ℕ) (h : p.LostBy on on' R R' act) :
    p.PaysN N on on' R R' act := by
  obtain ⟨lost, hD, hb⟩ := h
  exact Iop.knowB_of_lost S S act.1 F.E F.E W W p.ior N act.2 lost on R
    (Reduction.orOff on' R') p.ext p.err hD
    (fun a τ b w ha hl ho hw =>
      (hb a τ b ha hl ho).2 w (hw.elim id fun n => absurd (hb a τ b ha hl ho).1 n))

theorem onceOfGoodIn : OnceOfGoodIn := by
  intro S S₀ Cl W C F get set b₀ p lo N on o' ρ ρ' Rc hb g1 g2 ho hg he hk
  have hh := liftHands S S₀ Cl W C F get set b₀ p lo hb g1 g2 ho
  have hr := relsOfActs S Cl W C F p _ _ o' ρ ρ' he
  exact paysN_of_lostBy p _ _ _ _ _ N
    (lostBeside S Cl W C F p _ _ _ _ Rc _ (lostOfGoodIn S Cl W C F p _ _ _ _ _ _ hg ⟨hh, hr⟩) hk)

theorem paysCarry : PaysCarry := by
  rintro S Cl W C F p N on on' oc R R' act ⟨bad, hc, hJ⟩ hoc
  refine ⟨bad, fun a τ b w ha hτ hb hw => hc a τ b w ha.1 hτ hb ?_, hJ⟩
  rcases hw with hw | hn
  · exact Or.inl hw
  · exact Or.inr fun h => hn ⟨h, hoc a τ b ha.2 hb⟩

theorem eachRels_of_acts (act : ℕ → BKey F S) (on : ℕ → S × F.E.Str → Prop)
    (ρ : ∀ k, (act k).1 → W → Prop) (i₀ : ℕ)
    (hon : ∀ k b b', i₀ < k → (act k).2 b = (act k).2 b' → on k b → on k b') :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), i₀ ≤ i → EachExtBy act i l →
      EachRels on (fun k a w => ρ k ((act k).2 a) w) act i l
  | [], _, _, _ => trivial
  | _ :: l, i, hi, h =>
    ⟨⟨fun b b' => hon (i + 1) b b' (Nat.lt_succ_of_le hi),
        fun a a' w e (k : ρ i ((act i).2 a) w) => (show ρ i ((act i).2 a') w from e ▸ k),
        fun b b' w e (k : ρ (i + 1) ((act (i + 1)).2 b) w) =>
          (show ρ (i + 1) ((act (i + 1)).2 b') w from e ▸ k), h.1⟩,
      eachRels_of_acts act on ρ i₀ hon l (i + 1) (Nat.le_succ_of_le hi) h.2⟩

theorem eachPaysN_of_lost (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (act : ℕ → BKey F S) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachLost on R act i l → EachPaysN N on R act i l
  | [], _, _ => trivial
  | p :: l, i, h => ⟨paysN_of_lostBy p _ _ _ _ _ N h.1, eachPaysN_of_lost N on R act l (i + 1) h.2⟩

theorem rowOnce : RowOnce := by
  intro S S₀ Cl W C F get set lo N i act p l on o ρ Rc ha ht g1 g2 hb ho hon hg he hk
  have hr := eachRels_of_acts act on ρ i
    (fun k b b' hk e h => by
      rw [hon k hk] at h ⊢
      have h' : o k ((act k).2 b) := h
      show o k ((act k).2 b')
      exact e ▸ h') (p :: l) i (Nat.le_refl i) he
  obtain ⟨h1, -⟩ := each_own on _ Rc get set g1 g2 lo l p i act ha ht hg hr hk hb ho
  exact eachPaysN_of_lost N _ _ _ _ i h1

theorem tailActs : TailActs := by
  intro S S₀ Cl W C F get lo p q l k
  show actAt F get lo (hiAt (1 + k) p (q :: l)) = _
  rw [Nat.add_comm]
  rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.relsOfActs
#print axioms VerifiableInference.Desc.Sound.paysN_of_lostBy
#print axioms VerifiableInference.Desc.Sound.onceOfGoodIn
#print axioms VerifiableInference.Desc.Sound.rowOnce
#print axioms VerifiableInference.Desc.Sound.tailActs
#print axioms VerifiableInference.Desc.Sound.paysCarry
