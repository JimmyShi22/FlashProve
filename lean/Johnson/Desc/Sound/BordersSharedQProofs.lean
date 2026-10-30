-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- The proof of the statement `SharedJoin` of Johnson/Desc/Sound/BordersSharedQ.lean.
import Johnson.Desc.Sound.BordersSharedQ
import Johnson.Desc.Sound.SpineOnceProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)
open VerifiableInference.Desc.Shared

theorem ownAt_behind (k : ℕ) (h : 2 ≤ k) : ownAt k = ownAt 2 := by
  have h1 : ¬ k ≤ pointAt := by
    show ¬ k ≤ 1
    omega
  have h2 : ¬ 2 ≤ pointAt := by
    show ¬ 2 ≤ 1
    omega
  unfold ownAt
  rw [if_neg h1, if_neg h2]

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))

theorem relOwn_behind (k : ℕ) (h : 2 ≤ k) :
    relOwn (Fr := Fr) N Mg k = relOwn (Fr := Fr) N Mg 2 := by
  unfold relOwn
  rw [ownAt_behind k h]

theorem eachPaysN_turn (n : ℕ) :
    ∀ (m : List (Piece C Fr (P₁ × S₂) Cl Wt)) (i : ℕ), 2 ≤ i →
      EachPaysN n (fun k a => promQ N Pm split p l k ((actQ N p l k).2 a))
        (fun k a w => relSh (actQ N p l) (muQ N Mg p l)
          (openAfter (insSh split) (outsSh split) startSh k) k a w ∧
            relOwn N Mg 2 a w) (actQ N p l) i m →
      (∀ x ∈ m, ∀ a τ b, Oc a.1.1 (strsOf Fr a.2) → x.ior.red.out a τ = some b →
        Oc b.1.1 (strsOf Fr b.2)) →
      EachPaysN n (onQ₂ N Pm Oc split p l) (relQ₂ N Mg split p l) (actQ N p l) i m
  | [], _, _, _, _ => trivial
  | x :: m, i, hi, h, hc => by
    refine ⟨?_, eachPaysN_turn n m (i + 1) (Nat.le_succ_of_le hi) h.2
      fun y hy => hc y (List.mem_cons_of_mem _ hy)⟩
    have k := paysCarry _ _ _ _ _ x n _ _ (fun a => Oc a.1.1 (strsOf Fr a.2)) _ _ _ h.1
      (hc x (List.mem_cons_self ..))
    unfold relQ₂
    rw [relOwn_behind N Mg i hi, relOwn_behind N Mg (i + 1) (Nat.le_succ_of_le hi)]
    exact k

end

theorem sharedJoin : SharedJoin := by
  intro P₁ S₂ Cl Wt C Fr N Mg Pm Oc split n f pt q r ht hb ho hO hF he hk hc
  have h := spineOnce (P₁ × S₂) S₂ Cl Wt ItemS C Fr Prod.snd (fun t s => (t.1, s))
    N.lo n 2 (actQ N f (pt :: q :: r)) q r
    (fun k a => promQ N Pm split f (pt :: q :: r) k ((actQ N f (pt :: q :: r) k).2 a))
    (fun k v => promQ N Pm split f (pt :: q :: r) k v) (muQ N Mg f (pt :: q :: r))
    (relOwn N Mg 2) (insSh split) (outsSh split) startSh
    (fun k => by
      show actAt Fr Prod.snd N.lo (hiAt (2 + k) f (pt :: q :: r)) = _
      rw [Nat.add_comm]
      rfl)
    ht (fun _ _ => rfl) (fun _ _ _ => rfl) hb ho (fun _ _ => rfl) hO hF he hk
  exact eachPaysN_turn N Mg Pm Oc split f (pt :: q :: r) n (q :: r) 2 (Nat.le_refl 2) h hc

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.sharedJoin
