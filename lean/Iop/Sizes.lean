-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Sizes.lean: numbers attached to the rounds of a protocol, and the sums in which bounds on proof
sizes are written.

  `OpenList s` (Iop/SerS.lean): one number for each round: how many positions are opened at most;
      also the depths of the Merkle trees
  `OpenList.zero`, `add`, `app`, `rep`, `pull`; lemmas for `OpenList.Bounds`: subsets, unions, sets
      that are in the first round or after it
  `entBits`, `entSum`: a bound on the bits of one opening; on the bits of all lists of openings,
      summed over the rounds (`gam n`, Iop/Ser.lean: the bits of a length prefix n)
  `BitsS.app`, `rep`, `pull`; `SerS.Within` for `app`, `rep`, `pull`; `InteractiveOracleProof.OpensLe.pull`
In Compile/ only Compile/Size.lean uses `entBits`, for one opened position; `entSum` is used in
files on sizes of Iop/ and Blocks/. Numbers for the protocols of Blocks/: Blocks/Sizes.lean,
Blocks/SizesFr.lean.

Notation: `BitsS s : Type` (Iop/SerS.lean): for each round two numbers: the bits of a pair
(position, symbol), and the bits of the plain part; `a : ℕ × ℕ`: the two numbers of one round;
`OpenList.Bounds s o A : Prop` (there): a set of positions has, in each round, at most the given
number of elements; `SerS.Within s S b : Prop` (there): the serializers of all rounds encode within
the given numbers of bits; `InteractiveOracleProof.OpensLe Q o : Prop` (there): the verifier reads at most o_r
positions of the oracle of round r, whatever the instance, its randomness and the plain parts;
`Samplers s : Type 1` (Iop/Pull.lean): one sampler for each round; `Shape.pull s σ : Shape`
(there): the rounds `r.pull σ`: the same round with an element of the sampler's source Src as
challenge; `OPos.pushEquiv σ : OPos (s.pull σ) ≃ OPos s` (there): positions do not change.

Limits: no theorem of this library says that an encoding is at most `entSum` bits long; for
`entBits`: Compile/Size.lean.
-/
import Iop.SerS

set_option autoImplicit false

namespace Iop
open Ser (gam)

/-! ## Lists of numbers -/

namespace OpenList

def zero : (s : Shape) → OpenList s
  | [] => ()
  | _ :: s => (0, zero s)

def add : {s : Shape} → OpenList s → OpenList s → OpenList s
  | [], _, _ => ()
  | _ :: _, (a, as), (b, bs) => (a + b, add as bs)

def app : {s t : Shape} → OpenList s → OpenList t → OpenList (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (a, as), b => (a, app as b)

def rep (r : Round) (a : ℕ) :
    (n : ℕ) → {t : Shape} → OpenList t → OpenList (List.replicate n r ++ t)
  | 0, _, b => b
  | n + 1, _, b => (a, rep r a n b)

def pull : (s : Shape) → (σ : Samplers s) → OpenList s → OpenList (Shape.pull s σ)
  | [], _, _ => ()
  | _ :: s, (_, σs), (a, as) => (a, pull s σs as)

theorem add_zero : ∀ {s : Shape} (o : OpenList s), add o (zero s) = o
  | [], _ => rfl
  | _ :: _, (a, as) => congrArg (Prod.mk a) (add_zero as)

theorem zero_add : ∀ {s : Shape} (o : OpenList s), add (zero s) o = o
  | [], _ => rfl
  | _ :: _, (a, as) => by
      show (0 + a, add (zero _) as) = (a, as)
      rw [Nat.zero_add, zero_add as]

theorem add_app :
    ∀ {s t : Shape} (a a' : OpenList s) (b b' : OpenList t),
      add (app a b) (app a' b') = app (add a a') (add b b')
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (x, a), (x', a'), b, b' => congrArg (Prod.mk (x + x')) (add_app a a' b b')

theorem zero_app : ∀ (s t : Shape), zero (s ++ t) = app (zero s) (zero t)
  | [], _ => rfl
  | _ :: s, t => congrArg (Prod.mk 0) (zero_app s t)

/-! ### Lemmas for `Bounds` -/

theorem Bounds.subset :
    ∀ {s : Shape} {o : OpenList s} {A B : Finset (OPos s)},
      (∀ p ∈ A, p ∈ B) → Bounds s o B → Bounds s o A
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, h, hB =>
      ⟨le_trans (Finset.card_le_card fun _ hp => Finset.mem_toLeft.2 (h _ (Finset.mem_toLeft.1 hp)))
          hB.1,
        Bounds.subset (fun _ hp => Finset.mem_toRight.2 (h _ (Finset.mem_toRight.1 hp))) hB.2⟩

theorem Bounds.of_empty :
    ∀ {s : Shape} (o : OpenList s) {A : Finset (OPos s)}, (∀ p, p ∉ A) → Bounds s o A
  | [], _, _, _ => trivial
  | r :: s, (n, o), A, h =>
      ⟨by
        have : Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from A) = ∅ :=
          Finset.eq_empty_of_forall_notMem fun p hp => h _ (Finset.mem_toLeft.1 hp)
        rw [this]; exact Nat.zero_le _,
        Bounds.of_empty o fun p hp => h _ (Finset.mem_toRight.1 hp)⟩

/-- If C is within A ∪ B, o bounds A and o' bounds B, then `add o o'` bounds C. -/
theorem Bounds.union :
    ∀ {s : Shape} {o o' : OpenList s} {A B C : Finset (OPos s)},
      (∀ p ∈ C, p ∈ A ∨ p ∈ B) → Bounds s o A → Bounds s o' B → Bounds s (add o o') C
  | [], _, _, _, _, _, _, _, _ => trivial
  | r :: s, (_, _), (_, _), A, B, C, h, hA, hB => by
      classical
      refine ⟨?_, Bounds.union (fun p hp => ?_) hA.2 hB.2⟩
      · refine le_trans
          (Finset.card_le_card
            (t := Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from A) ∪
                Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from B)) fun p hp => ?_)
          (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA.1 hB.1))
        rcases h _ (Finset.mem_toLeft.1 hp) with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_toLeft.2 h1)
        · exact Finset.mem_union_right _ (Finset.mem_toLeft.2 h1)
      · rcases h _ (Finset.mem_toRight.1 hp) with h1 | h1
        · exact Or.inl (Finset.mem_toRight.2 h1)
        · exact Or.inr (Finset.mem_toRight.2 h1)

/-- a set of positions of the first round -/
theorem Bounds.head {r : Round} {s : Shape} {n : ℕ} (o : OpenList s) {A : Finset (OPos (r :: s))}
    (h : ∀ p ∈ A, ∃ q : r.Pos, p = Sum.inl q) (hn : A.card ≤ n) : Bounds (r :: s) (n, o) A := by
  refine ⟨le_trans ?_ hn, Bounds.of_empty o fun p hp => ?_⟩
  · have := Finset.card_toLeft_add_card_toRight (u := (show Finset (r.Pos ⊕ OPos s) from A))
    exact le_trans (Nat.le_add_right _ _) (le_of_eq this)
  · obtain ⟨q, hq⟩ := h _ (Finset.mem_toRight.1 hp)
    cases hq

/-- a set of positions after the first round -/
theorem Bounds.tail {r : Round} {s : Shape} (n : ℕ) {o : OpenList s} {A : Finset (OPos (r :: s))}
    {B : Finset (OPos s)} (h : ∀ p ∈ A, ∃ q ∈ B, p = Sum.inr q) (hB : Bounds s o B) :
    Bounds (r :: s) (n, o) A := by
  refine ⟨?_, Bounds.subset (fun p hp => ?_) hB⟩
  · have : Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from A) = ∅ :=
      Finset.eq_empty_of_forall_notMem fun p hp => by
        obtain ⟨q, -, hq⟩ := h _ (Finset.mem_toLeft.1 hp)
        cases hq
    rw [this]; exact Nat.zero_le _
  · obtain ⟨q, hq, e⟩ := h _ (Finset.mem_toRight.1 hp)
    cases e
    exact hq

theorem Bounds.pull :
    ∀ (s : Shape) (σ : Samplers s) {o : OpenList s}
        {A : Finset (OPos s)} {B : Finset (OPos (Shape.pull s σ))},
      (∀ p ∈ B, OPos.pushEquiv σ p ∈ A) → Bounds s o A → Bounds (Shape.pull s σ) (pull s σ o) B
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, σs), (_, _), _, _, h, hA =>
      ⟨le_trans (Finset.card_le_card fun _ hp => Finset.mem_toLeft.2 (h _ (Finset.mem_toLeft.1 hp)))
          hA.1,
        Bounds.pull s σs (fun _ hp => Finset.mem_toRight.2 (h _ (Finset.mem_toRight.1 hp))) hA.2⟩

end OpenList

/-- Numbers that bound the opened positions of Q round by round (`h`) bound those of `Q.pull σ` too
(challenges computed by samplers, `InteractiveOracleProof.pull`). -/
theorem InteractiveOracleProof.OpensLe.pull {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {o : OpenList Q.shape}
    (h : Q.OpensLe o) (σ : Samplers Q.shape) :
    (Q.pull σ).OpensLe (OpenList.pull Q.shape σ o) := fun x ρ pl =>
  OpenList.Bounds.pull Q.shape σ (fun p hp => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hp
    simpa using hq) (h x (Rho.push σ ρ) (Plains.push σ pl))

/-! ## Widths -/

namespace BitsS

def app : {s t : Shape} → BitsS s → BitsS t → BitsS (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (a, as), b => (a, app as b)

def rep (r : Round) (a : ℕ × ℕ) : (n : ℕ) → {t : Shape} → BitsS t → BitsS (List.replicate n r ++ t)
  | 0, _, b => b
  | n + 1, _, b => (a, rep r a n b)

def pull : (s : Shape) → (σ : Samplers s) → BitsS s → BitsS (Shape.pull s σ)
  | [], _, _ => ()
  | _ :: s, (_, σs), (a, as) => (a, pull s σs as)

theorem plainBits_app :
    ∀ {s t : Shape} (a : BitsS s) (b : BitsS t),
      plainBits (s ++ t) (app a b) = plainBits s a + plainBits t b
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, ((_, y), a), b => by
      show y + plainBits _ (app a b) = y + plainBits _ a + plainBits _ b
      rw [plainBits_app a b, Nat.add_assoc]

theorem plainBits_rep (r : Round) (a : ℕ × ℕ) : ∀ (n : ℕ) {t : Shape} (b : BitsS t),
    plainBits (List.replicate n r ++ t) (rep r a n b) = n * a.2 + plainBits t b
  | 0, _, _ => by simp [rep]
  | n + 1, _, b => by
      show a.2 + plainBits _ (rep r a n b) = (n + 1) * a.2 + plainBits _ b
      rw [plainBits_rep r a n b, Nat.succ_mul]; omega

theorem plainBits_pull :
    ∀ (s : Shape) (σ : Samplers s) (b : BitsS s),
      plainBits (Shape.pull s σ) (pull s σ b) = plainBits s b
  | [], _, _ => rfl
  | _ :: s, (_, σs), ((_, y), b) => congrArg (y + ·) (plainBits_pull s σs b)

end BitsS

namespace SerS

theorem Within.pull : ∀ (s : Shape) (σ : Samplers s) {S : SerS s} {b : BitsS s}, Within s S b →
    Within (Shape.pull s σ) (SerS.pull s σ S) (BitsS.pull s σ b)
  | [], _, _, _, _ => trivial
  | _ :: s, (_, σs), ((_, _), _), ((_, _), _), h => ⟨h.1, h.2.1, Within.pull s σs h.2.2⟩

end SerS

/-! ## The sums over the rounds -/

/-- the bits of one opening: x bits for (position, symbol); a salt of at most sMT bits; a path of at
most d digests of lam bits; both with their length prefixes -/
def entBits (lam sMT d x : ℕ) : ℕ := x + ((gam sMT + sMT * 1) + (gam d + d * lam))

/-- the bits of the lists of opened positions: for each round with depth d_r, width x_r and at most
n_r openings, gam n_r + n_r · entBits d_r x_r -/
def entSum (lam sMT : ℕ) : (s : Shape) → (d : OpenList s) → BitsS s → (o : OpenList s) → ℕ
  | [], _, _, _ => 0
  | _ :: s, (d, ds), ((x, _), t), (n, o) =>
    (gam n + n * entBits lam sMT d x) + entSum lam sMT s ds t o

theorem entSum_app (lam sMT : ℕ) :
    ∀ {s t : Shape} (d : OpenList s) (d' : OpenList t) (b : BitsS s) (b' : BitsS t)
        (o : OpenList s) (o' : OpenList t),
      entSum lam sMT (s ++ t) (OpenList.app d d') (BitsS.app b b') (OpenList.app o o') =
        entSum lam sMT s d b o + entSum lam sMT t d' b' o'
  | [], _, _, _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (d, ds), d', ((x, _), b), b', (n, o), o' => by
      show (gam n + n * entBits lam sMT d x) +
          entSum lam sMT _ (OpenList.app ds d') (BitsS.app b b') (OpenList.app o o') = _
      rw [entSum_app lam sMT ds d' b b' o o', ← Nat.add_assoc]
      rfl

theorem entSum_rep (lam sMT : ℕ) (r : Round) (d : ℕ) (a : ℕ × ℕ) (n : ℕ) :
    ∀ (k : ℕ) {t : Shape} (d' : OpenList t) (b' : BitsS t) (o' : OpenList t),
      entSum lam sMT (List.replicate k r ++ t) (OpenList.rep r d k d')
          (BitsS.rep r a k b') (OpenList.rep r n k o') =
        k * (gam n + n * entBits lam sMT d a.1) + entSum lam sMT t d' b' o'
  | 0, _, _, _, _ => by simp [OpenList.rep, BitsS.rep]
  | k + 1, _, d', b', o' => by
      show (gam n + n * entBits lam sMT d a.1) +
          entSum lam sMT _ (OpenList.rep r d k d') (BitsS.rep r a k b') (OpenList.rep r n k o') = _
      rw [entSum_rep lam sMT r d a n k d' b' o', Nat.succ_mul]; omega

theorem entSum_pull (lam sMT : ℕ) :
    ∀ (s : Shape) (σ : Samplers s) (d : OpenList s) (b : BitsS s) (o : OpenList s),
      entSum lam sMT (Shape.pull s σ) (OpenList.pull s σ d)
          (BitsS.pull s σ b) (OpenList.pull s σ o) =
        entSum lam sMT s d b o
  | [], _, _, _, _ => rfl
  | _ :: s, (_, σs), (d, ds), ((x, _), b), (n, o) =>
    congrArg ((gam n + n * entBits lam sMT d x) + ·) (entSum_pull lam sMT s σs ds b o)

/-- `entBits` grows with the depth and with the width. -/
theorem entBits_mono {lam sMT d d' x x' : ℕ} (hd : d ≤ d') (hx : x ≤ x') :
    entBits lam sMT d x ≤ entBits lam sMT d' x' :=
  Nat.add_le_add hx
    (Nat.add_le_add_left (Nat.add_le_add (Ser.gam_mono hd) (Nat.mul_le_mul_right lam hd)) _)

end Iop
