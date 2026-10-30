-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Sizes.lean: helper definitions and lemmas for the numbers from which the sizes of compiled
proofs are made, for the protocols of Blocks/: the width of a round's serialisers
(Blocks/SerS.lean), the depth of its Merkle tree, and how many positions of its oracle the verifier
opens at most.
  `wordsBits`, `plainBits2`: the widths for a round `wordsRound` and for a message without oracles;
  `wordsSer_within`: the serialisers of a round `wordsRound` stay within these widths (for a
  nonempty type of challenges).
  `depthList`: the depths, as the compiler's generic wire record makes them (Blocks/Leaves.lean:
  `depthR`).
  `bounds_posR`, `bounds_cons`: a bound on a set of opened positions, part by part.
  `B2 α b`: `Nat.card α ≤ 2 ^ b`: a finite type α has at most 2^b elements.
  `entSum_zero`, `entSum_head_le`, `entSum_cons_le` and the like: the sums over the rounds,
  evaluated or bounded.
Limits: this file does not give the widths or the opened positions of a given protocol (exactly: no
list of widths, `BitsS`, and no list of numbers of opened positions, `OpenList`). Of the levels (the
recursive column test of Blocks/LevelDef.lean, `LevSpec`) it has only one definition (`arrEntB`) and
lemmas on single rounds and on where the positions read lie.
-/
import Blocks.SerS
import Blocks.Opens
import Blocks.Leaves
import Iop.Sizes

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-! ## Lemmas: positions of the two parts of a list -/

theorem bounds_posR :
    ∀ (s : Shape) {t : Shape} {o : OpenList t} {A : Finset (OPos t)} {C : Finset (OPos (s ++ t))},
      (∀ p ∈ C, ∃ q ∈ A, p = posR (s := s) q) → OpenList.Bounds t o A →
      OpenList.Bounds (s ++ t) (OpenList.app (OpenList.zero s) o) C
  | [], _, _, _, _, h, hA =>
    OpenList.Bounds.subset (fun p hp => by obtain ⟨q, hq, rfl⟩ := h p hp; exact hq) hA
  | r :: s, t, _, A, C, h, hA => by
      refine OpenList.Bounds.tail 0
        (B := Finset.toRight (show Finset (r.Pos ⊕ OPos (s ++ t)) from C))
        (fun p hp => ?_) (bounds_posR s (fun y hy => ?_) hA)
      · obtain ⟨q, -, rfl⟩ := h p hp
        exact ⟨posR (s := s) q, Finset.mem_toRight.2 hp, rfl⟩
      · obtain ⟨q, hq, e⟩ := h _ (Finset.mem_toRight.1 hy)
        exact ⟨q, hq, Sum.inr.inj e⟩

/-! ## Depths -/

/-- the depths of the trees over the prover messages -/
def depthList : (s : Shape) → s.IsPoint → OpenList s
  | [], _ => ()
  | _ :: s, (pt, pts) => (depthR pt, depthList s pts)

theorem depthList_app : ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
    depthList (s ++ t) (pointApp a b) = OpenList.app (depthList s a) (depthList t b)
  | [], _, _, _ => rfl
  | _ :: _, _, (pt, a), b => congrArg (Prod.mk (depthR pt)) (depthList_app a b)

theorem depthList_rep (r : Round) (h : r.IsPoint) :
    ∀ (n : ℕ) {t : Shape} (b : t.IsPoint), depthList (List.replicate n r ++ t) (pointRep r h n b) =
      OpenList.rep r (depthR h) n (depthList t b)
  | 0, _, _ => rfl
  | n + 1, _, b => congrArg (Prod.mk (depthR h)) (depthList_rep r h n b)

/-! ## Widths of rounds -/

/-- a round `wordsRound`: the bits of (position, symbol), and of the plain part -/
def wordsBits (A : Type) [FinEnum A] (n : A → ℕ) (Sy : A → Type) [∀ a, FinEnum (Sy a)]
    (Plain : Type) [FinEnum Plain] : ℕ × ℕ :=
  (Nat.clog 2 (FinEnum.card (Σ p : (Σ a, Fin (n a)), Sy p.1)), Nat.clog 2 (FinEnum.card Plain))

/-- a message without oracles -/
def plainBits2 (Plain : Type) [FinEnum Plain] : ℕ × ℕ :=
  (Nat.clog 2 (FinEnum.card (Σ _ : Empty, Empty)), Nat.clog 2 (FinEnum.card Plain))

theorem wordsSer_within (A : Type) [FinEnum A] (n : A → ℕ) (Sy : A → Type)
    [∀ a, FinEnum (Sy a)] (Plain Chal : Type) [FinEnum Plain] [Fintype Chal] [Nonempty Chal]
    (dSy : ∀ a, Sy a) (dPlain : Plain) :
    (∀ z, ((wordsSer A n Sy Plain Chal dSy dPlain).1.put z).length ≤ (wordsBits A n Sy Plain).1) ∧
    ∀ z, ((wordsSer A n Sy Plain Chal dSy dPlain).2.put z).length ≤ (wordsBits A n Sy Plain).2 :=
  ⟨fun z => le_of_eq (Ser.length_put_ofFinEnum _ z),
    fun z => le_of_eq (Ser.length_put_ofFinEnum _ z)⟩

theorem within_cons {r : Round} {s : Shape} {A : SerR r} {S : SerS s} {a : ℕ × ℕ} {b : BitsS s}
    (h : (∀ z, (A.1.put z).length ≤ a.1) ∧ ∀ z, (A.2.put z).length ≤ a.2) (hS : SerS.Within s S b) :
    SerS.Within (r :: s) (A, S) (a, b) := ⟨h.1, h.2, hS⟩

/-! ## Lemmas: a set of positions, part by part -/

theorem posCase_posR :
    ∀ (s : Shape) {t : Shape} (p : OPos t), posCase (s := s) (t := t) (posR (s := s) p) = .inr p
  | [], _, _ => rfl
  | _ :: s, t, p => by
      show (posCase (s := s) (t := t) (posR (s := s) p)).map Sum.inr id = _
      rw [posCase_posR s p]; rfl

theorem posR_inj {s t : Shape} {p q : OPos t} (h : posR (s := s) p = posR (s := s) q) : p = q :=
  Sum.inr.inj ((posCase_posR s p).symm.trans ((congrArg posCase h).trans (posCase_posR s q)))

/-- a set all of whose elements are values of f on J has at most as many elements as J -/
theorem card_le_of_cover {α β : Type} (T : Finset α) (J : Finset β)
    (f : β → α) (h : ∀ x ∈ T, ∃ j ∈ J, f j = x) : T.card ≤ J.card := by
  classical
  refine le_trans (Finset.card_le_card (t := J.image f) fun x hx => ?_) Finset.card_image_le
  obtain ⟨j, hj, rfl⟩ := h x hx
  exact Finset.mem_image_of_mem f hj

/-- the first round, and those after it -/
theorem bounds_cons {r : Round} {s : Shape} {n : ℕ} {o : OpenList s}
    {C : Finset (OPos (r :: s))} (A : Finset r.Pos) (B : Finset (OPos s))
    (hA : ∀ q : r.Pos, (Sum.inl q : OPos (r :: s)) ∈ C → q ∈ A)
    (hB : ∀ q : OPos s, (Sum.inr q : OPos (r :: s)) ∈ C → q ∈ B)
    (hn : A.card ≤ n) (ho : OpenList.Bounds s o B) :
    OpenList.Bounds (r :: s) (n, o) C :=
  ⟨le_trans (Finset.card_le_card fun q hq => hA q (Finset.mem_toLeft.1 hq)) hn,
    OpenList.Bounds.subset (fun q hq => hB q (Finset.mem_toRight.1 hq)) ho⟩

/-! ## The levels: the positions read -/

section Levels
variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

variable {E}

theorem mem_levelsReadsOwn_cons {a b : LevSpec F} {rest : List (LevSpec F)}
    {ρ : Rho (levelsShape E a (b :: rest))} {p : OPos (levelsShape E a (b :: rest))}
    (hp : p ∈ levelsReadsOwn a (b :: rest) ρ) :
    (∃ i, p = posR (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest)
        (.inr (.inl ⟨(),
              levelsPos b rest
                (Rho.snd (s := List.replicate a.mu (LinSh.rSC E))
                  (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) ρ).2.2 i⟩))) ∨
    ∃ q ∈ levelsReadsOwn b rest
        (Rho.snd (s := List.replicate a.mu (LinSh.rSC E))
          (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) ρ).2.2,
      p = posR (s := List.replicate a.mu (LinSh.rSC E))
          (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) (.inr (.inr q)) := by
  classical
  unfold levelsReadsOwn at hp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨i, rfl⟩ | ⟨q, hq, rfl⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨q, hq, rfl⟩

end Levels

/-! ## Numbers of elements, up to powers of two -/

/-- `Nat.card α ≤ 2 ^ b`: a finite type has at most 2^b elements -/
def B2 (α : Type) (b : ℕ) : Prop := Nat.card α ≤ 2 ^ b

theorem finEnum_card_eq (α : Type) [FinEnum α] : FinEnum.card α = Nat.card α :=
  (Nat.card_eq_of_equiv_fin FinEnum.equiv).symm

theorem clog_le_of_B2 {α : Type} [FinEnum α] {b : ℕ} (h : B2 α b) :
    Nat.clog 2 (FinEnum.card α) ≤ b := by
  rw [finEnum_card_eq]
  exact (Nat.clog_le_iff_le_pow (by decide)).2 h

theorem B2.unit : B2 Unit 0 := by simp [B2]

theorem B2.prod {α β : Type} {a b : ℕ} (ha : B2 α a) (hb : B2 β b) : B2 (α × β) (a + b) := by
  unfold B2 at *
  rw [Nat.card_prod, pow_add]
  exact Nat.mul_le_mul ha hb

theorem B2.pi {ι : Type} [Fintype ι] {β : ι → Type} {b : ι → ℕ} (h : ∀ i, B2 (β i) (b i)) :
    B2 (∀ i, β i) (∑ i, b i) := by
  unfold B2 at *
  rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' fun i _ => h i

theorem B2.vec {α : Type} {a : ℕ} (ha : B2 α a) (k : ℕ) : B2 (Fin k → α) (k * a) := by
  have := B2.pi (ι := Fin k) (β := fun _ => α) (b := fun _ => a) fun _ => ha
  simpa using this

/-- pairs (position, symbol) of a round `wordsRound` all of whose symbols are of the type T -/
theorem B2.words {A : Type} [Fintype A] (n : A → ℕ) {T : Type} {d t : ℕ}
    (hn : ∑ a, n a ≤ 2 ^ d) (hT : B2 T t) :
    B2 (Σ _ : (Σ a, Fin (n a)), T) (d + t) := by
  unfold B2 at *
  rw [Nat.card_congr (Equiv.sigmaEquivProd _ _), Nat.card_prod, Nat.card_sigma, pow_add]
  refine Nat.mul_le_mul ?_ hT
  simpa using hn

theorem wordsBits_fst_le (A : Type) [FinEnum A] [Fintype A] (n : A → ℕ) (T : Type) [FinEnum T]
    (Plain : Type) [FinEnum Plain] {d t : ℕ} (hn : ∑ a, n a ≤ 2 ^ d) (hT : B2 T t) :
    (wordsBits A n (fun _ => T) Plain).1 ≤ d + t :=
  clog_le_of_B2 (B2.words n hn hT)

theorem wordsBits_snd_le (A : Type) [FinEnum A] (n : A → ℕ) (Sy : A → Type) [∀ a, FinEnum (Sy a)]
    (Plain : Type) [FinEnum Plain] {b : ℕ} (h : B2 Plain b) :
    (wordsBits A n Sy Plain).2 ≤ b := clog_le_of_B2 h

theorem plainBits2_snd_le (Plain : Type) [FinEnum Plain] {b : ℕ} (h : B2 Plain b) :
    (plainBits2 Plain).2 ≤ b := clog_le_of_B2 h

-- From here on in this file the widths are used through the lemmas above only; unfolding them would
-- make Lean compute with numbers of elements.
attribute [irreducible] wordsBits plainBits2

/-! ## The sums over the rounds -/

open Ser (gam)

theorem zero_rep (r : Round) :
    ∀ (n : ℕ) (t : Shape),
      OpenList.zero (List.replicate n r ++ t) = OpenList.rep r 0 n (OpenList.zero t)
  | 0, _ => rfl
  | n + 1, t => congrArg (Prod.mk 0) (zero_rep r n t)

theorem gam_zero : gam 0 = 1 := by simp [gam]

/-- a round in which nothing is opened costs one bit: the length 0 of its list -/
theorem ent_zero (lam sMT d x : ℕ) : gam 0 + 0 * entBits lam sMT d x = 1 := by
  rw [gam_zero, Nat.zero_mul]

/-- rounds in which nothing is opened cost one bit each -/
theorem entSum_zero (lam sMT : ℕ) :
    ∀ (s : Shape) (d : OpenList s) (b : BitsS s), entSum lam sMT s d b (OpenList.zero s) = s.length
  | [], _, _ => rfl
  | _ :: s, (d, ds), ((x, _), b) => by
      show (gam 0 + 0 * entBits lam sMT d x) + entSum lam sMT s ds b (OpenList.zero s) =
        s.length + 1
      rw [ent_zero, entSum_zero lam sMT s ds b, Nat.add_comm]

/-- one round, with bounds on its depth and its width -/
theorem ent_le {lam sMT n d d' x x' : ℕ} (hd : d ≤ d') (hx : x ≤ x') :
    gam n + n * entBits lam sMT d x ≤ gam n + n * entBits lam sMT d' x' :=
  Nat.add_le_add_left (Nat.mul_le_mul_left n (entBits_mono hd hx)) _

/-- rounds of which only the first is opened -/
theorem entSum_head_le (lam sMT : ℕ) {r : Round} {s : Shape} (d : OpenList (r :: s))
    (b : BitsS (r :: s)) (n : ℕ) {d' x' : ℕ} (hd : d.1 ≤ d') (hx : b.1.1 ≤ x') :
    entSum lam sMT (r :: s) d b (n, OpenList.zero s) ≤
      (gam n + n * entBits lam sMT d' x') + s.length := by
  obtain ⟨d0, ds⟩ := d
  obtain ⟨⟨x, y⟩, t⟩ := b
  show (gam n + n * entBits lam sMT d0 x) + entSum lam sMT s ds t (OpenList.zero s) ≤ _
  rw [entSum_zero]
  exact Nat.add_le_add_right (ent_le hd hx) _

theorem app_zero_replicate (r : Round) : ∀ (n : ℕ) {t : Shape} (o : OpenList t),
    OpenList.app (OpenList.zero (List.replicate n r)) o = OpenList.rep r 0 n o
  | 0, _, _ => rfl
  | n + 1, _, o => congrArg (Prod.mk 0) (app_zero_replicate r n o)

/-- k copies of a round r, in which nothing is opened, cost one bit each -/
theorem entSum_rep_zero (lam sMT : ℕ) (r : Round) (d : ℕ) (a : ℕ × ℕ) (k : ℕ) {t : Shape}
    (d' : OpenList t) (b' : BitsS t) (o' : OpenList t) :
    entSum lam sMT (List.replicate k r ++ t) (OpenList.rep r d k d') (BitsS.rep r a k b')
        (OpenList.app (OpenList.zero (List.replicate k r)) o') =
      k + entSum lam sMT t d' b' o' := by
  rw [app_zero_replicate, entSum_rep, ent_zero, Nat.mul_one]

/-- the first round, with bounds on its depth and its width, and the rest -/
theorem entSum_cons_le (lam sMT : ℕ) {r : Round} {s : Shape} (d : OpenList (r :: s))
    (b : BitsS (r :: s)) (o : OpenList (r :: s)) {d' x' N : ℕ} (hd : d.1 ≤ d') (hx : b.1.1 ≤ x')
    (hN : entSum lam sMT s d.2 b.2 o.2 ≤ N) :
    entSum lam sMT (r :: s) d b o ≤ (gam o.1 + o.1 * entBits lam sMT d' x') + N := by
  obtain ⟨d0, ds⟩ := d
  obtain ⟨⟨x, y⟩, t⟩ := b
  obtain ⟨n, o⟩ := o
  exact Nat.add_le_add (ent_le hd hx) hN

/-- a first round in which nothing is opened -/
theorem entSum_cons_zero_le (lam sMT : ℕ) {r : Round} {s : Shape} (d : OpenList (r :: s))
    (b : BitsS (r :: s)) (o : OpenList s) {N : ℕ} (hN : entSum lam sMT s d.2 b.2 o ≤ N) :
    entSum lam sMT (r :: s) d b (0, o) ≤ 1 + N := by
  obtain ⟨d0, ds⟩ := d
  obtain ⟨⟨x, y⟩, t⟩ := b
  show (gam 0 + 0 * entBits lam sMT d0 x) + entSum lam sMT s ds t o ≤ _
  rw [ent_zero]
  exact Nat.add_le_add_left hN _

theorem plainBits_cons_le {r : Round} {s : Shape} (b : BitsS (r :: s)) {y' N : ℕ}
    (hy : b.1.2 ≤ y') (hN : BitsS.plainBits s b.2 ≤ N) :
    BitsS.plainBits (r :: s) b ≤ y' + N := by
  obtain ⟨⟨x, y⟩, t⟩ := b
  exact Nat.add_le_add hy hN

/-! ### The levels -/

section Levels
variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] [FinEnum E]

/-- one array of the format b as a prover message: the bound for its q opened columns, in a tree of
depth ⌈log₂ n⌉ -/
def arrEntB (lam sMT e : ℕ) (b : LevSpec F) : ℕ :=
  gam b.q + b.q * entBits lam sMT (Nat.clog 2 b.code.n) (Nat.clog 2 b.code.n + b.rows * e)

theorem depth_arr_le (b : LevSpec F) (Chal : Type) [Fintype Chal] [Nonempty Chal] :
    depthR (wordsPoint Unit (fun _ => b.code.n) (fun _ => Fin b.rows → E)
          Unit Chal (fun _ _ => 0) ()) ≤
      Nat.clog 2 b.code.n := by
  rw [depth_words]
  simp

theorem arrBits_fst_le (b : LevSpec F) {e : ℕ} (hE : B2 E e) :
    (wordsBits Unit (fun _ => b.code.n) (fun _ => Fin b.rows → E) Unit).1 ≤
      Nat.clog 2 b.code.n + b.rows * e :=
  wordsBits_fst_le Unit (fun _ => b.code.n) (Fin b.rows → E) Unit
    (by simpa using Nat.le_pow_clog (by norm_num) b.code.n) (hE.vec _)

end Levels

end Blocks
