-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/RowMeet.lean: from a law at each block of a typed list to one law for the whole
list: the written transcript has an image, and on it the list's verifier puts out the last
statement.

Each kind's files are to show of its block, at a written stretch τ of it: if τ passes its tests on
the written verifier's messages, and the rounds that a run has still to take begin with the rounds
of τ, then τ has an image under the block's map, the block's verifier puts out on it the statement
that the next block starts from, and the rounds still to be taken are the rest. Here these laws
are laid behind each other along a family of blocks (RowCarry.lean: famCar, hfamCar, chainCar,
lout).

Main names:
  PlaceAt V ok b F τ p a p' a': the law at one block and one written stretch τ. V reads a written
    stretch as a list of rounds of some type ρ; ok says that the stretch passes (a map has an
    image only where each written verifier's message passes its test of work, which V does not
    show); p, p' are the rounds still to be taken before and behind the block; a, a' the typed
    statements before and behind it. The statements may hang on τ: a reading V may forget what a
    typed statement keeps.
  PlaceLaw V ok b F p a p' a': the law at all stretches with the same statements; PlaceLaw.at.
  vAll, okAll, lawAll; vHead, okHead, lawHead: the reading of the stretches 0 to n of a transcript
    behind each other; that all of them pass; that each has its law (with a head's stretch in
    front).
  fam_meet, hfam_meet, chain_meet: the laws at all blocks give the law for the whole.

Limits. ρ, V, ok, the lists p i and the statements a i are letters. No law at any block is shown
here. That a file's written shape is the stretches behind each other, and that the reading of a
file's transcript is the stretches' readings behind each other, is the user's to show. One
direction, as in OnBytes/Flat/CarrySkip.lean. Nothing is said on an honest prover or on hiding.
-/
import Johnson.Top.H.RowCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.RowCar
open Iop Prob OnBytes.Flat

variable {ρ : Type}

/-- The law at one block and one written stretch: where the stretch passes and the rounds still to
be taken begin with the stretch's, the stretch has an image, the block's verifier puts out a' on
it, and the rest is still to be taken. -/
def PlaceAt {A B : JK} {s : Shape} (V : Tr s → List ρ) (ok : Tr s → Prop) (b : BK A B)
    (F : CarryS s b.R.shape) (τ : Tr s) (p : List ρ) (a : A.X × A.E.Str) (p' : List ρ)
    (a' : B.X × B.E.Str) : Prop :=
  ∀ rest : List ρ, ok τ → p = V τ ++ rest →
    ∃ τ', F.tr τ = some τ' ∧ b.R.red.out a τ' = some a' ∧ p' = rest

/-- The law at all written stretches, with the same statements. -/
def PlaceLaw {A B : JK} {s : Shape} (V : Tr s → List ρ) (ok : Tr s → Prop) (b : BK A B)
    (F : CarryS s b.R.shape) (p : List ρ) (a : A.X × A.E.Str) (p' : List ρ)
    (a' : B.X × B.E.Str) : Prop :=
  ∀ τ : Tr s, PlaceAt V ok b F τ p a p' a'

theorem PlaceLaw.at {A B : JK} {s : Shape} {V : Tr s → List ρ} {ok : Tr s → Prop} {b : BK A B}
    {F : CarryS s b.R.shape} {p : List ρ} {a : A.X × A.E.Str} {p' : List ρ} {a' : B.X × B.E.Str}
    (h : PlaceLaw V ok b F p a p' a') (τ : Tr s) : PlaceAt V ok b F τ p a p' a' := h τ

/-- The reading of the stretches 0 to n behind each other. -/
def vAll (ws : ℕ → Shape) (V : ∀ i, Tr (ws i) → List ρ) : ∀ n, Tr (wsAll ws n) → List ρ
  | 0, τ => V 0 τ
  | n + 1, τ => vAll ws V n (Tr.fst τ) ++ V (n + 1) (Tr.snd (s := wsAll ws n) τ)

/-- The stretches 0 to n all pass. -/
def okAll (ws : ℕ → Shape) (ok : ∀ i, Tr (ws i) → Prop) : ∀ n, Tr (wsAll ws n) → Prop
  | 0, τ => ok 0 τ
  | n + 1, τ => okAll ws ok n (Tr.fst τ) ∧ ok (n + 1) (Tr.snd (s := wsAll ws n) τ)

/-- Each of the stretches 0 to n has its law. -/
def lawAll (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ws : ℕ → Shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (V : ∀ i, Tr (ws i) → List ρ)
    (ok : ∀ i, Tr (ws i) → Prop) (p : ℕ → List ρ) (a : ∀ i, (J i).X × (J i).E.Str) :
    ∀ n, Tr (wsAll ws n) → Prop
  | 0, τ => PlaceAt (V 0) (ok 0) (b 0) (F 0) τ (p 0) (a 0) (p 1) (a 1)
  | n + 1, τ => lawAll J b ws F V ok p a n (Tr.fst τ) ∧
      PlaceAt (V (n + 1)) (ok (n + 1)) (b (n + 1)) (F (n + 1)) (Tr.snd (s := wsAll ws n) τ)
        (p (n + 1)) (a (n + 1)) (p (n + 1 + 1)) (a (n + 1 + 1))

/-- **The laws at the blocks 0 to n give the law for the family.** -/
theorem fam_meet (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ws : ℕ → Shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (V : ∀ i, Tr (ws i) → List ρ)
    (ok : ∀ i, Tr (ws i) → Prop) (p : ℕ → List ρ) (a : ∀ i, (J i).X × (J i).E.Str) :
    ∀ (n : ℕ) (τ : Tr (wsAll ws n)) (rest : List ρ), lawAll J b ws F V ok p a n τ →
      okAll ws ok n τ → p 0 = vAll ws V n τ ++ rest →
        ∃ τ', (famCar J b ws F n).car.tr τ = some τ' ∧
          lout (LK.fam J b n) (a 0) τ' = some (a (n + 1)) ∧ p (n + 1) = rest
  | 0, _, rest, h, ho, hp => h rest ho hp
  | n + 1, τ, rest, h, ho, hp => by
    have hp' : p 0 = vAll ws V n (Tr.fst τ) ++
        (V (n + 1) (Tr.snd (s := wsAll ws n) τ) ++ rest) := by
      rw [hp]
      exact List.append_assoc _ _ _
    obtain ⟨τ₁, h1, h2, h3⟩ := fam_meet J b ws F V ok p a n (Tr.fst τ) _ h.1 ho.1 hp'
    obtain ⟨τ₂, g1, g2, g3⟩ := h.2 rest ho.2 h3
    refine ⟨Tr.app τ₁ τ₂, ?_, ?_, g3⟩
    · have e := LCar.tr_snoc (b (n + 1)) (famCar J b ws F n) (fun _ => F (n + 1)) (Tr.fst τ)
        (Tr.snd (s := wsAll ws n) τ)
      rw [Tr.app_fst_snd, h1, g1] at e
      exact e
    · have e := lout_app (LK.fam J b n) (b (n + 1)) (a 0) τ₁ τ₂
      rw [h2] at e
      exact e.trans g2

/-- The reading of the head's stretch and the stretches 0 to n behind each other. -/
def vHead (wh : Shape) (ws : ℕ → Shape) (Vh : Tr wh → List ρ) (V : ∀ i, Tr (ws i) → List ρ) :
    ∀ n, Tr (wsHead wh ws n) → List ρ
  | 0, τ => Vh (Tr.fst τ) ++ V 0 (Tr.snd (s := wh) τ)
  | n + 1, τ => vHead wh ws Vh V n (Tr.fst τ) ++ V (n + 1) (Tr.snd (s := wsHead wh ws n) τ)

/-- The head's stretch and the stretches 0 to n all pass. -/
def okHead (wh : Shape) (ws : ℕ → Shape) (okh : Tr wh → Prop) (ok : ∀ i, Tr (ws i) → Prop) :
    ∀ n, Tr (wsHead wh ws n) → Prop
  | 0, τ => okh (Tr.fst τ) ∧ ok 0 (Tr.snd (s := wh) τ)
  | n + 1, τ => okHead wh ws okh ok n (Tr.fst τ) ∧ ok (n + 1) (Tr.snd (s := wsHead wh ws n) τ)

/-- The head's stretch and each of the stretches 0 to n has its law. -/
def lawHead {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (wh : Shape)
    (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape) (F : ∀ i, CarryS (ws i) (b i).R.shape)
    (Vh : Tr wh → List ρ) (V : ∀ i, Tr (ws i) → List ρ) (okh : Tr wh → Prop)
    (ok : ∀ i, Tr (ws i) → Prop) (ph : List ρ) (p : ℕ → List ρ) (ah : A.X × A.E.Str)
    (a : ∀ i, (J i).X × (J i).E.Str) : ∀ n, Tr (wsHead wh ws n) → Prop
  | 0, τ => PlaceAt Vh okh h Fh (Tr.fst τ) ph ah (p 0) (a 0) ∧
      PlaceAt (V 0) (ok 0) (b 0) (F 0) (Tr.snd (s := wh) τ) (p 0) (a 0) (p 1) (a 1)
  | n + 1, τ => lawHead J h b wh ws Fh F Vh V okh ok ph p ah a n (Tr.fst τ) ∧
      PlaceAt (V (n + 1)) (ok (n + 1)) (b (n + 1)) (F (n + 1)) (Tr.snd (s := wsHead wh ws n) τ)
        (p (n + 1)) (a (n + 1)) (p (n + 1 + 1)) (a (n + 1 + 1))

/-- The same with a head block in front. -/
theorem hfam_meet {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1)))
    (wh : Shape) (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (Vh : Tr wh → List ρ) (V : ∀ i, Tr (ws i) → List ρ)
    (okh : Tr wh → Prop) (ok : ∀ i, Tr (ws i) → Prop) (ph : List ρ) (p : ℕ → List ρ)
    (ah : A.X × A.E.Str) (a : ∀ i, (J i).X × (J i).E.Str) :
    ∀ (n : ℕ) (τ : Tr (wsHead wh ws n)) (rest : List ρ),
      lawHead J h b wh ws Fh F Vh V okh ok ph p ah a n τ → okHead wh ws okh ok n τ →
        ph = vHead wh ws Vh V n τ ++ rest →
        ∃ τ', (hfamCar J h b wh ws Fh F n).car.tr τ = some τ' ∧
          lout (hfam J h b n) ah τ' = some (a (n + 1)) ∧ p (n + 1) = rest
  | 0, τ, rest, hl, ho, hp => by
    have hp' : ph = Vh (Tr.fst τ) ++ (V 0 (Tr.snd (s := wh) τ) ++ rest) := by
      rw [hp]
      exact List.append_assoc _ _ _
    obtain ⟨τ₁, h1, h2, h3⟩ := hl.1 _ ho.1 hp'
    obtain ⟨τ₂, g1, g2, g3⟩ := hl.2 rest ho.2 h3
    refine ⟨Tr.app τ₁ τ₂, ?_, ?_, g3⟩
    · have e := LCar.tr_snoc (b 0) (LCar.one h Fh) (fun _ => F 0) (Tr.fst τ)
        (Tr.snd (s := wh) τ)
      rw [Tr.app_fst_snd, LCar.tr_one, h1, g1] at e
      exact e
    · have e := lout_app (LK.one h) (b 0) ah τ₁ τ₂
      exact e.trans (by
        show (h.R.red.out ah τ₁).bind _ = _
        rw [h2]
        exact g2)
  | n + 1, τ, rest, hl, ho, hp => by
    have hp' : ph = vHead wh ws Vh V n (Tr.fst τ) ++
        (V (n + 1) (Tr.snd (s := wsHead wh ws n) τ) ++ rest) := by
      rw [hp]
      exact List.append_assoc _ _ _
    obtain ⟨τ₁, h1, h2, h3⟩ :=
      hfam_meet J h b wh ws Fh F Vh V okh ok ph p ah a n (Tr.fst τ) _ hl.1 ho.1 hp'
    obtain ⟨τ₂, g1, g2, g3⟩ := hl.2 rest ho.2 h3
    refine ⟨Tr.app τ₁ τ₂, ?_, ?_, g3⟩
    · have e := LCar.tr_snoc (b (n + 1)) (hfamCar J h b wh ws Fh F n) (fun _ => F (n + 1))
        (Tr.fst τ) (Tr.snd (s := wsHead wh ws n) τ)
      rw [Tr.app_fst_snd, h1, g1] at e
      exact e
    · have e := lout_app (hfam J h b n) (b (n + 1)) ah τ₁ τ₂
      rw [h2] at e
      exact e.trans g2

/-- **A whole chain: a head block, the blocks 0 to n, a last block: the laws at all blocks give:
the written transcript has an image under the chain's one map, at the shape of the chain's one
block, and on it that block's verifier puts out the last statement.** -/
theorem chain_meet {A Z : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (n : ℕ)
    (t : BK (J (n + 1)) Z) (wh wt : Shape) (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (Ft : CarryS wt t.R.shape) (Vh : Tr wh → List ρ)
    (V : ∀ i, Tr (ws i) → List ρ) (Vt : Tr wt → List ρ) (okh : Tr wh → Prop)
    (ok : ∀ i, Tr (ws i) → Prop) (okt : Tr wt → Prop) (ph : List ρ) (p : ℕ → List ρ)
    (pz : List ρ) (ah : A.X × A.E.Str) (a : ∀ i, (J i).X × (J i).E.Str) (az : Z.X × Z.E.Str)
    (d : A.W) (τ : Tr (wsHead wh ws n ++ wt)) (rest : List ρ)
    (hl : lawHead J h b wh ws Fh F Vh V okh ok ph p ah a n (Tr.fst τ))
    (ht : PlaceAt Vt okt t Ft (Tr.snd (s := wsHead wh ws n) τ) (p (n + 1)) (a (n + 1)) pz az)
    (ho : okHead wh ws okh ok n (Tr.fst τ) ∧ okt (Tr.snd (s := wsHead wh ws n) τ))
    (hp : ph = (vHead wh ws Vh V n (Tr.fst τ) ++ Vt (Tr.snd (s := wsHead wh ws n) τ)) ++ rest) :
    ∃ τ'', ((chainCar J h b n t wh wt ws Fh F Ft).carAt d).tr τ = some τ'' ∧
      ((chainL J h b n t).blk d).R.red.out ah τ'' = some az ∧ pz = rest := by
  have hp' : ph = vHead wh ws Vh V n (Tr.fst τ) ++
      (Vt (Tr.snd (s := wsHead wh ws n) τ) ++ rest) := by
    rw [hp]
    exact List.append_assoc _ _ _
  obtain ⟨τ₁, h1, h2, h3⟩ :=
    hfam_meet J h b wh ws Fh F Vh V okh ok ph p ah a n (Tr.fst τ) _ hl ho.1 hp'
  obtain ⟨τ₂, g1, g2, g3⟩ := ht rest ho.2 h3
  have e : (chainCar J h b n t wh wt ws Fh F Ft).car.tr τ = some (Tr.app τ₁ τ₂) := by
    have e := LCar.tr_snoc t (hfamCar J h b wh ws Fh F n) (fun _ => Ft) (Tr.fst τ)
      (Tr.snd (s := wsHead wh ws n) τ)
    rw [Tr.app_fst_snd, h1, g1] at e
    exact e
  obtain ⟨τ'', k1, k2⟩ := LCar.out_at _ d τ _ e
  refine ⟨τ'', k1, ?_, g3⟩
  rw [k2 ah]
  have e2 := lout_app (hfam J h b n) t ah τ₁ τ₂
  rw [h2] at e2
  exact e2.trans g2

end KObj.RowCar

#print axioms KObj.RowCar.fam_meet
#print axioms KObj.RowCar.hfam_meet
#print axioms KObj.RowCar.chain_meet
