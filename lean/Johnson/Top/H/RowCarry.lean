-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/RowCarry.lean: the maps from a file's written rounds to the rounds of a typed list
of blocks, put together from the maps of the single blocks.

A typed list of blocks (KObj.LK, Johnson/E/KObj/Blocks.lean) is one reduction: its blocks in a
row. The maps from written rounds to typed rounds (OnBytes.Flat.CarryS,
OnBytes/Flat/CarrySkip.lean) are made block by block by whoever owns a block. Here they are laid
behind each other, by CarryS.app (OnBytes/Flat/CarrySApp.lean), so that the rules that carry
soundness along such maps can be applied once to the whole list.

Main names:
  LCar l s: for a typed list l and a written shape s: a map for each block of l; the map of a
    later block may read the written transcript of all blocks before it; s is the written
    stretches behind each other.
  lsh l, lerr l: the list's rounds and error counts, written by recursion; shape_blk, err_blk:
    they are those of the list's one block (LK.blk).
  LCar.car c: the one map from s to lsh l. LCar.tr_one, LCar.tr_snoc: the image of a written
    transcript is the blocks' images behind each other. LCar.fits_one, LCar.fits_snoc: the written
    rounds' error counts bear the list's, if each stretch's bear its block's.
  LCar.carAt c d: the same map at the shape of the list's one block; LCar.fitsAt, LCar.trAt.
  wsAll ws n, errAll, famCar: the same for a family of blocks numbered from 0 to n, each with a
    map that reads nothing before its stretch. fits_fam, fits_famAt.
  hfam, hfam_eq, wsHead, errHead, hfamCar, fits_hfam: the same with a head block in front.
  lout l: the list's verifier on lsh l, by recursion; lout_app; out_blk: it is the verifier of the
    list's one block. LCar.out_at: where car has an image, carAt has one, and on it the one block's
    verifier puts out what lout puts out.
  chainL, chain_eq, chainCar, chain_car: a whole chain in the form ((one head).app (fam …)).snoc
    last: one map from the written stretches behind each other to the rounds of the chain's one
    block; the written counts bear the block's; where the stretches' maps have an image, this map
    has one, and on it the block's verifier puts out what lout puts out.

Limits. No map of any block is made here, and nothing says that a written round is a round of a
file. One direction, as in CarrySkip.lean. Nothing is said on an honest prover or on hiding.
-/
import Johnson.E.KObj.Arrows
import OnBytes.Flat.CarrySApp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.RowCar
open Iop Prob OnBytes.Flat

/-- The rounds of a typed list: its blocks' rounds behind each other. -/
def lsh {A : JK} : {B : JK} → LK A B → Shape
  | _, .one b => b.R.shape
  | _, .snoc l b => lsh l ++ b.R.shape

/-- The error counts of a typed list: its blocks' behind each other. -/
def lerr {A : JK} : {B : JK} → (l : LK A B) → Err (lsh l)
  | _, .one b => b.err
  | _, .snoc l b => Err.app (lerr l) b.err

/-- The list's one block has these rounds. -/
theorem shape_blk {A : JK} (d : A.W) : ∀ {B : JK} (l : LK A B), (l.blk d).R.shape = lsh l
  | _, .one b => by rw [LK.blk_one]; rfl
  | _, .snoc l b => by
    rw [LK.blk_snoc]
    show (l.blk d).R.shape ++ b.R.shape = lsh l ++ b.R.shape
    rw [shape_blk d l]

/-- The list's one block has these error counts. -/
theorem err_blk {A : JK} (d : A.W) : ∀ {B : JK} (l : LK A B), HEq (l.blk d).err (lerr l)
  | _, .one b => by rw [LK.blk_one]; rfl
  | _, .snoc l b => by
    rw [LK.blk_snoc]
    show HEq (Err.app (l.blk d).err b.err) (Err.app (lerr l) b.err)
    have h1 := shape_blk d l
    have h2 := err_blk d l
    revert h2
    generalize (l.blk d).err = e
    revert e
    rw [h1]
    intro e h2
    rw [eq_of_heq h2]

/-- The list's verifier on the list's rounds, written by recursion: each block's verifier on its own
rounds, from what the block before has put out. -/
def lout {A : JK} : {B : JK} → (l : LK A B) → A.X × A.E.Str → Tr (lsh l) → Option (B.X × B.E.Str)
  | _, .one b, a, τ => b.R.red.out a τ
  | _, .snoc l b, a, τ =>
    (lout l a (Tr.fst τ)).bind fun x => b.R.red.out x (Tr.snd (s := lsh l) τ)

theorem lout_app {A B C : JK} (l : LK A B) (b : BK B C) (a : A.X × A.E.Str) (τ : Tr (lsh l))
    (σ : Tr b.R.shape) :
    lout (l.snoc b) a (Tr.app τ σ) = (lout l a τ).bind fun x => b.R.red.out x σ := by
  show (lout l a (Tr.fst (Tr.app τ σ))).bind
    (fun x => b.R.red.out x (Tr.snd (s := lsh l) (Tr.app τ σ))) = _
  rw [Tr.fst_app, Tr.snd_app]

/-- Two reductions in a row, the first one's rounds given by an equation. -/
theorem seq_out_cast {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂)
    (R₂ : IOR X₂ E₂ X₃ E₃) {s : Shape} (h : R₁.shape = s)
    (hs : R₁.shape ++ R₂.shape = s ++ R₂.shape) (a : X₁ × E₁.Str) (τ : Tr (s ++ R₂.shape)) :
    (R₁.seq R₂).red.out a (hs.symm ▸ τ : Tr (R₁.shape ++ R₂.shape)) =
      (R₁.red.out a (h.symm ▸ Tr.fst τ : Tr R₁.shape)).bind fun x =>
        R₂.red.out x (Tr.snd (s := s) τ) := by
  subst h
  exact IOR.red_seq_out R₁ R₂ a τ

/-- A block given by an equation. -/
theorem out_of_eq {A B : JK} {β β' : BK A B} (h : β = β') {s : Shape} (hs : β.R.shape = s)
    (hs' : β'.R.shape = s) (a : A.X × A.E.Str) (τ : Tr s) :
    β.R.red.out a (hs.symm ▸ τ : Tr β.R.shape) = β'.R.red.out a (hs'.symm ▸ τ : Tr β'.R.shape) := by
  subst h
  rfl

/-- The verifier of the list's one block is the list's verifier. -/
theorem out_blk {A : JK} (d : A.W) : ∀ {B : JK} (l : LK A B) (a : A.X × A.E.Str) (τ : Tr (lsh l)),
    (l.blk d).R.red.out a ((shape_blk d l).symm ▸ τ : Tr (l.blk d).R.shape) = lout l a τ
  | _, .one b, a, τ =>
    out_of_eq (LK.blk_one b d) (shape_blk d (.one b)) rfl a τ
  | _, .snoc l b, a, τ => by
    have hs : ((l.blk d).seq b d).R.shape = lsh (l.snoc b) := by
      show (l.blk d).R.shape ++ b.R.shape = lsh l ++ b.R.shape
      rw [shape_blk d l]
    rw [out_of_eq (LK.blk_snoc l b d) (shape_blk d (l.snoc b)) hs a τ]
    refine (seq_out_cast (l.blk d).R b.R (shape_blk d l) hs a τ).trans ?_
    rw [out_blk d l a (Tr.fst τ)]
    rfl

/-- A map for each block of a typed list; s: the written stretches behind each other. -/
inductive LCar {A : JK} : {B : JK} → LK A B → Shape → Type 1
  | one {B : JK} (b : BK A B) {s : Shape} (F : CarryS s b.R.shape) : LCar (.one b) s
  | snoc {B C : JK} {l : LK A B} (b : BK B C) {s t : Shape} (c : LCar l s)
      (G : Tr s → CarryS t b.R.shape) : LCar (.snoc l b) (s ++ t)

namespace LCar

/-- The one map from the written rounds to the list's rounds. -/
def car {A : JK} : {B : JK} → {l : LK A B} → {s : Shape} → LCar l s → CarryS s (lsh l)
  | _, _, _, .one _ F => F
  | _, _, _, .snoc _ c G => c.car.app G

theorem tr_one {A B : JK} (b : BK A B) {s : Shape} (F : CarryS s b.R.shape) (τ : Tr s) :
    (LCar.one b F).car.tr τ = F.tr τ := rfl

/-- The image of a written transcript: the images behind each other. -/
theorem tr_snoc {A B C : JK} {l : LK A B} (b : BK B C) {s t : Shape} (c : LCar l s)
    (G : Tr s → CarryS t b.R.shape) (τ : Tr s) (σ : Tr t) :
    (LCar.snoc b c G).car.tr (Tr.app τ σ) =
      (c.car.tr τ).bind fun τ' => ((G τ).tr σ).map fun σ' => Tr.app τ' σ' :=
  CarryS.tr_app c.car G τ σ

theorem fits_one {A B : JK} (b : BK A B) {s : Shape} (F : CarryS s b.R.shape) (ε' : Err s)
    (h : F.Fits b.err ε') : (LCar.one b F).car.Fits (lerr (.one b)) ε' := h

/-- The counts of the written rounds bear the list's. -/
theorem fits_snoc {A B C : JK} {l : LK A B} (b : BK B C) {s t : Shape} (c : LCar l s)
    (G : Tr s → CarryS t b.R.shape) (ε' : Err s) (δ' : Err t) (h : c.car.Fits (lerr l) ε')
    (hG : ∀ τ, (G τ).Fits b.err δ') :
    (LCar.snoc b c G).car.Fits (lerr (l.snoc b)) (Err.app ε' δ') :=
  CarryS.Fits.app h hG

/-- The same map, at the shape of the list's one block. -/
def carAt {A B : JK} {l : LK A B} {s : Shape} (c : LCar l s) (d : A.W) :
    CarryS s (l.blk d).R.shape :=
  (shape_blk d l).symm ▸ c.car

end LCar

/-- A map along an equation of typed shapes keeps what its counts bear. -/
theorem fits_cast {s s' s'' : Shape} (h : s'' = s') (F : CarryS s s') (e : Err s') (e'' : Err s'')
    (he : HEq e'' e) (ε' : Err s) (hF : F.Fits e ε') : (h.symm ▸ F : CarryS s s'').Fits e'' ε' := by
  subst h
  rw [eq_of_heq he]
  exact hF

/-- A map along an equation of typed shapes has an image just where it had one. -/
theorem tr_cast {s s' s'' : Shape} (h : s'' = s') (F : CarryS s s') (τ : Tr s) :
    (h.symm ▸ F : CarryS s s'').tr τ = (h.symm ▸ F.tr τ : Option (Tr s'')) := by
  subst h
  rfl

/-- The counts of the written rounds bear those of the list's one block. -/
theorem LCar.fitsAt {A B : JK} {l : LK A B} {s : Shape} (c : LCar l s) (d : A.W) (ε' : Err s)
    (h : c.car.Fits (lerr l) ε') : (c.carAt d).Fits (l.blk d).err ε' :=
  fits_cast (shape_blk d l) c.car (lerr l) (l.blk d).err (err_blk d l) ε' h

theorem LCar.trAt {A B : JK} {l : LK A B} {s : Shape} (c : LCar l s) (d : A.W) (τ : Tr s) :
    (c.carAt d).tr τ = ((shape_blk d l).symm ▸ c.car.tr τ : Option (Tr (l.blk d).R.shape)) :=
  tr_cast (shape_blk d l) c.car τ

/-- **Where the map has an image, the same map at the one block's shape has one, and the one block's
verifier puts out on it what the list's verifier puts out.** -/
theorem LCar.out_at {A B : JK} {l : LK A B} {s : Shape} (c : LCar l s) (d : A.W) (τ : Tr s)
    (τ' : Tr (lsh l)) (h : c.car.tr τ = some τ') :
    ∃ τ'' : Tr (l.blk d).R.shape, (c.carAt d).tr τ = some τ'' ∧
      ∀ a, (l.blk d).R.red.out a τ'' = lout l a τ' := by
  refine ⟨((shape_blk d l).symm ▸ τ' : Tr (l.blk d).R.shape), ?_, fun a => out_blk d l a τ'⟩
  rw [LCar.trAt, h]
  have key : ∀ {s' s'' : Shape} (hs : s'' = s') (x : Tr s'),
      (hs.symm ▸ (some x : Option (Tr s')) : Option (Tr s'')) = some (hs.symm ▸ x : Tr s'') := by
    intro s' s'' hs x
    subst hs
    rfl
  exact key (shape_blk d l) τ'

/-- The written stretches 0 to n behind each other. -/
def wsAll (ws : ℕ → Shape) : ℕ → Shape
  | 0 => ws 0
  | n + 1 => wsAll ws n ++ ws (n + 1)

/-- The written rounds' counts, stretch by stretch, behind each other. -/
def errAll (ws : ℕ → Shape) (e : ∀ i, Err (ws i)) : ∀ n, Err (wsAll ws n)
  | 0 => e 0
  | n + 1 => Err.app (errAll ws e n) (e (n + 1))

/-- A family of blocks, each with a map of its own stretch. -/
def famCar (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ws : ℕ → Shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) : ∀ n, LCar (LK.fam J b n) (wsAll ws n)
  | 0 => .one (b 0) (F 0)
  | n + 1 => .snoc (b (n + 1)) (famCar J b ws F n) fun _ => F (n + 1)

theorem fits_fam (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ws : ℕ → Shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (e : ∀ i, Err (ws i)) :
    ∀ n, (∀ i ≤ n, (F i).Fits (b i).err (e i)) →
      (famCar J b ws F n).car.Fits (lerr (LK.fam J b n)) (errAll ws e n)
  | 0, h => h 0 le_rfl
  | n + 1, h =>
    LCar.fits_snoc (b (n + 1)) (famCar J b ws F n) _ _ _
      (fits_fam J b ws F e n fun i hi => h i (Nat.le_succ_of_le hi)) fun _ => h (n + 1) le_rfl

/-- The family's one block: the written rounds' counts bear its own. -/
theorem fits_famAt (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) (ws : ℕ → Shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (e : ∀ i, Err (ws i)) (d : (J 0).W) (n : ℕ)
    (h : ∀ i ≤ n, (F i).Fits (b i).err (e i)) :
    ((famCar J b ws F n).carAt d).Fits ((LK.fam J b n).blk d).err (errAll ws e n) :=
  (famCar J b ws F n).fitsAt d _ (fits_fam J b ws F e n h)

/-! ### a head block in front and a last block behind -/

/-- A head block, then the family's blocks 0 to n. -/
def hfam {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) :
    ∀ n, LK A (J (n + 1))
  | 0 => (LK.one h).snoc (b 0)
  | n + 1 => (hfam J h b n).snoc (b (n + 1))

/-- It is the head's list with the family's list behind it. -/
theorem hfam_eq {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) :
    ∀ n, (LK.one h).app (LK.fam J b n) = hfam J h b n
  | 0 => by
    show (LK.one h).app (LK.one (b 0)) = _
    rw [LK.app_one]
    rfl
  | n + 1 => by
    show (LK.one h).app ((LK.fam J b n).snoc (b (n + 1))) = _
    rw [LK.app_snoc, hfam_eq J h b n]
    rfl

/-- The written stretches: the head's, then 0 to n. -/
def wsHead (wh : Shape) (ws : ℕ → Shape) : ℕ → Shape
  | 0 => wh ++ ws 0
  | n + 1 => wsHead wh ws n ++ ws (n + 1)

/-- The written rounds' counts: the head's stretch, then 0 to n. -/
def errHead (wh : Shape) (ws : ℕ → Shape) (eh : Err wh) (e : ∀ i, Err (ws i)) :
    ∀ n, Err (wsHead wh ws n)
  | 0 => Err.app eh (e 0)
  | n + 1 => Err.app (errHead wh ws eh e n) (e (n + 1))

/-- A head block and a family of blocks, each with a map of its own stretch. -/
def hfamCar {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (wh : Shape)
    (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape) (F : ∀ i, CarryS (ws i) (b i).R.shape) :
    ∀ n, LCar (hfam J h b n) (wsHead wh ws n)
  | 0 => .snoc (b 0) (.one h Fh) fun _ => F 0
  | n + 1 => .snoc (b (n + 1)) (hfamCar J h b wh ws Fh F n) fun _ => F (n + 1)

theorem fits_hfam {A : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1)))
    (wh : Shape) (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (eh : Err wh) (e : ∀ i, Err (ws i))
    (hh : Fh.Fits h.err eh) :
    ∀ n, (∀ i ≤ n, (F i).Fits (b i).err (e i)) →
      (hfamCar J h b wh ws Fh F n).car.Fits (lerr (hfam J h b n)) (errHead wh ws eh e n)
  | 0, hF => LCar.fits_snoc (b 0) (.one h Fh) _ _ _ hh fun _ => hF 0 le_rfl
  | n + 1, hF =>
    LCar.fits_snoc (b (n + 1)) (hfamCar J h b wh ws Fh F n) _ _ _
      (fits_hfam J h b wh ws Fh F eh e hh n fun i hi => hF i (Nat.le_succ_of_le hi))
      fun _ => hF (n + 1) le_rfl

/-- A whole chain: a head block, the blocks 0 to n, a last block. -/
def chainL {A Z : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (n : ℕ)
    (t : BK (J (n + 1)) Z) : LK A Z :=
  (hfam J h b n).snoc t

theorem chain_eq {A Z : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (n : ℕ)
    (t : BK (J (n + 1)) Z) : ((LK.one h).app (LK.fam J b n)).snoc t = chainL J h b n t := by
  rw [hfam_eq J h b n]
  rfl

/-- The chain's maps: the head's, the blocks', the last block's. -/
def chainCar {A Z : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (n : ℕ)
    (t : BK (J (n + 1)) Z) (wh wt : Shape) (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (Ft : CarryS wt t.R.shape) :
    LCar (chainL J h b n t) (wsHead wh ws n ++ wt) :=
  .snoc t (hfamCar J h b wh ws Fh F n) fun _ => Ft

/-- **A whole chain: one map from the written stretches behind each other to the rounds of the
chain's one block. The written rounds' counts bear the block's. Where the stretches' maps have an
image, this map has one, and on it the one block's verifier puts out what the blocks' verifiers put
out one behind the other.** -/
theorem chain_car {A Z : JK} (J : ℕ → JK) (h : BK A (J 0)) (b : ∀ i, BK (J i) (J (i + 1))) (n : ℕ)
    (t : BK (J (n + 1)) Z) (wh wt : Shape) (ws : ℕ → Shape) (Fh : CarryS wh h.R.shape)
    (F : ∀ i, CarryS (ws i) (b i).R.shape) (Ft : CarryS wt t.R.shape) (eh : Err wh)
    (e : ∀ i, Err (ws i)) (et : Err wt) (hh : Fh.Fits h.err eh)
    (hF : ∀ i ≤ n, (F i).Fits (b i).err (e i)) (ht : Ft.Fits t.err et) (d : A.W) :
    ∃ G : CarryS (wsHead wh ws n ++ wt) ((((LK.one h).app (LK.fam J b n)).snoc t).blk d).R.shape,
      G.Fits ((((LK.one h).app (LK.fam J b n)).snoc t).blk d).err
        (Err.app (errHead wh ws eh e n) et) ∧
      ∀ (τ : Tr (wsHead wh ws n ++ wt)) (τ' : Tr (lsh (chainL J h b n t))),
        (chainCar J h b n t wh wt ws Fh F Ft).car.tr τ = some τ' →
        ∃ τ'', G.tr τ = some τ'' ∧ ∀ a,
          ((((LK.one h).app (LK.fam J b n)).snoc t).blk d).R.red.out a τ'' =
            lout (chainL J h b n t) a τ' := by
  rw [chain_eq J h b n t]
  exact ⟨(chainCar J h b n t wh wt ws Fh F Ft).carAt d,
    LCar.fitsAt _ d _ (LCar.fits_snoc t _ _ _ _ (fits_hfam J h b wh ws Fh F eh e hh n hF)
      fun _ => ht), fun τ τ' hτ => LCar.out_at _ d τ τ' hτ⟩

end KObj.RowCar

#print axioms KObj.RowCar.shape_blk
#print axioms KObj.RowCar.err_blk
#print axioms KObj.RowCar.LCar.tr_snoc
#print axioms KObj.RowCar.LCar.fitsAt
#print axioms KObj.RowCar.LCar.trAt
#print axioms KObj.RowCar.fits_famAt
#print axioms KObj.RowCar.out_blk
#print axioms KObj.RowCar.LCar.out_at
#print axioms KObj.RowCar.hfam_eq
#print axioms KObj.RowCar.chain_car
