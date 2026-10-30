-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfPlace.lean: lemmas which say, each under the hypotheses of its statement, that the
names that the builder of Cb/Ld/LdBldWf.lean gives to digits and masks are different coordinates of
the oracle messages.

Theorems on Cb/Ld/LdBldWf.lean's definitions, under `X.Room p` (Cb/Ld/LdBldWfSpec.lean) or less:
they are put together with Cb/Ld/LdBldWfDef.lean's in Cb/Ld/LdBldWfProofs.lean. Generic; nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Why: every place that a lookup plays is `X.mkN f a` for a name a (`plN_eq`): for f ≤ `X.n`
(`mkN_pos`) a constructor of the sum type of named entries, with the forest in it. So "different
places" are different constructors, different forests, different names, under injective placings.
For l ≤ `X.n` the lookup's own table of places (`K.pl`) has exactly these places, each once
(Cb/Ld/LdLkpMaskPutLkp2.lean: `ldLkpPl2_asm`; `ldLkpPlaces2_sw`: stated in
Cb/Ld/LdLkpMaskPlaces2.lean, proved in Cb/Ld/LdLkpMaskPlaces2Proofs.lean): `bldWfP_pl`,
`bldWfP_plName`.

Main names:
  `bldWfP_ent`: the named entries in the messages. `bldWfP_apartL`: between the blocks.
    `bldWfP_supR`, under `X.Room p` and f ≤ `X.n`: the public support of each row. `bldWfP_hpl`,
    under `hM`: the masks of all blocks stand at different free entries. These are the main lemmas:
    see their doc comments.
  `bldWfP_atEq`, `bldWfP_ownL`: the lookups' places are named entries, read by their own lookup.
  `bldWfP_noPad`: no named entry is a pad.
  `bldWfP_supC`: the public support `gC f` holds the two inner masks of the last level of the keys'
    tree.
  `bldWfP_wfAtL`: the named entry `X.atL l i` stands at the free entry `X.plV (some l) i`.
    `bldWf_where` proves `Spec.bldWf_where` (Cb/Ld/LdBldWfSpec.lean): for f ≤ `X.n`, where the
    places stand.

Limits: what the head of Cb/Ld/LdBldWfSpec.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldWfSpec
import Cb.Ld.LdLkpMaskPutLkp2

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

/-- a data entry, as an entry of the family: different data entries are different entries -/
theorem stdL_entD_inj {Fp E : Type} [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E]
    {N : Sig E} (Y : N.StdL Fp) :
    Function.Injective fun x : Σ a, Y.Dt a => (⟨x.1, Y.atD x.1 x.2⟩ : N.Ent) := by
  rintro ⟨a, u⟩ ⟨b, v⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (show (⟨a, Y.atD a u⟩ : N.Ent) = ⟨b, Y.atD b v⟩ from h)
  exact congrArg (Sigma.mk a) (Sum.inl.inj (Sum.inl.inj ((Y.ν a).symm.injective (eq_of_heq h2))))

/-- a data entry is no free entry -/
theorem stdL_entD_ne {Fp E : Type} [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E]
    {N : Sig E} (Y : N.StdL Fp) (x : Σ a, Y.Dt a) (y : Σ a, Y.Fr a) :
    (⟨x.1, Y.atD x.1 x.2⟩ : N.Ent) ≠ Y.entF y := by
  obtain ⟨a, u⟩ := x
  obtain ⟨b, v⟩ := y
  intro h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (show (⟨a, Y.atD a u⟩ : N.Ent) = ⟨b, Y.atF b v⟩ from h)
  have h3 := Sum.inl.inj ((Y.ν a).symm.injective (eq_of_heq h2))
  cases h3

namespace BldWf
variable {F E Fp : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp)

/-! ### The dictionary -/

/-- a name of an own mask of the lookup, as the builder's name -/
def toB (f : ℕ) : (X.K.asm f).Nm → X.num.LkM E f
  | .s i => .s i
  | .t l h i => .t l h i
  | .k l h i => .k l h i
  | .f l h i => .f l h i
  | .e i => .e i
  | .b i => .b i

def ofB (f : ℕ) : X.num.LkM E f → (X.K.asm f).Nm
  | .s i => .s i
  | .t l h i => .t l h i
  | .k l h i => .k l h i
  | .f l h i => .f l h i
  | .e i => .e i
  | .b i => .b i

theorem ofB_toB (f : ℕ) (a : (X.K.asm f).Nm) : X.ofB f (X.toB f a) = a := by cases a <;> rfl

theorem toB_inj (f : ℕ) : Function.Injective (X.toB f) :=
  Function.LeftInverse.injective (X.ofB_toB f)

theorem mkN_pos (f : ℕ) (h : f ≤ X.n) (a : X.num.LkM E f) :
    X.mkN f a = Sum.inr (Sum.inl ⟨⟨f, h⟩, a⟩) := dif_pos h

theorem mkN_inj (f : ℕ) (h : f ≤ X.n) : Function.Injective (X.mkN f) := by
  intro a b e
  rw [X.mkN_pos f h, X.mkN_pos f h] at e
  exact eq_of_heq (Sigma.mk.inj_iff.1 (Sum.inl.inj (Sum.inr.inj e))).2

/-- For f, g ≤ `X.n`: masks of different forests have different names. -/
theorem mkN_forest (f g : ℕ) (hf : f ≤ X.n) (hg : g ≤ X.n) (a : X.num.LkM E f)
    (b : X.num.LkM E g) (e : X.mkN f a = X.mkN g b) : f = g := by
  rw [X.mkN_pos f hf, X.mkN_pos g hg] at e
  exact congrArg (fun s : Σ f : X.num.Fo, X.num.LkM E f.1 => s.1.1) (Sum.inl.inj (Sum.inr.inj e))

/-- The place of each own mask that the lookup plays is the builder's name of that mask:
`X.mkN f (X.toB f a)`. -/
theorem plN_eq (f : ℕ) (a : (X.K.asm f).Nm) :
    (X.K.asm f).plN a = Sum.inr (X.mkN f (X.toB f a)) := by
  cases a with
  | s i => cases i <;> rfl
  | t l h i =>
      cases i with
      | inl i => exact congrArg Sum.inr (dif_pos (show l < X.nd f from h))
      | inr b => exact congrArg Sum.inr (dif_pos (show l < X.nd f from h))
  | k l h i =>
      cases i with
      | inl i => exact congrArg Sum.inr (dif_pos (show l ≤ X.num.v' f from h))
      | inr b => exact congrArg Sum.inr (dif_pos (show l ≤ X.num.v' f from h))
  | f l h i =>
      cases i with
      | inl i => exact congrArg Sum.inr (dif_pos (show l < X.d f from h))
      | inr b => exact congrArg Sum.inr (dif_pos (show l < X.d f from h))
  | e i => rfl
  | b i => cases i <;> rfl

end BldWf

section
variable {F E Fp : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp)

/-- Inside each lookup (f ≤ `X.n`): the four plain conditions (`PlacesOK`,
Cb/Ld/LdLkpMaskPlaces2.lean). -/
theorem bldWfP_lkPl (f : ℕ) (hf : f ≤ X.n) : (X.K.asm f).PlacesOK (X.K.Dt f) where
  inj := fun a b e =>
    X.toB_inj f (X.mkN_inj f hf (Sum.inr.inj ((X.plN_eq f a).symm.trans (e.trans (X.plN_eq f b)))))
  out := fun a hD => by
    rw [X.plN_eq f a, X.mkN_pos f hf] at hD
    rcases hD with ⟨rc, e⟩ | ⟨u, i, e⟩
    · cases e
    · have e' : (Sum.inr (Sum.inl ⟨⟨f, hf⟩, X.toB f a⟩) : X.num.N E) = Sum.inl (X.bitB f u i) :=
        Sum.inr.inj e
      cases e'
  bits := fun u j => Or.inr ⟨u, j, rfl⟩
  keys := fun _ m m' hm => by
    show X.P.keyE f (fun rc => m (Sum.inl rc)) = X.P.keyE f (fun rc => m' (Sum.inl rc))
    exact congrArg (X.P.keyE f) (funext fun rc => hm _ (Or.inl ⟨rc, rfl⟩))

/-- For l ≤ `X.n`: the lookup's own table of places meets `MJ.Pl.OK` (Cb/Ld/LdLkpMaskPut.lean); its
places are the own masks'. -/
theorem bldWfP_pl (l : ℕ) (hl : l ≤ X.n) :
    (X.K.pl X.Rl l).OK ∧ ∀ j, (X.K.pl X.Rl l).At j ↔ (X.K.asm l).swAll j :=
  (ldLkpPl2_asm E (X.K.asm l) X.Cf.conf.E0 (X.Cf.conf.Msg × X.P.S.Msg) Unit Unit X.P.msg (X.Rl l)
    (X.K.Dt l) (ldLkpPlaces2_ok E _ _ (bldWfP_lkPl X l hl))).1

theorem bldWfP_plName (l : ℕ) (hl : l ≤ X.n) (i : (X.K.pl X.Rl l).I) :
    ∃ a : X.num.LkM E l, (X.K.pl X.Rl l).pl i = Sum.inr (X.mkN l a) := by
  obtain ⟨a, ha⟩ := (ldLkpPlaces2_sw E (X.K.asm l) _).1 (((bldWfP_pl X l hl).2 _).1 ⟨i, rfl⟩)
  exact ⟨X.toB l a, ha.trans (X.plN_eq l a)⟩

theorem bldWfP_atLName (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) :
    ∃ a : X.num.LkM E l, (X.K.pl X.Rl l).pl i = Sum.inr (X.mkN l a) ∧ X.atL l i = X.mkN l a := by
  obtain ⟨a, ha⟩ := bldWfP_plName X l (Nat.lt_succ_iff.1 l.2) i
  refine ⟨a, ha, ?_⟩
  unfold BldWf.atL
  rw [ha]
  rfl

theorem bldWfP_atEq (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) :
    (X.K.pl X.Rl l).pl i = (Sum.inr (X.atL l i) : X.P.bt.J) := by
  obtain ⟨a, h1, h2⟩ := bldWfP_atLName X l i
  rw [h1, h2]

theorem bldWfP_ownL (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) :
    X.Rl l (Sum.inr (X.atL l i)) := by
  rw [← bldWfP_atEq X l i]
  exact Or.inr (((bldWfP_pl X l (Nat.lt_succ_iff.1 l.2)).2 _).1 ⟨i, rfl⟩)

/-- no named entry is a pad -/
theorem bldWfP_noPad (n : X.num.N E) : X.Y.NoPad (X.nAt n) := by
  cases n with
  | inl b => exact ⟨Sum.inl (X.pB b).2, rfl⟩
  | inr m => exact ⟨Sum.inr (X.pM m).2, rfl⟩

/-- Under `hB`, `hM` (both placings are injective): the named entries are different entries of the
messages (`LdWfP.EntAt`, Cb/Ld/LdWfMasksBatt.lean). -/
theorem bldWfP_ent (hB : Function.Injective X.pB) (hM : Function.Injective X.pM) :
    X.P.EntAt X.nAt where
  ent := fun _ _ => rfl
  inj := by
    intro a b e
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hB (stdL_entD_inj X.Y e))
      | inr b => exact absurd e (stdL_entD_ne X.Y _ _)
    | inr a =>
      cases b with
      | inl b => exact absurd e.symm (stdL_entD_ne X.Y _ _)
      | inr b => exact congrArg Sum.inr (hM (X.Y.entF_injective e))

/-- a place of the keys' tree's inner masks is no hiding coefficient of the batching -/
theorem bldWfP_cK_ne (f l : ℕ) (b : Bool) (i : PIdx (List.replicate X.num.k (pfCube E 2))) :
    X.wBt i ≠ X.cKn f l b := by
  unfold BldWf.cKn BldWf.mkN BldWf.wBt BldWf.dN
  intro e
  split_ifs at e
  cases e

/-- The batching's own places (`LdWfP.OwnPlaces`, Cb/Ld/LdWfOwn.lean, at "the batching reads
everything"). -/
theorem bldWfP_own : X.P.OwnPlaces fun _ => True where
  inj := fun _ _ e => Sum.inr.inj (Sum.inr.inj e)
  own := fun _ => trivial
  mat := fun _ => trivial
  rdC := fun _ _ _ => trivial
  off := fun q i ⟨b, e⟩ => bldWfP_cK_ne X q _ b i e

/-- Between the blocks: a named entry that the messages of lookup j read is no mask place of a later
lookup, nor (`bldWfP_apartB`, for j ≤ `X.n`) of the batching. -/
theorem bldWfP_apartL (j : ℕ) (l : Fin (X.P.n + 1)) (hj : j < l) (n : X.num.N E)
    (hS : (X.K.asm j).srAll (X.K.Dt j) (Sum.inr n)) (i : (X.K.pl X.Rl l).I) : n ≠ X.atL l i := by
  have hl : (l : ℕ) ≤ X.n := Nat.lt_succ_iff.1 l.2
  have hjn : j ≤ X.n := le_trans (le_of_lt hj) hl
  obtain ⟨a, -, h2⟩ := bldWfP_atLName X l i
  rw [h2]
  rcases hS with (⟨rc, e⟩ | ⟨u, i', e⟩) | hw
  · cases e
  · have e' : n = Sum.inl (X.bitB j u i') := Sum.inr.inj e
    rw [e', X.mkN_pos l hl]
    intro e''
    cases e''
  · obtain ⟨a', ha'⟩ := (ldLkpPlaces2_sw E (X.K.asm j) _).1 hw
    have e' : n = X.mkN j (X.toB j a') := Sum.inr.inj (ha'.trans (X.plN_eq j a'))
    rw [e']
    exact fun e'' => absurd (X.mkN_forest j l hjn hl _ _ e'') (ne_of_lt hj)

theorem bldWfP_apartB (j : ℕ) (hj : j ≤ X.n) (n : X.num.N E)
    (hS : (X.K.asm j).srAll (X.K.Dt j) (Sum.inr n))
    (i : PIdx (List.replicate X.num.k (pfCube E 2))) : n ≠ X.wBt i := by
  rcases hS with (⟨rc, e⟩ | ⟨u, i', e⟩) | hw
  · cases e
  · have e' : n = Sum.inl (X.bitB j u i') := Sum.inr.inj e
    rw [e']
    intro e''
    cases e''
  · obtain ⟨a', ha'⟩ := (ldLkpPlaces2_sw E (X.K.asm j) _).1 hw
    have e' : n = X.mkN j (X.toB j a') := Sum.inr.inj (ha'.trans (X.plN_eq j a'))
    rw [e', X.mkN_pos j hj]
    intro e''
    cases e''

/-! ### The public supports -/

theorem bldWfP_supC (f : ℕ) (b : Bool) : X.P.gC f (X.K.cK f (X.K.v' f) b) := ⟨b, rfl⟩

/-- Under `h`, `hf`: the public support of each row holds all places of its lookup but the two inner
masks of the last level of the keys' tree, in this sense: `LkAsm2.PlacesInR`
(Cb/Ld/LdBldWfSupp.lean: `cK l b` for l < `v'`). -/
theorem bldWfP_supR (p : ℕ) (h : X.Room p) (f : ℕ) (hf : f ≤ X.n) (b : Fin (X.P.nR f)) :
    (X.K.asm f).PlacesInR fun j => ∃ n', j = Sum.inr n' ∧ X.P.gR f b n' := by
  obtain ⟨g0, gb, gm⟩ := h.supR f hf b
  have d0 : ∃ n', (Sum.inr X.dN : X.P.bt.J) = Sum.inr n' ∧ X.P.gR f b n' := ⟨_, rfl, g0⟩
  have mk : ∀ a : X.num.LkM E f, (∀ h c, a ≠ .k (X.num.v' f) h (Sum.inr c)) →
      ∃ n', (Sum.inr (X.mkN f a) : X.P.bt.J) = Sum.inr n' ∧ X.P.gR f b n' :=
    fun a ha => ⟨_, rfl, gm a ha⟩
  refine ⟨fun u j => ⟨_, rfl, gb u j⟩, fun i => mk _ (fun _ _ e => by cases e),
    fun c => mk _ (fun _ _ e => by cases e), fun l i => ?_, fun l c => ?_, fun l i => ?_,
    fun l hl c => ?_, fun l i => ?_, fun l c => ?_, fun i => mk _ (fun _ _ e => by cases e),
    fun i => mk _ (fun _ _ e => by cases e), mk _ (fun _ _ e => by cases e)⟩
  · show ∃ n', (Sum.inr (X.wAtn f l i) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.wAtn
    split_ifs
    · exact mk _ fun _ _ e => by cases e
    · exact d0
  · show ∃ n', (Sum.inr (X.cAtn f l c) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.cAtn
    split_ifs
    · exact mk _ fun _ _ e => by cases e
    · exact d0
  · show ∃ n', (Sum.inr (X.wKn f l i) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.wKn
    split_ifs
    · refine mk _ fun _ c e => ?_
      obtain ⟨e1, e2⟩ := LkAsm2.Nm.k.inj e
      subst e1
      cases eq_of_heq e2
    · exact d0
  · show ∃ n', (Sum.inr (X.cKn f l c) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.cKn
    rw [dif_pos (le_of_lt (show l < X.num.v' f from hl))]
    exact mk _ fun _ _ e => absurd (LkAsm2.Nm.k.inj e).1 (ne_of_lt (show l < X.num.v' f from hl))
  · show ∃ n', (Sum.inr (X.wTn f l i) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.wTn
    split_ifs
    · exact mk _ fun _ _ e => by cases e
    · exact d0
  · show ∃ n', (Sum.inr (X.cTn f l c) : X.P.bt.J) = Sum.inr n' ∧ _
    unfold BldWf.cTn
    split_ifs
    · exact mk _ fun _ _ e => by cases e
    · exact d0

/-! ### The masks of all blocks at free entries -/

theorem bldWfP_plVL (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) :
    ∃ a : X.num.LkM E l,
      (X.K.pl X.Rl l).pl i = Sum.inr (X.mkN l a) ∧
      X.atL l i = X.mkN l a ∧
      X.plV (some l) i = X.pM (Sum.inl ⟨⟨l, Nat.lt_succ_iff.1 l.2⟩, a⟩) := by
  obtain ⟨a, h1, h2⟩ := bldWfP_atLName X l i
  refine ⟨a, h1, h2, ?_⟩
  show X.frOf (X.atL l i) = _
  rw [h2, X.mkN_pos l (Nat.lt_succ_iff.1 l.2)]
  rfl

/-- Under `hM`: the masks of all blocks stand at different free entries. -/
theorem bldWfP_hpl (hM : Function.Injective X.pM) : X.Hpl := by
  rintro ⟨b, i⟩ ⟨b', i'⟩ h
  cases b with
  | some l =>
    obtain ⟨a, h1, -, h3⟩ := bldWfP_plVL X l i
    cases b' with
    | some l' =>
      obtain ⟨a', h1', -, h3'⟩ := bldWfP_plVL X l' i'
      have e : X.pM (Sum.inl ⟨⟨l, Nat.lt_succ_iff.1 l.2⟩, a⟩) =
          X.pM (Sum.inl ⟨⟨l', Nat.lt_succ_iff.1 l'.2⟩, a'⟩) :=
        h3.symm.trans (h.trans h3')
      have e2 := Sum.inl.inj (hM e)
      have el : l = l' := Fin.ext (congrArg (fun s : Σ f : X.num.Fo, X.num.LkM E f.1 => s.1.1) e2)
      subst el
      have ea : a = a' := eq_of_heq (Sigma.mk.inj_iff.1 e2).2
      subst ea
      have ei : i = i' := (bldWfP_pl X l (Nat.lt_succ_iff.1 l.2)).1.inj (h1.trans h1'.symm)
      rw [ei]
    | none =>
      have e : X.pM (Sum.inl ⟨⟨l, Nat.lt_succ_iff.1 l.2⟩, a⟩) = X.pM (Sum.inr i') := h3.symm.trans h
      cases hM e
  | none =>
    cases b' with
    | some l' =>
      obtain ⟨a', -, -, h3'⟩ := bldWfP_plVL X l' i'
      have e : X.pM (Sum.inr i) = X.pM (Sum.inl ⟨⟨l', Nat.lt_succ_iff.1 l'.2⟩, a'⟩) :=
        Eq.trans h h3'
      cases hM e
    | none =>
      have e : X.pM (Sum.inr i) = X.pM (Sum.inr i') := h
      rw [Sum.inr.inj (hM e)]

theorem bldWfP_wfAtL (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) :
    X.nAt (X.atL l i) = X.Y.entF (X.plV (some l) i) := by
  obtain ⟨a, -, h2, h3⟩ := bldWfP_plVL X l i
  rw [h2, h3, X.mkN_pos l (Nat.lt_succ_iff.1 l.2)]
  rfl

end

theorem bldWf_where (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Field Fp] [Fintype Fp] [Algebra Fp E] : Spec.bldWf_where F E Fp := by
  intro X f _
  have hc : ∀ c, X.cKn f (X.num.v' f) c = X.mkN f (.k (X.num.v' f) (le_refl _) (Sum.inr c)) :=
    fun c => dif_pos (le_refl _)
  refine ⟨fun n => ⟨fun ⟨c, e⟩ => ⟨c, e.trans (hc c)⟩, fun ⟨c, e⟩ => ⟨c, e.trans (hc c).symm⟩⟩,
    fun h a => ?_, fun _ => rfl⟩
  rw [X.mkN_pos f h]
  rfl

end Cb
