-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyWfJ.lean: a small test instance at which all hypotheses of the theorem on the preamble
of weights-formedness below the Johnson radius (`LdWfE.John`, `Spec.ldJn_wf`,
Cb/Obj/LdObjectJohnTests.lean) are proved together, so that this theorem holds of something: the two
oracle messages that the preamble sends are read at the radius 3 of the distance 6: beyond a third
and not below half the distance, with the Johnson bound as the bound on lists.

Definitions, statement (`Cb.Gl.Spec.gl_wfToyJ`) and proofs. A guard against empty theorems; no
parameter of a protocol.
The preamble of weights-formedness is the sub-protocol for the claim that an encoded index decodes
to a message that holds an index, where lookups describe the index set.
The data are those of Cb/GlVal/GlToyWf.lean, Cb/GlVal/GlToyWfMasks.lean, Cb/GlVal/GlToyWfItem.lean,
changed in two places:
  (a) the pad's coefficient of a sample is drawn among all values other than 0 (`Wf8J.Bq`): with
    the one value 1 a sample's number (`Sample.err`) would be the number of all its seeds, and
    at lists of two the seed round's error
    would be at least its number of values;
  (b) the two oracle messages that the preamble sends are read at radius 3 (there: 1) of the
    distance 6 of the code on the subgroup of order 8: 8 · (8 - 6) = 16 < 25 = (8 - 3)^2: below the
    Johnson radius; 3 · 3 > 6; 2 · 3 = 6.
The bounds for lists are the Johnson bound `listMax 8 6 3`
(`listMax n d e := n * (d - e) / ((n - e) ^ 2 - n * (n - d))`, Cb/Gen/JohnsonList.lean;
by hand: 8 · 3 / 9, rounded down: 2).
The configuration is unchanged: its radius of decoding is 1; its sample map is `Sample.nil`.
Why so much is stated again: the radius is a field of an oracle message, so the signature is another
term, and what speaks of the signature is stated and proved again here (the same proofs); what does
not (keys, tables, the lookup's data and places, the model) is taken over as it stands.

Main names:
  `Wf8J.ZJ Ln`: all data (`LdWfE F E`, Cb/Ld/LdWfEnd.lean), for any data Ln of the test that
    follows; lists: `LJ`, `LJ`; each encoding bears 2 long positions.
  `Spec.gl_wfToyJ`: for every Ln: all conditions; neither 3 · 3 < 6 nor 2 · 3 < 6; and so the two
    items of the object for the preamble (`PreListR`, `PreKnowR`, Hiop/RecSubs.lean) and "the
    preamble bears what follows" (`Side`, Ior/KnowCollPiece.lean): with no hypothesis beside
    whatever the argument `Ln` holds as proofs: weights-formedness asks no bound on agreement.

No clause needs F = E (the two fields: Cb/GlVal/GlToyWf.lean).

Notation: `LdWfE.John` (Cb/Obj/LdObjectJohnTests.lean): `Z.Rest p` and five fields: `confH`: `Half`
of the configuration; and of every oracle message a: `dist`: `Dist` at `dS a`; `inJ`: `InJohnson`;
`isL`: `Z.L a` is `listMax`; `ev`: `Evades`.

Limits: the toy has one forest: this file says nothing on more than one. (Forest: `LdWfP`,
Cb/Ld/LdWf.lean.) It says nothing on the size of errors. (With lists of 2 the sending's seed round
has an error other than 0.) On security the file has one statement: it concludes `PreKnowR` and
`PreListR` (field `exact`), at `nums.err`, `nums.bud`, which are not evaluated here: no level of
security is said.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyWfItem
import Cb.GlVal.GlToyWfMasks
import Cb.Ld.LdWfEndThird
import Cb.Obj.LdObjectJohnTestsProofs

set_option autoImplicit false

namespace Cb.Gl
namespace Wf8J
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp Wf8

noncomputable section

/-- The values other than 0: the pad's coefficients. (Lists may have two members here, so a
sample's number is read:
with the one coefficient 1 it would be the number of all its seeds.) -/
def Bq : Type := {x : E // x ≠ 0}

instance : Fintype Bq := Fintype.ofFinite {x : E // x ≠ 0}
instance : Nonempty Bq := ⟨(⟨1, one_ne_zero⟩ : {x : E // x ≠ 0})⟩

/-- The value. -/
def Bq.val (β : Bq) : E := Subtype.val (p := fun x : E => x ≠ 0) β

/-- The family, read at radius 3; the pad's coefficient is drawn among all values other than 0. -/
abbrev Fm3 : StdFam E :=
  { Fm with
    e₁ := 3, e₂ := 3
    Z₁ := Sample.pad E Ix Ix Unit Bq (fun i j => decide (j = i)) (fun _ => 1) Bq.val
    Z₂ := Sample.pad E Im Im Unit Bq (fun i j => decide (j = i)) (fun _ => 1) Bq.val }

/-- The bound on lists: the Johnson bound at eight positions, distance 6, radius 3. -/
abbrev LJ : ℕ := listMax (Fintype.card P8) 6 3

/-- The data of the preamble. -/
@[reducible] def P3 : LdWfP E Cf.conf where
  S := Fm3.sig
  Sd := Sig.Seeds.indep Fm3.sig
  Body := Ix → E
  body := Fm3.vec
  bodyOf := P.bodyOf
  N := Nm
  ent := fun m => Sum.elim (Fm3.vec m) (Fm3.msk m)
  n := P.n
  v := P.v
  d := P.d
  key := P.key
  tab := P.tab
  mult := P.mult
  nR := P.nR
  gC := P.gC
  gR := P.gR
  Rw := P.Rw
  k := P.k
  mat := P.mat
  off := P.off
  gOf := P.gOf
  cOf := P.cOf
  Z := P.Z
  deg := P.deg
  wAt := P.wAt

/-- The places and numbers of the lookup: unchanged. -/
@[reducible] def Kl3 : P3.Lks :=
  { v' := Kl.v', w := Kl.w, n := Kl.n, bAt := Kl.bAt, wS := Kl.wS, cS := Kl.cS, wAt := Kl.wAt,
    cAt := Kl.cAt, wK := Kl.wK, cK := Kl.cK, wT := Kl.wT, cT := Kl.cT, wE := Kl.wE,
    wB := Kl.wB, cB := Kl.cB }

/-- The data of the preamble and of the test. -/
@[reducible] def W3 (Ln : ToyLn) : LdOWf F E where
  Cf := Cf
  P := P3
  klo := 0
  e := (Equiv.sumEmpty (Fin 1) (Fin 0)).symm
  l := Ln.l
  lay := fun _ => ()
  py := Ln.py
  e' := Ln.e'
  t := Ln.t
  NW := Ln.NW
  SdW := Ln.SdW
  iW := Ln.iW
  lW := Ln.lW
  NU := Ln.NU
  SdU := Ln.SdU
  iU := Ln.iU
  lU := Ln.lU
  NO := Ln.NO
  SdO := Ln.SdO
  iO := Ln.iO
  lO := Ln.lO

/-- The mask entries cut into the same three blocks. -/
def Kb3 : Fm3.Blk where
  Bk := TB
  I := TB.I
  σ := Kb.σ

/-- Where the named entries stand. -/
def nAt3 : Nm → Fm3.sig.Ent :=
  Sum.elim (fun c => ⟨false, Fm3.at₁ c⟩) fun i => ⟨true, Fm3.ν₂.symm (Sum.inl i)⟩

/-- What the lookup's reading keeps. (`LkAsm2.srAll`, Cb/Ld/LdLkpMaskAsm2.lean) -/
def Rl3 (l : ℕ) : P3.bt.J → Prop := (Kl3.asm l).srAll (Kl3.Dt l)

/-- The honest sender. -/
abbrev D3 : P3.S.Sender (P3.Body × P3.Wp) P3.Wp := Fm3.snd P3.Wp (p0, ())

end

/-! ### Codes and sender -/

theorem inJ8 : InJohnson (Fintype.card P8) 6 3 := by
  rw [card8]
  show 8 * (8 - 6) < (8 - 3) ^ 2
  norm_num

theorem Bq.val_inj : Function.Injective Bq.val := fun _ _ h => Subtype.ext h
theorem Bq.val_ne (β : Bq) : β.val ≠ 0 := Subtype.property (p := fun x : E => x ≠ 0) β

theorem padq_ok (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ]
    (pl : J₀ → μ → Bool) (h : Function.Injective pl) :
    (Sample.pad E μ J₀ Unit Bq pl (fun _ => 1) Bq.val).OK :=
  fun v hv =>
    ood_okOn_pad E E μ J₀ Unit Bq pl _ _ h Bq.val_inj std_padBasis.1 v (fun _ => ⟨_, rfl⟩) hv

theorem padq_priv (J₀ μ : Type) [Fintype J₀] [Fintype μ] [DecidableEq μ] (pl : J₀ → μ → Bool) :
    (Sample.pad E μ J₀ Unit Bq pl (fun _ => 1) Bq.val).Private E fun _ => True :=
  fun ρ _ a => ood_private_pad E E μ J₀ Unit Bq pl _ _ std_padBasis ρ (Bq.val_ne ρ.2) a

theorem famHyp3 : Fm3.Hyp LJ LJ 2 2 where
  laws₁ := famHyp.laws₁
  laws₂ := famHyp.laws₂
  list₁ := ld_list_johnson E P8 Fm3.C₁ 6 3 famHyp.laws₁
    (fam8_hyp Ix Im Ix Im _ _ oneHot_inj oneHot_inj).2.1 inJ8
  list₂ := ld_list_johnson E P8 Fm3.C₂ 6 3 famHyp.laws₂
    (fam8_hyp Ix Im Ix Im _ _ oneHot_inj oneHot_inj).2.2.1 inJ8
  ok₁ := padq_ok Ix Ix _ oneHot_inj
  ok₂ := padq_ok Im Im _ oneHot_inj
  priv₁ := padq_priv Ix Ix _
  priv₂ := padq_priv Im Im _
  zk₁ := famHyp.zk₁
  zk₂ := famHyp.zk₂

/-! ### What does not speak of the signature (of `lks3`: all but its clause `mult`) -/

theorem lin3 : P3.LinKeys (fun _ => 0) (fun _ _ => 0) (fun _ _ _ => 1) := by
  rcases lin with ⟨⟩
  constructor <;> assumption

theorem own3 : P3.OwnPlaces (fun _ => True) := by
  rcases own with ⟨⟩
  constructor <;> assumption

theorem laws3 : P3.Laws where
  describes := describes
  held_hold := ldCf_held_hold F E Cf (toyCf8_ok ToyMo8.two).held
  dcd_enc := ldCf_dcd_enc F E Cf (toyCf8_ok ToyMo8.two).core.dist (toyCf8_ok ToyMo8.two).rad
  multOf := multOf
  keyLin := ldWfK_keyLin E Cf.conf P3 _ _ _ lin3

theorem lks3 : Kl3.OK p := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := lks
  exact ⟨h1, h2,
    fun f hf _ U _ h => valid_congr (fun b hb => ldWfB_key E Cf.conf P3 laws3 f hf U b hb) h,
    h4, h5, h6⟩

/-! ### Places -/

theorem nAt3_inj : Function.Injective nAt3 := by
  rintro (a | a) (b | b) h
  · have h' : (⟨false, Fm3.at₁ a⟩ : Fm3.sig.Ent) = ⟨false, Fm3.at₁ b⟩ := h
    exact congrArg Sum.inl
      (Sum.inl_injective (Fm3.ν₁.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))
  · exact absurd (show false = true from congrArg Sigma.fst h) (by decide)
  · exact absurd (show true = false from congrArg Sigma.fst h) (by decide)
  · have h' : (⟨true, Fm3.ν₂.symm (Sum.inl a)⟩ : Fm3.sig.Ent) = ⟨true, Fm3.ν₂.symm (Sum.inl b)⟩ := h
    exact congrArg Sum.inr
      (Sum.inl_injective (Fm3.ν₂.symm.injective (eq_of_heq (Sigma.mk.inj h').2)))

theorem entAt3 : P3.EntAt nAt3 where
  ent := fun _ n => by cases n <;> rfl
  inj := nAt3_inj

theorem noPad3 (n : Nm) : Fm3.NoPad (nAt3 n) := by
  cases n with
  | inl c =>
    show (Fm3.ν₁ (Fm3.ν₁.symm (Sum.inl c))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl
  | inr i =>
    show (Fm3.ν₂ (Fm3.ν₂.symm (Sum.inl i))).isLeft = true
    rw [Equiv.apply_symm_apply]
    rfl

theorem pl3 (l : ℕ) : (Kl3.pl Rl3 l).OK ∧ ∀ j, (Kl3.pl Rl3 l).At j ↔ (Kl3.asm l).swAll j :=
  (ldLkpPl2_asm E (Kl3.asm l) Cf.conf.E0 (Cf.conf.Msg × P3.S.Msg) Unit Unit P3.msg
    (Rl3 l) (Kl3.Dt l) (maskW l)).1

theorem pl3_ex (l : ℕ) (i : (Kl3.pl Rl3 l).I) : ∃ c, (Kl3.pl Rl3 l).pl i = Sum.inr (mkAt c) :=
  (sw_iffW l _).1 (((pl3 l).2 _).1 ⟨i, rfl⟩)

noncomputable section

/-- The names of the places of the lookup's own masks (`LdWfP.Lks.pl`) are the toy's names
(`LkpToyE.Mk E`). -/
def sg3 (l : ℕ) : (Kl3.pl Rl3 l).I ≃ LkpToyE.Mk E :=
  Equiv.ofBijective (fun i => Classical.choose (pl3_ex l i))
    ⟨fun i i' h => (pl3 l).1.inj (by
        have h1 := Classical.choose_spec (pl3_ex l i)
        have h2 := Classical.choose_spec (pl3_ex l i')
        have h' : Classical.choose (pl3_ex l i) = Classical.choose (pl3_ex l i') := h
        rw [h1, h2, h']),
      fun c => by
        obtain ⟨i, hi⟩ := ((pl3 l).2 _).2 ((sw_iffW l _).2 ⟨c, rfl⟩)
        exact ⟨i, inrMk_inj ((Classical.choose_spec (pl3_ex l i)).symm.trans hi)⟩⟩

theorem sg3_at (l : ℕ) (i : (Kl3.pl Rl3 l).I) : (Kl3.pl Rl3 l).pl i = Sum.inr (mkAt (sg3 l i)) :=
  Classical.choose_spec (pl3_ex l i)

/-- The places of all masks. -/
@[reducible] def X3 : Kl3.MaskPl D3 Rl3 where
  nAt := nAt3
  RdW := Fm3.NoPad
  L := Kb3.lay P3.Wp (p0, ())
  bk := bkOf
  eL := fun l => Equiv.arrowCongr (sg3 l).symm (Equiv.refl E)
  eB := Equiv.refl _
  atL := fun l i => mkAt (sg3 l i)

/-- All data. -/
@[reducible] def ZJ (Ln : ToyLn) : LdWfE F E :=
  ⟨W3 Ln, Kl3, D3, Fm3.two LJ LJ, Fm3.two 2 2, Rl3, fun _ => True, X3, p0, fun _ _ => 0, fun _ => 0,
    fun _ _ => 0, fun _ _ _ => 1⟩

end

theorem pa3_eq : ∀ (b : Option (Fin (P3.n + 1))) (i : X3.I b),
    ∃ m : TB.I (bkOf b), nAt3 (X3.pa b i) = Kb3.at' (bkOf b) m ∧ ∀ ms : ∀ c, TB.I c → E,
  X3.vl b (ms (bkOf b)) i = ms (bkOf b) m
  | some l, i => ⟨sg3 l i, rfl, fun _ => rfl⟩
  | none, i => ⟨i, rfl, fun _ => rfl⟩

theorem pa3_surj :
    ∀ (b : Option (Fin (P3.n + 1))) (m : TB.I (bkOf b)),
      ∃ i : X3.I b, nAt3 (X3.pa b i) = Kb3.at' (bkOf b) m
  | some l, m => ⟨(sg3 l).symm m, by
      show nAt3 (mkAt (sg3 l ((sg3 l).symm m))) = _
      rw [Equiv.apply_symm_apply]
      rfl⟩
  | none, m => ⟨m, rfl⟩

theorem restJ (Ln : ToyLn) : (ZJ Ln).Rest p := by
  obtain ⟨s1, -, -, s4, s5, s6, s7, -⟩ := stdFam_all E Fm3 LJ LJ 2 2 P3.Wp (p0, ()) famHyp3
  obtain ⟨hpad, -, -, -, hown, hoff⟩ := stdFamL_all E Fm3 Kb3 LJ LJ 2 2 P3.Wp (p0, ()) famHyp3
  exact
  { val := ⟨Cf.conf.enc p0.1.1 p0.1.2⟩
    describes := describes
    lin := lin3
    lks := lks3
    deg := deg
    zOK := zOK
    laws := s1
    fair := s4
    sender := s5
    sBlind := s6 _
    hides := s7
    multOf := multOf
    pad := hpad P3.Sd
    sOwn := fun b w ms f η i => by
      obtain ⟨m, e1, e2⟩ := pa3_eq b i
      show Fm3.sig.ents _ (nAt3 (X3.pa b i)) = X3.vl b (ms (bkOf b)) i
      rw [e1, e2 ms]
      exact hown (bkOf b) w ms f η m
    sOff := fun b w ms ms' f η η' n ho hn hne => hoff (bkOf b) w ms ms' f η η' n ho hn fun m => by
      obtain ⟨i, e⟩ := pa3_surj b m
      rw [← e]
      exact hne i
    tie := fun _ _ _ => rfl
    lkPl := fun f _ => placesW f
    rdL := fun _ _ _ h => h
    own := own3
    ent := entAt3
    inRd := fun _ _ => noPad3 _
    rdJ := fun _ n _ => noPad3 n
    atEq := fun l i => sg3_at l i
    ownL := fun l i => Or.inr ((sw_iffW l _).2 ⟨sg3 l i, rfl⟩)
    apart := fun b j hj n hS => by
      refine ⟨noPad3 n, fun i e => ?_⟩
      cases b with
      | some l =>
          have hj' : j < (l : ℕ) := hj
          have hl : (l : ℕ) < 0 + 1 := l.2
          omega
      | none =>
          have e' : n = btAt i := e
          rcases hS with (⟨rc, h⟩ | ⟨u, i', h⟩) | hw
          · cases h
          · exact bit_ne _ i ((Sum.inr.inj h).symm.trans e')
          · obtain ⟨c, h⟩ := (sw_iffW j _).1 hw
            exact mk_ne c i ((Sum.inr.inj h).symm.trans e') }

theorem john (Ln : ToyLn) : (ZJ Ln).John p (fun _ => 6) where
  toRest := restJ Ln
  confH := ⟨core8, distC8 ToyMo8.two, (by norm_num : 2 * 1 < 6), smp8 ToyMo8.two, model8 ToyMo8.two⟩
  dist := fun a => by
    cases a
    · exact (fam8_hyp Ix Im Ix Im _ _ oneHot_inj oneHot_inj).2.1
    · exact (fam8_hyp Ix Im Ix Im _ _ oneHot_inj oneHot_inj).2.2.1
  inJ := fun a => by
    cases a
    · exact inJ8
    · exact inJ8
  isL := fun a => by cases a <;> rfl
  ev := (stdFam_all E Fm3 LJ LJ 2 2 P3.Wp (p0, ()) famHyp3).2.2.1

end Wf8J

namespace Spec
open Iop Hiop IOR Wf8 Wf8J

/-- The guard: all conditions of `LdWfE.John` are met together. With them the statement has the
conclusions of `Spec.ldWfEnd` and `Spec.ldWfEnd_side` (Cb/Ld/LdWfEnd.lean) at `ZJ Ln`. -/
def gl_wfToyJ : Prop :=
  ∀ (Ln : ToyLn),
    (ZJ Ln).John p (fun _ => 6) ∧
    ¬ 3 * 3 < 6 ∧ ¬ 2 * 3 < 6 ∧
    PreListR (ZJ Ln).W.O.left (ZJ Ln).G.B.wf (ZJ Ln).G.B.hWf id id
      (ZJ Ln).W.Cf.conf.Rwf (ZJ Ln).G.B.nums ∧
    PreKnowR (ZJ Ln).W.O.left (ZJ Ln).G.B.wf (ZJ Ln).W.Cf.conf.free (ZJ Ln).W.Cf.conf.RwfR
      (fun _ _ _ => ()) (ZJ Ln).G.B.nums.err ∧
    ∀ q : Finset (ZJ Ln).W.Cf.conf.E0.Pos → Prop,
      Side (ZJ Ln).G.B.wf (ZJ Ln).G.B.hWf (ZJ Ln).G.B.nums.bud q ((ZJ Ln).W.P.S.qFam q (ZJ Ln).t)

end Spec

open Wf8J in
theorem gl_wfToyJ : Spec.gl_wfToyJ := fun Ln =>
  have h := ldJn_wf F E (ZJ Ln) p _ (john Ln)
  ⟨john Ln, by norm_num, by norm_num, (ldWfEnd p (ZJ Ln) 1 h).1,
    (ldWfEnd p (ZJ Ln) 1 h).2, fun q => ldWfEnd_side p (ZJ Ln) 1 q h⟩

end Cb.Gl
