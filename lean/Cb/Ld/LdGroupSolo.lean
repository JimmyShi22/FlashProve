-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupSolo.lean: this file is for toys (a toy: a small example instance). Several oracle
messages under one code (a group of copies of one oracle message), each a single row, are arranged
on a Boolean cube, in the form (`GShape`: the shape of a group) that the sumcheck that folds rows on
a cube takes: each at its corner (`cor`), but for the held ones (`cl`), which are repeated at every
corner.

Definitions, statements as theorems, proofs. Abstract field, variable codes.

Why: the standard group of Cb/Ld/LdGroupStd.lean has messages declared as main rows under a base
code beside mask rows under a mask code. The toys of a segment's body send families of copies of one
small oracle message under one code (Cb/Req1/LdSegRefToy.lean; `datSig`,
Cb/Req1/LdSegRefToyKit.lean). Such a family fits the shape of a group (Cb/Ld/LdGroupFold.lean:
`GShape`) too.

Main names:
  `Reshape.solo C Zb`, `ldShape_solo`: a code C as one main row under itself beside no mask rows: a
    code in another shape (Cb/Ld/LdBatShape.lean), with its laws; every codeword of the new shape
    comes from the old one.
  `SoloD E P`: among the data: the names I; the fold's mask code Zb; members (mem), what is read
    after the bridge (kp), what is held (cl; hm: held ⇒ member; hc: member or kept).
  `D.sh : GShape D.G`: a held member is in a kept slot (copied into every super-row:
    Cb/Ld/LdGroupFold.lean), every other member at its corner; all other corners are virtual zero
    rows; there are no mask rows (the fold's mask table is all virtual zero rows).
  `solo_fits`: `D.G.Fits` (`Grp.Fits`, Cb/Ld/LdBatSig.lean). `solo_ok`: the laws of Cb and Zb, cor
    injective, 1 ≤ h + g ⇒ `D.sh.OK` (`GShape.OK`, Cb/Ld/LdGroupFold.lean). `solo_held`: `D.hd.Laws`
    (`GHeld.Laws`, Cb/Ld/LdGroupSeg.lean): no premise beside D, whose fields hm, hc, neCh are
    proofs.

In `solo_ok` the laws of Cb and Zb are premises. The laws of a code read under a transformation
(`C.Laws`, that is `LdCode.Laws`) ask: the encoder `C.enc`, as a map of the pair (message,
randomness), and the transformation `C.T`, from native words to long words, are linear over E; the
encoder sends only the zero message with zero randomness to zero; and, for every long position x,
any two native words that agree at the native positions `C.src x` have the same long symbol at x.

Notation: `h`, `g`: the cube has h + g variables; `n`: the largest degree of a round polynomial;
`Ch`, `val`: the challenge set, and its map into E; `AaW`, `TW`, `srcW`, `pk`, `Qw`: the fields of
these names of `SumPar` (all of them: Cb/Ld/LdSum.lean).

Limits: this file says nothing on the fold's own hypotheses, and nothing on a signature whose
members are equal to one oracle message only case by case (a sum of families):
Cb/Ld/LdGroupPack.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupSegProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- A code as one main row under itself, beside no mask rows. -/
def Reshape.solo {E P : Type} (C Zb : LdCode E P) : Reshape C ((C.il Unit).pair (Zb.il Empty)) where
  wd := fun f =>
    LdCode.mkW (C₁ := C.il Unit) (C₂ := Zb.il Empty) (fun p s => f p s.2) fun _ s => s.1.elim
  up := fun w =>
    (Sum.elim (fun n => w.1 n.2) fun n => n.1.elim, Sum.elim (fun n => w.2 n.2) fun n => n.1.elim)
  dn := fun w => (fun j => w.1 (.inl ((), j)), fun q => w.2 (.inl ((), q)))
  fm := fun a => Sum.elim (fun n => a n.2) fun n => n.1.elim

theorem ldShape_solo {E P : Type} [Field E] [Finite P] (C Zb : LdCode E P) :
    (Reshape.solo C Zb).Laws ∧ ∀ e, (Reshape.solo C Zb).Fix e := by
  refine ⟨⟨fun f g x h => ?_, fun w => ?_, fun f w' x h => ?_, fun w => rfl,
      fun f g h => ?_, fun a w' => ?_⟩,
    fun e f w' _ => ?_⟩
  · funext α
    rcases α with ⟨u, α⟩ | ⟨e, _⟩
    · exact congrFun h α
    · exact e.elim
  · funext p
    rcases p with p | p
    · rfl
    · funext s
      exact s.1.elim
  · funext α
    exact congrFun h (.inl ((), α))
  · funext p s
    exact congrFun (congrFun h (.inl p)) ((), s)
  · show ∑ j : (Unit × C.J) ⊕ (Empty × Zb.J),
        Sum.elim (fun n : Unit × C.J => a n.2) (fun n : Empty × Zb.J => n.1.elim) j * w'.1 j =
      ∑ j, a j * w'.1 (.inl ((), j))
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp
  · refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
    · rcases n with ⟨u, j⟩ | ⟨e, _⟩
      · rfl
      · exact e.elim
    · rcases n with ⟨u, j⟩ | ⟨e, _⟩
      · rfl
      · exact e.elim

/-- A group of copies of one oracle message: the data. -/
structure SoloD (E P : Type) [Field E] [Fintype P] where
  I  : Type
  [finI : Fintype I]
  [decI : DecidableEq I]
  /-- the one code, its sample, the radius; the mask code of the fold -/
  Cb : LdCode E P
  Zs : Sample E Cb.J
  e  : ℕ
  Zb : LdCode E P
  /-- members; what is read after the bridge; what is held -/
  mem : I → Prop
  [decMem : DecidablePred mem]
  kp  : I → Prop
  [decKp : DecidablePred kp]
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  hm  : ∀ k : {a // cl a}, mem k.1.1
  hc  : ∀ o, mem o ∨ kp o
  /-- the cube, and a corner for each member -/
  h : ℕ
  g : ℕ
  cor : {o // mem o} → Fin (h + g) → Bool
  /-- what the fold needs beside codes and forms -/
  n : ℕ
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  val : Ch → E
  AaW : Type
  TW : Zb.Word → P → AaW → E
  srcW : P → Finset Zb.NP
  pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × Zb.J → E
  Qw : Slf E (Fin (h + g) → E) Zb.J

attribute [instance] SoloD.finI SoloD.decI SoloD.decMem SoloD.decKp
  SoloD.decCl SoloD.finCh SoloD.neCh

namespace SoloD
variable {E P : Type} [Field E] [Fintype P] (D : SoloD E P)

@[reducible] def o : OMsg E := OMsg.plain D.Cb D.Zs D.e fun _ => 0
@[reducible] def S : Sig E := { O := D.I, om := fun _ => D.o }
@[reducible] def G : Grp D.S := { P := P, mem := D.mem, pos := fun _ x => x, e := D.e }

/-- the member is held -/
def hp (a : D.G.A) : Prop := ∃ h : D.kp a.1, D.cl ⟨a.1, h⟩

open Classical in
/-- The shape: each member is one main row; a held member is in a kept slot, every other one at its
corner; all other corners are virtual zero rows; no mask rows. -/
def sh : GShape D.G where
  Cb := D.Cb
  Zb := D.Zb
  Kp := {a : D.G.A // D.hp a}
  h := D.h
  g := D.g
  Rm := fun _ => Unit
  Rz := fun _ => Empty
  view := Reshape.fam fun _ : D.G.A => Reshape.solo D.Cb D.Zb
  dst := fun r => if h : D.hp r.1 then .inr ⟨r.1, h⟩ else .inl (D.cor r.1)
  ord := fun b => if h : ∃ a : D.G.A, ¬ D.hp a ∧ D.cor a = b then some ⟨h.choose, ()⟩ else none
  kept := fun j => ⟨j.1, ()⟩
  dstZ := fun r => r.2.elim
  ordZ := fun _ => none
  n := D.n
  Ch := D.Ch
  val := D.val
  AaW := D.AaW
  TW := D.TW
  srcW := D.srcW
  pk := D.pk
  Qw := D.Qw

/-- The held messages. -/
@[reducible] def hd : GHeld D.sh D.kp where
  cl := D.cl
  mem := D.hm
  slot := fun k _ => ⟨⟨k.1.1, D.hm k⟩, ⟨k.1.2, k.2⟩⟩
  unW := fun _ f p s => f p ((), s)
  cJ := fun _ j => ((), j)
  cQ := fun _ q => ((), q)

end SoloD

theorem solo_fits {E P : Type} [Field E] [Fintype P] (D : SoloD E P) : D.G.Fits := fun _ _ _ h => h

theorem solo_ok {E P : Type} [Field E] [Fintype E] [Fintype P] (D : SoloD E P) (hC : D.Cb.Laws)
    (hZ : D.Zb.Laws) (hcor : Function.Injective D.cor) (h1 : 1 ≤ D.h + D.g) : D.sh.OK := by
  classical
  refine ⟨(ldShape_fam E P D.G.A _ _ (fun _ => Reshape.solo D.Cb D.Zb)
      (fun _ => (ldShape_solo D.Cb D.Zb).1)).1,
    hC, hZ, fun r => ?_, fun r => r.2.elim, h1⟩
  split
  · next b hb =>
    obtain ⟨a, u⟩ := r
    by_cases hh : D.hp a
    · simp only [SoloD.sh, dif_pos hh] at hb
      cases hb
    · simp only [SoloD.sh, dif_neg hh] at hb
      obtain rfl : D.cor a = b := Sum.inl.inj hb
      have hex : ∃ a' : D.G.A, ¬ D.hp a' ∧ D.cor a' = D.cor a := ⟨a, hh, rfl⟩
      show (if h : ∃ a' : D.G.A,
          ¬ D.hp a' ∧ D.cor a' = D.cor a then some (⟨h.choose, ()⟩ : Σ _ : D.G.A, Unit) else none) =
        some ⟨a, u⟩
      rw [dif_pos hex, hcor hex.choose_spec.2]
      rfl
  · next j hj =>
    obtain ⟨a, u⟩ := r
    by_cases hh : D.hp a
    · simp only [SoloD.sh, dif_pos hh] at hj
      obtain rfl := Sum.inr.inj hj
      rfl
    · simp only [SoloD.sh, dif_neg hh] at hj
      cases hj

theorem solo_held {E P : Type} [Field E] [Fintype P] (D : SoloD E P) : D.hd.Laws :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ h => funext fun α => congrFun h ((), α)⟩

end Cb
