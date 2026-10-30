-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegWhole.lean: a segment from its body and the data of its closing, for one group and for
two.

Definitions, statements (Cb.Spec.ldSegWhole_*) and proofs.
In standard terms: book-keeping for one piece of the preamble of a request (`LdReq`,
Cb/Req1/LdReq.lean): a sequence of interactive oracle reductions, written out as one term.
Cb/Req1/LdSeg.lean states a segment (`LdSeg`) over arbitrary lists of moves. Here the four parts
after the body are terms, made from the data of the closing, and the segment's hypotheses are
reduced to those of its blocks.

Main names:
  `segOne D body hT l Q`: one group. body: any list of moves that ends at "rows on all entries,
    beside A₀ of the messages that are kept"; D (Cb/Req1/LdSegClose.lean: `LdCl1`): the rows, the
    evader, the group, the folded complex, the held messages; l: the link bridge-to-fold, a
    parameter; Q (Cb/Req1/LdSegFit.lean: `LdCloseD`): the one sending and the locations.
    The parts: [many rows into one; the one row is a row on the group] [bridge-to-fold] [one
    sending] [locations].
  `F.nest ..`: the data of Cb/Req1/LdSegFitTwo.lean from those of Cb/Req1/LdSegClose.lean; its
    second bridge-to-fold is `F.fold₂` (`Spec.ldSegWhole_nest`: by definition).
  `segTwo D F body hT l₁ l₂ ..`: two groups. [many rows into one; a part on each group; the split;
    the second row goes inside] [bridge-to-fold on the first; the open test goes inside;
    bridge-to-fold on the second] [one sending] [locations of the second test; a re-bracketing;
    locations of the first]. Asked, here and in `F.nest`, `Spec.ldSegWhole_nest`,
    `Spec.ldSegWhole_two`: both folded codes have at least one long position (`Nonempty D.Pf`,
    `Nonempty F.Pf`).
  `Spec.ldSegWhole_one`: `(segOne ..).Hyp` from: body.Hyp; the evader's law; the rows vanish outside
    the group; D.fold.Hyp l; the sending's seven hypotheses.
  `Spec.ldSegWhole_two`: `(segTwo ..).Hyp` from: body.Hyp; the evader's law; F.OK (supports; the
    mask entry; the second group is kept and not held at the first closing; the two readings agree);
    the two folds' hypotheses; the sending's seven.
  So `Spec.ldSeg_goodB`, `Spec.ldSeg_into`, `Spec.ldSeg_nums` (Cb/Req1/LdSeg.lean) apply to both.

Limits: this file says nothing on bodies: body is any list of moves of the kinds "send", "sub",
"step" that ends at `D.bat.src`. Nothing on layouts: the cuts are any functions.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFitTwo
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdProg.all_nil (q : LdTag → Prop) (a : LdStage E Kc) : (LdProg.nil a).All q := by
  rw [LdProg.All]; trivial
theorem LdProg.all_snoc' (q : LdTag → Prop) {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).All q ↔ p.All q ∧ q m.tag := by rw [LdProg.All]

/-! ## One group -/

/-- many rows into one; the one row is a row on the group -/
def LdCl1.batP (D : LdCl1 E Kc) : LdProg D.bat.src D.fold.src :=
  .snoc (.snoc (.nil _) (.bat D.bat)) D.step

/-- A segment with one group. -/
def segOne {a : LdStage E Kc} (D : LdCl1 E Kc) (body : LdProg a D.bat.src)
    (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
    (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold) : LdSeg a Q.loc.tgt where
  b := D.bat.src
  b₁ := D.fold.src
  c := D.fold.tgt
  body := body
  bat := D.batP
  fold := Q.foldP l
  snd := Q.snd
  loc := Q.locP
  bodyT := hT
  batT := (LdProg.all_snoc' _ _ _).2
    ⟨(LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩, Or.inr (Or.inr rfl)⟩
  foldT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩
  locT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩

/-! ## Two groups -/

/-- The data of the second half of a closing with two groups. -/
@[reducible] def LdCl2b.nest {D : LdCl2 E Kc} (F : LdCl2b D) [Nonempty D.Pf] [Nonempty F.Pf]
    (t₁ t₂ : ℕ) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (cut₂ : N.Msg → F.Cf.N.Wit)
    (cut₁ : N.Msg → D.Cf.N.Wit) (bk₀ : N.Msg → Wp' → D.Wp) (L tN : N.O → ℕ) : LdNestD E Kc :=
  { P₁ := D.Pf, C₁ := D.Cf, e₁ := D.e, t₁ := t₁, h₁ := D.fold₁.held, Xc₁ := E × D.Stf,
    Φ₁ := D.slf.Holds, M := D.M, St₀ := D.St₀, Wp := D.Wp, E₀ := D.E₀, A₀ := D.A₀, S := D.S₂,
    G := D.G₂', kp := F.kp₂, B := Unit, Sb := fun _ => D.Sx, sl := fun _ => D.r₂', rd₁ := F.rd',
    Pf := F.Pf, Cf := F.Cf, Stf := F.Stf, slf := F.slf, e := F.e, cl := F.cl, sW := F.sW,
    sJ := F.sJ, sQ := F.sQ, N := N, Sd := Sd, Wp' := Wp', cut₂ := cut₂, cut₁ := cut₁, bk₀ := bk₀,
    L := L, tN := tN, t₂ := t₂ }

/-- the kinds of the moves of the last part -/
theorem LdNestD.locP_kinds (T : LdNestD E Kc)
    (Sn : T.N.Sender (T.outer.tgt.S.Wit × T.outer.tgt.Wp) (T.outer.tgt.S.Wit × T.Wp')) :
    (T.locP Sn).All fun t => t = .loc ∨ t = .step :=
  (LdProg.all_snoc' _ _ _).2
    ⟨(LdProg.all_snoc' _ _ _).2
        ⟨(LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩, Or.inr rfl⟩,
      Or.inl rfl⟩

/-- A segment with two groups. -/
def segTwo {a : LdStage E Kc} (D : LdCl2 E Kc) (F : LdCl2b D)
    (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
    (l₁ : Link Kc D.fold₁.src.J D.fold₁.mid) (l₂ : Link Kc F.fold₂.src.J F.fold₂.mid)
    [Nonempty D.Pf] [Nonempty F.Pf] (t₁ t₂ : ℕ) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
    (cut₂ : N.Msg → F.Cf.N.Wit) (cut₁ : N.Msg → D.Cf.N.Wit) (bk₀ : N.Msg → Wp' → D.Wp)
    (L tN : N.O → ℕ)
    (Sn : N.Sender (F.fold₂.tgt.S.Wit × F.fold₂.tgt.Wp) (F.fold₂.tgt.S.Wit × Wp')) :
    LdSeg a (((F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).inner Sn).under
        ((F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).Y Sn)
        ((F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).Q Sn).loc.After).tgt where
  b := D.bat.src
  b₁ := D.fold₁.src
  c := F.fold₂.tgt
  body := body
  bat := D.progBat
  fold := F.progFold l₁ l₂
  snd := ((F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).Q Sn).snd
  loc := (F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).locP Sn
  bodyT := hT
  batT := (ldSegCl_kinds E Kc D F l₁ l₂).1
  foldT := (ldSegCl_kinds E Kc D F l₁ l₂).2
  locT := (F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).locP_kinds Sn

end

namespace Spec

/-- One group. -/
def ldSegWhole_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl1 E Kc)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold),
    body.Hyp → D.Z.OK → (∀ b st (n : D.S.Ent), ¬ D.G.mem n.1 → D.sl b st n = 0) →
    D.fold.Hyp l → Q.snd.Hyp → (segOne D body hT l Q).Hyp

/-- For `Nonempty D.Pf`, `Nonempty F.Pf` (as `F.nest` needs): the second bridge-to-fold of the
nested data is the closing's. -/
def ldSegWhole_nest : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdCl2 E Kc) (F : LdCl2b D) [Nonempty D.Pf]
      [Nonempty F.Pf] (t₁ t₂ : ℕ) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
      (cut₂ : N.Msg → F.Cf.N.Wit) (cut₁ : N.Msg → D.Cf.N.Wit)
      (bk₀ : N.Msg → Wp' → D.Wp) (L tN : N.O → ℕ),
    (F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).outer = F.fold₂

/-- Two groups. -/
def ldSegWhole_two : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl2 E Kc) (F : LdCl2b D)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l₁ : Link Kc D.fold₁.src.J D.fold₁.mid) (l₂ : Link Kc F.fold₂.src.J F.fold₂.mid)
      [Nonempty D.Pf] [Nonempty F.Pf] (t₁ t₂ : ℕ) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
      (cut₂ : N.Msg → F.Cf.N.Wit) (cut₁ : N.Msg → D.Cf.N.Wit) (bk₀ : N.Msg → Wp' → D.Wp)
      (L tN : N.O → ℕ)
      (Sn : N.Sender (F.fold₂.tgt.S.Wit × F.fold₂.tgt.Wp) (F.fold₂.tgt.S.Wit × Wp')),
    body.Hyp → D.Z.OK → F.OK → D.fold₁.Hyp l₁ → F.fold₂.Hyp l₂ →
    ((F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN).Q Sn).snd.Hyp →
    (segTwo D F body hT l₁ l₂ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn).Hyp

end Spec

theorem ldSegWhole_one : Spec.ldSegWhole_one := by
  intro E Kc _ _ a D body hT l Q hb hZ hs hl hq
  have h := ldSegCl_one E Kc D l hZ hs hl
  have h1 := (LdProg.hyp_snoc _ _).1 h
  obtain ⟨f1, f2, f3⟩ := ldSegFit_hyp E Kc D.fold Q l hl hq
  exact ⟨hb, h1.1, f1, f2, f3⟩

theorem ldSegWhole_nest : Spec.ldSegWhole_nest := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldSegWhole_two : Spec.ldSegWhole_two := by
  intro E Kc _ _ a D F body hT l₁ l₂ _ _ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn hb hZ hF h₁ h₂ hq
  obtain ⟨c1, c2⟩ := ldSegCl_two E Kc D F l₁ l₂ hZ hF h₁ h₂
  obtain ⟨-, f2, f3, -⟩ :=
    ldSegTwo_hyp E Kc (F.nest t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN) Sn l₂ h₂ h₁.laws hq
  exact ⟨hb, c1, c2, f2, f3⟩

end Cb
