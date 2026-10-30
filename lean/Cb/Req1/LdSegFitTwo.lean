-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFitTwo.lean: two groups close in one segment: the second fold, the one sending and the
two locations fit together with one re-bracketing in between.

Definitions, statements (Cb.Spec.ldSegTwo_*) and proofs.
A group (`Grp`, Cb/Ld/LdBatSig.lean) is some whole oracle messages of a signature, read at common
long positions. A bridge-to-fold is the data `LdFoldD` of a move "fold" (with `l`, an `IOR.Link`),
locations are the data `LdLocD` of a move "loc", a sending is the data `LdSendD` of a move "send"
(all three in Cb/Req1/LdSegKit.lean; the moves and a segment, `LdSeg`, in Cb/Req1/LdSeg.lean).
Cb/Req1/LdSegClose.lean ends, for two groups, at the fold on the second group, which carries the
open test of the first inside "what else is claimed" (a base joint `heldB`, Cb/Req1/LdSegKit.lean).
This file has the rest.

Main names:
  `LdNestD`: the first test, open (code C₁, radius, held messages, claim Φ₁, how what else is
    claimed reads messages and slots); the second group's bridge-to-fold; the family N of the one
    sending with cut₂, cut₁: (message, randomness) of the second and of the first folded complex, as
    the messages of N hold them; the numbers of locations t₂, t₁.
  `T.Q Sn : LdCloseD T.outer` (Cb/Req1/LdSegFit.lean), for the data Sn of an honest sender
    (`Sig.Sender`, Cb/Ld/LdSendFam.lean).
  `T.locP Sn`: locations of the second test; a step without rounds, which re-brackets the explicit
    part (`LdLocD.underStep`, Cb/Req1/LdSegFitUnder.lean); locations of the first test.
  `Spec.ldSegTwo_meet`: the stage after the second test's locations is the stage at which the step
    begins (by definition); `(T.inner Sn).Near` (by definition).
  `Spec.ldSegTwo_hyp`: from `T.outer.Hyp l` (`T.outer`: the second bridge-to-fold), the laws of the
    first test's slots (`T.h₁.Laws T.e₁`) and the sending's seven hypotheses (`(T.Q Sn).snd.Hyp`):
    the hypotheses of the fold, of the one sending and of `T.locP Sn`; the kinds of its moves are
    those of a segment's last part (`LdSeg.locT`).

Limits: this file says nothing on the first group's bridge-to-fold and the steps before
(Cb/Req1/LdSegClose.lean). Nothing on layouts.
-/
import Cb.Req1.LdSegFitUnder
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

/-- Two open tests and the one sending: the data. -/
structure LdNestD (E Kc : Type) [Field E] [Fintype E] : Type 1 where
  /-- the first test, open -/
  P₁  : Type
  [finP₁ : Fintype P₁]
  [neP₁ : Nonempty P₁]
  C₁  : LdCode E P₁
  e₁  : ℕ
  t₁  : ℕ
  h₁  : LdHeld E C₁
  Xc₁ : Type
  Φ₁  : Xc₁ → (C₁.J → E) → Prop
  /-- what else is claimed -/
  M   : Type
  St₀ : Type
  Wp  : Type
  E₀  : ExtSpec
  A₀  : Rels Kc St₀ E₀ (M × Wp)
  /-- the second group's bridge-to-fold -/
  S   : Sig E
  G   : Grp S
  kp  : S.O → Prop
  [decKp : DecidablePred kp]
  B   : Type
  Sb  : B → Type
  sl  : ∀ b, Slf E (Sb b) G.C.J
  rd₁ : (S.sub kp).Msg → (∀ k, (h₁.o k).Msg) → M
  Pf  : Type
  [finPf : Fintype Pf]
  [nePf : Nonempty Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (S.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (S.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (S.om k.1.1).C.Q → Cf.Q
  /-- the one sending -/
  N    : Sig E
  Sd   : N.Seeds
  Wp'  : Type
  cut₂ : N.Msg → Cf.N.Wit
  cut₁ : N.Msg → C₁.N.Wit
  bk₀  : N.Msg → Wp' → Wp
  L    : N.O → ℕ
  tN   : N.O → ℕ
  t₂   : ℕ

attribute [instance] LdNestD.finP₁ LdNestD.neP₁ LdNestD.decKp LdNestD.finPf
  LdNestD.nePf LdNestD.decCl

namespace LdNestD
variable {E Kc : Type} [Field E] [Fintype E] (T : LdNestD E Kc)

/-- The second bridge-to-fold: it carries the first test, open. -/
@[reducible] def outer : LdFoldD E Kc :=
  { S := T.S, G := T.G, kp := T.kp, B := T.B, Sb := T.Sb, sl := T.sl,
    St₀ := (T.Xc₁ × T.h₁.Smp) × T.St₀, Wp := T.C₁.N.Wit × T.Wp, E₀ := T.C₁.ext.prod T.E₀,
    A₀ := heldB T.C₁ T.e₁ T.h₁ T.Φ₁ T.rd₁ T.A₀, Pf := T.Pf, Cf := T.Cf, Stf := T.Stf, slf := T.slf,
    e := T.e, cl := T.cl, sW := T.sW, sJ := T.sJ, sQ := T.sQ }

variable (Sn : T.N.Sender (T.outer.tgt.S.Wit × T.outer.tgt.Wp) (T.outer.tgt.S.Wit × T.Wp'))

/-- The one sending and the second test's locations. -/
@[reducible] def Q : LdCloseD T.outer :=
  ⟨T.N, T.Sd, T.Wp', T.cut₂, fun n w' => (T.cut₁ n, T.bk₀ n w'), Sn, T.L, T.tN, T.t₂⟩

/-- what else is claimed in the end -/
def A₁ : Rels Kc T.St₀ T.E₀ ((T.outer.S₂.sum T.N).Msg × T.Wp') where
  rel  := fun st y w =>
    T.A₀.rel st y
      (T.rd₁ (T.outer.rd (T.outer.S₂.left T.N (T := OMsg.Msg) w.1)
            (T.outer.held.msg (T.cut₂ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1))
          (T.h₁.msg (T.cut₁ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1),
        T.bk₀ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1) w.2)
  relR := fun a w =>
    T.A₀.relR a
      (T.rd₁ (T.outer.rd (T.outer.S₂.left T.N (T := OMsg.Msg) w.1)
            (T.outer.held.msg (T.cut₂ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1))
          (T.h₁.msg (T.cut₁ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1),
        T.bk₀ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1) w.2)
  on   := T.A₀.on
  core := fun w =>
    T.A₀.core (T.rd₁
          (T.outer.rd (T.outer.S₂.left T.N (T := OMsg.Msg) w.1)
            (T.outer.held.msg (T.cut₂ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1))
          (T.h₁.msg (T.cut₁ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1)).1),
        T.bk₀ (T.outer.S₂.right T.N (T := OMsg.Msg) w.1) w.2)

/-- The first test's locations, read after the sending. -/
@[reducible] def inner : LdLocD E Kc :=
  { S := T.outer.S₂.sum T.N, P := T.P₁, C := T.C₁, e := T.e₁, t := T.t₁, hd := T.h₁, Xc := T.Xc₁,
    St₀ := T.St₀, Wp := T.Wp', E₀ := T.E₀, Φ := T.Φ₁,
    cut := fun m => T.cut₁ (T.outer.S₂.right T.N (T := OMsg.Msg) m), A₁ := T.A₁, A := (T.Q Sn).A₁ }

/-- what the second test's locations leave in the explicit part -/
abbrev Y : Type := ((E × T.Stf) × T.outer.held.Smp) × (T.Q Sn).loc.Lc

/-- The last part of the segment. -/
def locP :
    LdProg (T.Q Sn).snd.tgt ((T.inner Sn).under (T.Y Sn) (T.Q Sn).loc.After).tgt :=
  .snoc (.snoc (.snoc (.nil _) (.loc (T.Q Sn).loc))
      ((T.inner Sn).underStep (T.Y Sn) (T.Q Sn).loc.After))
    (.loc ((T.inner Sn).under (T.Y Sn) (T.Q Sn).loc.After))

end LdNestD

namespace Spec

def ldSegTwo_meet : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : LdNestD E Kc)
      (Sn : T.N.Sender (T.outer.tgt.S.Wit × T.outer.tgt.Wp) (T.outer.tgt.S.Wit × T.Wp')),
    (T.Q Sn).loc.tgt = (T.inner Sn).overSt (T.Y Sn) (T.Q Sn).loc.After ∧ (T.inner Sn).Near

def ldSegTwo_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (T : LdNestD E Kc)
      (Sn : T.N.Sender (T.outer.tgt.S.Wit × T.outer.tgt.Wp) (T.outer.tgt.S.Wit × T.Wp'))
      (l : Link Kc T.outer.src.J T.outer.mid),
    T.outer.Hyp l → T.h₁.Laws T.e₁ → (T.Q Sn).snd.Hyp →
    ((T.Q Sn).foldP l).Hyp ∧ (T.Q Sn).snd.Hyp ∧ (T.locP Sn).Hyp ∧
    (T.locP Sn).All fun t => t = .loc ∨ t = .step

end Spec

theorem ldSegTwo_meet : Spec.ldSegTwo_meet := fun _ _ _ _ _ _ =>
  ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ => rfl⟩

theorem ldSegTwo_hyp : Spec.ldSegTwo_hyp := by
  intro E Kc _ _ T Sn l h h₁ hs
  obtain ⟨a1, a2, a3⟩ := ldSegFit_hyp E Kc T.outer (T.Q Sn) l h hs
  have hin : (T.inner Sn).Hyp := ⟨(ldSegTwo_meet E Kc T Sn).2, h₁⟩
  obtain ⟨b1, -⟩ := ldSegUnder_hyp E Kc (T.inner Sn) (T.Y Sn) (T.Q Sn).loc.After hin
  obtain ⟨⟨-, c1⟩, c2⟩ : ((LdProg.nil _).Hyp ∧
        ((T.inner Sn).underStep (T.Y Sn) (T.Q Sn).loc.After).Hyp) ∧
      (LdMv.loc ((T.inner Sn).under (T.Y Sn) (T.Q Sn).loc.After)).Hyp := by
    have := (LdProg.hyp_snoc _ _).1 b1
    exact ⟨(LdProg.hyp_snoc _ _).1 this.1, this.2⟩
  refine ⟨a1, a2, ?_, ?_⟩
  · exact (LdProg.hyp_snoc _ _).2 ⟨(LdProg.hyp_snoc _ _).2 ⟨a3, c1⟩, c2⟩
  · rw [LdNestD.locP, LdProg.All, LdProg.All, LdProg.All, LdProg.All]
    exact ⟨⟨⟨trivial, Or.inl rfl⟩, Or.inr rfl⟩, Or.inl rfl⟩

end Cb
