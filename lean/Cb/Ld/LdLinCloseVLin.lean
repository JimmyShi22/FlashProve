-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseVLin.lean: the closing of the test for linear constraints in a batch, at the plan
without a splitting: the honest side.

Definitions, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseVLinProofs.lean.
The plan is Cb/Ld/LdLinClosePlan.lean's, its tests Cb/Ld/LdLinCloseDemand.lean's (`T : LdLinPlT p`),
its annotations Cb/Ld/LdBatchPlanLin.lean's (`T.QA`: the first test once by the shared part, the
second in every slot, then the rest), all unchanged. Here the same links get the honest side of a
batch (Cb/Ld/LdLinCloseVPlan.lean), from the joint at which the core ends (`P.V6`,
Cb/Ld/LdLinBHon.lean).

Limits: declared: a slot's own test on Ω uses Ω's pairs (message and encoding randomness); the tie
takes them from the shared part. So an instance's later messages may depend on the shared part's
coins: a choice of ours, as in Cb/Ld/LdLinBHon.lean, where a write-up of ours
(lean/CREDITS.md) is silent.
This file says nothing on plans with a splitting. Nothing on soundness. It does not say that the
hypotheses can be met together.

What the shared part holds in the closing up to where the rest (`QV'`) begins: what it holds after ζ
(`C.P.Sh6`): the index as sent, its full messages, the record, the shared point, G_u's family
(samples, words, pairs), the locations and folds read, Ω's family, ζ. No test changes it (so of the
step without rounds and the plan's two tests: `T.cZV`, `T.QV`; the honest side of the rest, `QV'`,
is a parameter).

Main names:
  `C.tieS s x y w`: the first test's rows have the targets and states that s gives; samples, words
    and pairs of the members of G_u's and Ω's families are those that s holds.
  `T.repX`, `T.repW`, `C.yrep`: a statement and a witness of the shared part's own, on which it runs
    the first test: the rows from s; the two shared families from s; all else (what a slot owns)
    from fixed values, which the test does not read, as all members of the first group are shared
    (`p.Shared`).
  tie': a parameter: the tie at the joint of what is left after the two tests. Demands on families
    of positions: Cb/Ld/LdLinCloseDemandV.lean's, from a bound b' on what the rest needs.
  `Spec.ldLinVL_tie`: the step without rounds carries `P.V6`'s tie to `C.tieS`.
  `Spec.ldLinVL_act`: under `p.Shared`, on tied statements the first test's acting part is that of
    the shared part's own statement: rows, members' pairs, members' words.
  `Spec.ldLinVL_plan`: under `p.Shared`, `same'`, `T.D₁.OK`, `T.D₂.OK`, `QV'.OK` and with a value of
    `(C.E₀.prod C.S.ext).Str`, `T.QV` is OK (every link a piece, annotations coherent, the empty
    family).
  `Spec.ldLinVL_all`: the closing meets all that the whole test asks of it on the honest side of a
    batch (`ldLinT_all`, Cb/Ld/LdLinBHonTop.lean): it stands behind every chain that ends at `P.V6`,
    its annotations are coherent, its last demand holds of the empty family; and its annotated links
    are `C.cZA (T.QA ..) T.fq`, its links `C.cZ T.Q T.fq`: the term of the sound side and of one
    instance;
      asked: ι nonempty; `p.Shared`; "restG is rest", "T.Q'.base says Ab"; the two tests' own
      hypotheses; the rest's annotated chain forgets to the rest's chain (`same'`); the rest's
      honest side is OK; tie' is carried from `P.V6`; a value of `(C.E₀.prod C.S.ext).Str`; qa
      allows what q₀ and ba allow; and the numbers: what the first test (once), the second (in every
      slot) and the rest need is at most what the senders bear: T.D₁.need (T.D₂.needV N .. b') ≤ ba,
      tW, tU, tO.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinCloseVPlan
import Cb.Ld.LdLinCloseVStep
import Cb.Ld.LdLinCloseDemandVProofs
import Cb.Ld.LdBatchPlanLin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (C : LdLinC E ι κ J Y)

/-- the shared part of the explicit part, read off what the shared part holds -/
def shS (s : C.P.Sh6) : C.Sh6 := (((s.1.1.1.1.1.2, s.1.1.1.1.2), s.1.1.2), s.2)

/-- The tie at the joint over the one signature. -/
def tieS {St' : Type} (s : C.P.Sh6) (x : (((C.B₁ → E) × (C.B₁ → C.Sh6)) × St') × C.S.Smp)
    (y : (C.E₀.prod C.S.ext).Str) (w : C.S.Wit × C.Wpa) : Prop :=
  x.1.1 = (C.tg₁ (C.shS s), fun _ => C.shS s) ∧
  (∀ a,
    x.2 (.inl (.inr a)) = s.1.1.1.2.1 a ∧
    y.2 (.inl (.inr a)) = s.1.1.1.2.2.1 a ∧
    w.1 (.inl (.inr a)) = s.1.1.1.2.2.2 a) ∧
  ∀ a, x.2 (.inr a) = s.1.2.1 a ∧ y.2 (.inr a) = s.1.2.2.1 a ∧ w.1 (.inr a) = s.1.2.2.2 a

/-- the words of the shared part's own statement; y₀: fixed values for what a slot owns -/
def yrep (y₀ : C.S.ext.Str) (s : C.P.Sh6) : C.S.ext.Str :=
  C.join4 (T := OMsg.Str) (fun i => y₀ (.inl (.inl (.inl i))))
    (fun i => y₀ (.inl (.inl (.inr i)))) s.1.1.1.2.2.1 s.1.2.2.1

end LdLinC

/-- the demand on families of positions at the joint of what is left after the two tests -/
def LdLinPl.qB₂ {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPl C) (N : ℕ)
    (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₂.O → ℕ) : QFam (C.E₀.prod p.S₂.ext) N :=
  p.S₂.qV (fun a => C.isSh a.1.1) (QFam.each q₀) b'

namespace LdLinPlT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPl C} (T : LdLinPlT p)

/-- the explicit part between the two tests (its last component, T.Q'.St: after them) -/
abbrev St₁ : Type := ((LinB₂ → E) × (LinB₂ → C.St6)) × T.Q'.St

/-- A statement and a witness of the shared part's own. x₀, and in `repW` `T.d₁`: fixed values for
what a slot owns. -/
def repX (x₀ : T.St₁ × C.S.Smp) (s : C.P.Sh6) : (((C.B₁ → E) × (C.B₁ → C.Sh6)) × T.St₁) × C.S.Smp :=
  (((C.tg₁ (C.shS s), fun _ => C.shS s), x₀.1),
    C.join4 (T := OMsg.Smp) (fun i => x₀.2 (.inl (.inl (.inl i))))
      (fun i => x₀.2 (.inl (.inl (.inr i)))) s.1.1.1.2.1 s.1.2.1)
def repW (s : C.P.Sh6) : C.S.Wit × C.Wpa :=
  (C.join4 (T := OMsg.Wit) (fun i => T.d₁.1 (.inl (.inl (.inl i))))
      (fun i => T.d₁.1 (.inl (.inl (.inr i)))) s.1.1.1.2.2.2 s.1.2.2.2,
    T.d₁.2)

variable (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₂.O → ℕ)
  (tie' : C.P.Sh6 → T.Q'.St × p.S₂.Smp → (C.E₀.prod p.S₂.ext).Str → p.S₂.Wit × C.Wpa → Prop)

/-- the demands on families of positions at the two joints before -/
def qB₁ : QFam (C.E₀.prod p.S₁.ext) N :=
  p.S₁.qV (fun a => C.isSh a.1) (QFam.each q₀) (T.D₂.needV N (fun a => C.isSh a.1) b')
def qB₀ : QFam (C.E₀.prod C.S.ext) N :=
  C.S.qV C.isSh (QFam.each q₀) (T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b'))

/-- the ties at the joint between the two tests and at the joint over the one signature -/
def tie₁ (s : C.P.Sh6) (x : T.St₁ × p.S₁.Smp)
    (y : (C.E₀.prod p.S₁.ext).Str) (w : p.S₁.Wit × C.Wpa) : Prop :=
  tie' s (T.D₂.outX x) (T.D₂.outY y) (T.D₂.outW w)
def tie₀ (s : C.P.Sh6) (x : (((C.B₁ → E) × (C.B₁ → C.Sh6)) × T.St₁) × C.S.Smp)
    (y : (C.E₀.prod C.S.ext).Str) (w : C.S.Wit × C.Wpa) : Prop :=
  C.tieS s x y w ∧ T.tie₁ tie' s (T.D₁.outX x) (T.D₁.outY y) (T.D₁.outW w)

variable (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)

/-- The honest side of the plan. -/
def QV (x₀ : T.St₁ × C.S.Smp)
    (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₂ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', p.qB₂ N q₀ b'⟩) :
    LdTcV N (T.QA cA' same') ⟨C.P.Sh6, T.tie₀ tie', T.qB₀ N q₀ b'⟩ :=
  LdTcV.consSh T.D₁ (LdTcA.consLo T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂') T.d₁ T.d₁'
    ⟨C.P.Sh6, T.tie₀ tie', T.qB₀ N q₀ b'⟩ C.P.Sh6 (T.tie₁ tie') (T.qB₁ N q₀ b')
    (fun s => (T.repX x₀ s, T.repW s)) id
    (LdTcV.consLo T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂' ⟨C.P.Sh6, T.tie₁ tie', T.qB₁ N q₀ b'⟩
      tie' (p.qB₂ N q₀ b') QV')

/-- The closing for a batch, with its honest side, from the joint at which the core ends. -/
def cZV (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (x₀ : T.St₁ × C.S.Smp)
    (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₂ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', p.qB₂ N q₀ b'⟩) :
    ChainV Unit N (C.P.V6 Sn qa N) QV'.VT :=
  C.cZV (T.QA cA' same') T.fq (C.P.V6 Sn qa N) (T.tie₀ tie')
    (T.qB₀ N q₀ b') (T.QV N q₀ b' tie' cA' same' x₀ QV')

end LdLinPlT

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The step without rounds carries the core's tie. -/
def ldLinVL_tie : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (St' : Type) (fa : C.Sta → St') (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (N : ℕ) (s : C.P.Sh6) (x : C.P.X6)
      (y : C.P.E5.Str) (w : C.P.W5),
    (C.P.V6 Sn qa N).tie s x y w → C.tieS s (C.fq fa (C.toSt x), C.toSmp x) (C.toE.map y) (C.toW w)

/-- Under the hypotheses below, on tied statements the first test's acting part is that of the
shared part's own statement. -/
def ldLinVL_act : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (x₀ : T.St₁ × C.S.Smp)
      (y₀ : C.S.ext.Str) (s : C.P.Sh6) (x : (((C.B₁ → E) × (C.B₁ → C.Sh6)) × T.St₁) × C.S.Smp)
      (y : (C.E₀.prod C.S.ext).Str) (w : C.S.Wit × C.Wpa),
    p.Shared → C.tieS s x y w →
    p.G₁.claims x.1.1 x.2 = p.G₁.claims (T.repX x₀ s).1.1 (T.repX x₀ s).2 ∧
    p.G₁.wit w.1 = p.G₁.wit (T.repW s).1 ∧
    ∀ a : p.G₁.A, y.2 a.1 = C.yrep y₀ s a.1

/-- Under the hypotheses below, the honest side of the plan is OK. -/
def ldLinVL_plan : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop)
      (b' : p.S₂.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₂.Smp → (C.E₀.prod p.S₂.ext).Str → p.S₂.Wit × C.Wpa → Prop)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)
      (x₀ : T.St₁ × C.S.Smp) (_ : (C.E₀.prod C.S.ext).Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₂ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', p.qB₂ N q₀ b'⟩),
    p.Shared → T.D₁.OK → T.D₂.OK → QV'.OK → (T.QV N q₀ b' tie' cA' same' x₀ QV').OK

/-- For ι nonempty and under the hypotheses below, the closing meets all that the whole test asks of
it on the honest side of a batch. -/
def ldLinVL_all : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop)
      (b' : p.S₂.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₂.Smp → (C.E₀.prod p.S₂.ext).Str → p.S₂.Wit × C.Wpa → Prop)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)
      (x₀ : T.St₁ × C.S.Smp) (_ : (C.E₀.prod C.S.ext).Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₂ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', p.qB₂ N q₀ b'⟩)
      (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (ba : C.Sa.O → ℕ),
    p.Shared →
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → QV'.OK →
    (∀ x y w, (C.P.V6 Sn qa N).rel x y w →
      tie' w.1 (T.D₂.outX (T.D₁.outX (T.fq (C.toSt x), C.toSmp x)))
        (T.D₂.outY (T.D₁.outY (C.toE.map y))) (T.D₂.outW (T.D₁.outW (C.toW w.2)))) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') (.inr a) ≤ Sn.tO a) →
    (∀ (Z : Joint Unit) (VZ : JV N Z) (c₀ : ChainV Unit N VZ (C.P.V6 Sn qa N)),
      (T.cZV N q₀ b' tie' cA' same' Sn qa x₀ QV').OkFromV c₀) ∧
    (T.cZV N q₀ b' tie' cA' same' Sn qa x₀ QV').forget.Coh ∧
    (∀ Jn, QV'.VT.q Jn fun _ => ∅) ∧
    (T.cZV N q₀ b' tie' cA' same' Sn qa x₀ QV').forget = C.cZA (T.QA cA' same') T.fq ∧
    (T.cZV N q₀ b' tie' cA' same' Sn qa x₀ QV').forget.forget = C.cZ T.Q T.fq

end
end Spec
end Cb
