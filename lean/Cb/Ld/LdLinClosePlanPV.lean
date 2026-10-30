-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanPV.lean: the write-up's plan of the closing of the test for linear
constraints, for a batch: the honest side.

In standard terms: the conditions on the honest prover's strategy in an interactive oracle proof
that proves at most N instances at once, where one part of the prover acts for all instances.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanPVProofs.lean.
It uses Cb/Ld/LdLinClosePlanP.lean, Cb/Ld/LdLinCloseDemandP.lean (the plan; its three tests),
Cb/Ld/LdLinClosePlanPB.lean (`T.QA`: the plan for a batch: the front and the first two tests once,
by the shared part; the third test in every slot; then the rest (cA', a parameter)),
Cb/Ld/LdFrontOn.lean (a front with one splitting by the shared part), Cb/Ld/LdAltB.lean,
Cb/Ld/LdLinCloseVPlan.lean, Cb/Ld/LdLinStdSpV.lean (what the shared part reads; under the hypotheses
of `Spec.ldSpV_fresh`, the mask is fresh). The pattern is that of Cb/Ld/LdLinCloseVLin.lean (the
plan without a splitting).
The shared witness is `C.P.Sh6` up to where the rest (`QV'`, a parameter) begins: what the shared
part holds at the end of the core: the encoded index, the table of full messages of the index, the
record, the shared point, G_u's family, the locations, Ω's family (the mask's holder in it), ζ
(exactly: `LdLinP.Sh6`, Cb/Ld/LdLinBHon.lean). That the holder is in Ω's family is asked in
`Spec.ldLinPV_std`; under `p.Plain` alone it is in one of the two families.
The honest side adds at each joint (`IOR.JV`, Cb/Ld/LdLinChainV.lean) a shared witness, a tie of
each slot's statement and witness to it, and a demand on families of positions (`QFam`,
Ior/LinkVBears.lean). It is OK (`LdTcV.OK`, Cb/Ld/LdLinCloseVPlan.lean) if every link is a piece
(`LinkV.PV`, Cb/Ld/LdLinChainV.lean; `PieceV`, Ior/LinkVBears.lean), the annotations are coherent,
and the last demand holds of the empty family.

Main names:
  `T.sg s`: the splitting's scalar, a function of the shared witness alone.
  `T.rd`: what the shared part reads at the splitting (`C.rdV` at `p.Rs₀`; public part: target 0 and
    the shared part of the explicit part, twice).
  `T.qB₀` to `T.qB₃`: the demands on families of positions at the four joints: a shared oracle
    message in the instance's group bears N times the third test's positions. The front keeps the
    demand.
  `T.tieF`, `T.tie₁`, `T.tie₂`, `T.tie₃`: the shared tests' claims are `T.cl₁ s`, `T.cl₂ s`;
    samples, words and pairs of the shared oracle messages are those that s holds; then the next
    tie.
  `T.rep₁`, `T.rep₂`: a statement and a witness of the shared part's own for each shared test (fixed
    values for what a slot owns).
  `Spec.ldLinPV_tie`: the step without rounds carries the core's tie to `T.tieF` (from `p.Shared`,
    `p.Plain`: here `p.Plain.rsSh` is read), if tie' holds of what the three tests hand on.
  `Spec.ldLinPV_plan`: the three tests and the rest: every link is a piece (all of `LdTcV.OK`), for
    an annotated chain cA' whose links are those of `T.Q'.c` (`same'`), from `p.Shared`, the three
    tests' own hypotheses (`T.D₁.OK`, `T.D₂.OK`, `T.D₃.OK`) and `QV'.OK`.
  `Spec.ldLinPV_all`: under the hypotheses of its statement, the closing meets the three conditions
    that the whole test asks of its closing on the honest side of a batch (Cb/Ld/LdLinBHonTop.lean),
    behind the core, its annotated links are those of `C.cZA (T.QA ..) ..`
    (Cb/Ld/LdBatchBlocksPlan.lean: the step without rounds, then those of `T.QA`), and its links
    those of `C.cZ (T.QA ..).Q ..`; one hypothesis on masks: κ is fresh for sets of slots after
    (core ; step).
  `Spec.ldLinPV_std`: under the hypotheses of its statement, at the standard senders: no hypothesis
    on a fresh mask (Cb/Ld/LdLinStdSpV.lean: `ldSpV_fresh`): κ a free entry of a member of Ω's
    family; `p.Rs₀` holds no pad entry of Ω's family.

Limits:
The arguments without a name in `Spec.ldLinPV_plan`, `Spec.ldLinPV_all`, `Spec.ldLinPV_std`
((_ : C.E₀.Str), (_ : C.Sh6), (_ : C.P.X4), (_ : C.P.E4.Str)) are inhabitants only: they say that
these types are not empty; no clause reads them. (Cb/Ld/LdLinCloseVLin.lean has the same;
Cb/Ld/LdLinChainVFresh.lean writes such arguments _x₄, _y₄.)
This file says nothing on an instance that has failed (the write-up: it sends fixed
messages, the shared messages stay as prescribed); "for sets of slots" is the notion of
Cb/Ld/LdLinBHonTop.lean.
This file says nothing on soundness (Cb/Ld/LdLinClosePlanPB.lean), nothing on what closes the rest
(QV' is a parameter with its own condition and its tie tie'), and nothing on the two items of the
object's list (Cb/Obj/LdObjectPaperBatch.lean). That these conditions can be met together is not
said here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinClosePlanPB
import Cb.Ld.LdLinCloseVLin
import Cb.Ld.LdLinStdSpV
import Cb.Ld.LdAltB
import Cb.Ld.LdFrontOnProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (C : LdLinC E ι κ J Y)

/-- samples and pairs of the shared part's own statement and witness; x₀, d: fixed values for what a
slot owns -/
def smpS (x₀ : C.S.Smp) (s : C.P.Sh6) : C.S.Smp :=
  C.join4 (T := OMsg.Smp) (fun i => x₀ (.inl (.inl (.inl i))))
    (fun i => x₀ (.inl (.inl (.inr i)))) s.1.1.1.2.1 s.1.2.1
def witS (d : C.S.Wit) (s : C.P.Sh6) : C.S.Wit :=
  C.join4 (T := OMsg.Wit) (fun i => d (.inl (.inl (.inl i))))
    (fun i => d (.inl (.inl (.inr i)))) s.1.1.1.2.2.2 s.1.2.2.2

/-- the shared part of the explicit part, off the arguments of the public part -/
def shP (z : C.P.Sh4 × C.NO.Smp × (Fin C.D.l → E)) : C.Sh6 :=
  (((z.1.1.1.1.2, z.1.1.1.2), z.1.2), z.2.2)

end LdLinC

namespace LdLinPpT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p)

/-- the explicit parts in front of the third, the second, the first test -/
abbrev StC : Type := ((LinB₂ → E) × (LinB₂ → C.St6)) × T.Q'.St
abbrev StB : Type := ((Unit → E) × (Unit → C.Sh6)) × T.StC
abbrev StA : Type := ((C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) × T.StB

/-- The scalar of the splitting, off the shared witness; the claims of the two shared tests -/
def sg (_ : LdLinPpT p) (s : C.P.Sh6) : E := splitVal p.k₀ p.fO (C.shMsg s) (C.shS s)
def cl₁ (s : C.P.Sh6) : (C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6) :=
  (Sum.elim (C.tgRC (C.shS s)) fun _ => 0 - T.sg s, Sum.elim (fun _ => C.shS s) fun _ => C.shS s)
def cl₂ (s : C.P.Sh6) : (Unit → E) × (Unit → C.Sh6) := oneClaim (T.sg s, C.shS s)

variable (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₃.O → ℕ)
  (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)

/-- the demands on families of positions at the four joints -/
def qB₃ (_ : LdLinPpT p) : QFam (C.E₀.prod p.S₃.ext) N :=
  p.S₃.qV (fun a => C.isSh a.1.1.1) (QFam.each q₀) b'
def qB₂ : QFam (C.E₀.prod p.S₂.ext) N :=
  p.S₂.qV (fun a => C.isSh a.1.1) (QFam.each q₀) (T.D₃.needV N (fun a => C.isSh a.1.1) b')
def qB₁ : QFam (C.E₀.prod p.S₁.ext) N :=
  p.S₁.qV (fun a => C.isSh a.1) (QFam.each q₀) (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b'))
def qB₀ : QFam (C.E₀.prod C.S.ext) N :=
  C.S.qV C.isSh (QFam.each q₀) (T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')))

variable (x₀ : C.S.Smp) (y₀ : C.S.ext.Str)

/-- The ties in front of the third, the second, the first test, and at the start of the front -/
def tie₃ (s : C.P.Sh6) (x : T.StC × p.S₂.Smp)
    (y : (C.E₀.prod p.S₂.ext).Str) (w : p.S₂.Wit × C.Wpa) : Prop :=
  tie' s (T.D₃.outX x) (T.D₃.outY y) (T.D₃.outW w)
def tie₂ (s : C.P.Sh6) (x : T.StB × p.S₁.Smp)
    (y : (C.E₀.prod p.S₁.ext).Str) (w : p.S₁.Wit × C.Wpa) : Prop :=
  (x.1.1 = T.cl₂ s ∧
    ∀ o : p.S₁.O, C.isSh o.1 →
      x.2 o = C.smpS x₀ s o.1 ∧ y.2 o = C.yrep y₀ s o.1 ∧ w.1 o = C.witS T.d₁.1 s o.1) ∧
  T.tie₃ tie' s (T.D₂.outX x) (T.D₂.outY y) (T.D₂.outW w)
def tie₁ (s : C.P.Sh6) (x : T.StA × C.S.Smp) (y : (C.E₀.prod C.S.ext).Str) (w : C.S.Wit × C.Wpa) :
    Prop :=
  (x.1.1 = T.cl₁ s ∧
    ∀ o : C.S.O,
      C.isSh o → x.2 o = C.smpS x₀ s o ∧ y.2 o = C.yrep y₀ s o ∧ w.1 o = C.witS T.d₁.1 s o) ∧
  T.tie₂ tie' x₀ y₀ s (T.D₁.outX x) (T.D₁.outY y) (T.D₁.outW w)

/-- each row goes to its test -/
def fF (s : ((E × C.Sh6) × (E × C.Sh6)) × (((C.Brc → E) × (C.Brc → C.Sh6)) × T.StC)) : T.StA :=
  ((Sum.elim s.2.1.1 fun _ => s.1.2.1, Sum.elim s.2.1.2 fun _ => s.1.2.2), (oneClaim s.1.1, s.2.2))

/-- what the shared part reads at the splitting -/
def rd (_ : LdLinPpT p) : C.P.Sh6 → C.S.Msg × (E × (C.Sh6 × C.Sh6)) :=
  C.rdV p.Rs₀ fun z => (0, (C.shP z, C.shP z))

def tieF (s : C.P.Sh6)
    (x : ((E × (C.Sh6 × C.Sh6)) × (((C.Brc → E) × (C.Brc → C.Sh6)) × T.StC)) × C.S.Smp)
    (y : (C.E₀.prod C.S.ext).Str) (w : C.S.Wit × C.Wpa) : Prop :=
  ((T.rd s).1 = C.S.cut p.Rs₀ (C.S.msgs w.1) ∧ (T.rd s).2 = x.1.1) ∧
  T.tie₁ tie' x₀ y₀ s
    (T.fF (splitNx C.S C.Sh6 C.Sh6 _ x (splitVal p.k₀ p.fO (C.S.msgs w.1) x.1.1.2.1)).1, x.2)
    ((sideG C.S (ExtMap.id C.E₀)).map y) w

/-- Statements and witnesses of the shared part's own for the two shared tests; xB, xC: fixed values
-/
def rep₁ (xB : T.StB) (s : C.P.Sh6) :
    ((((C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) × T.StB) × C.S.Smp) × (C.S.Wit × C.Wpa) :=
  (((T.cl₁ s, xB), C.smpS x₀ s), (C.witS T.d₁.1 s, T.d₁.2))
def rep₂ (xC : T.StC) (s : C.P.Sh6) :
    ((((Unit → E) × (Unit → C.Sh6)) × T.StC) × p.S₁.Smp) × (p.S₁.Wit × C.Wpa) :=
  (((T.cl₂ s, xC), C.S.res (T := OMsg.Smp) p.kp₁ (C.smpS x₀ s)),
    (C.S.res (T := OMsg.Wit) p.kp₁ (C.witS T.d₁.1 s), T.d₁.2))

variable (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)

/-- The honest side of the three tests and the rest. -/
def QVt (xB : T.StB) (xC : T.StC)
    (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩) :
    LdTcV N (LdTcA.consSh T.D₁
        (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁')
      ⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ :=
  LdTcV.consSh T.D₁ (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂')
    T.d₁ T.d₁' ⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ C.P.Sh6 (T.tie₂ tie' x₀ y₀)
    (T.qB₁ N q₀ b') (T.rep₁ x₀ xB) id
    (LdTcV.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂'
      ⟨C.P.Sh6, T.tie₂ tie' x₀ y₀, T.qB₁ N q₀ b'⟩ C.P.Sh6 (T.tie₃ tie')
      (T.qB₂ N q₀ b') (T.rep₂ x₀ xC) id
      (LdTcV.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃' ⟨C.P.Sh6, T.tie₃ tie', T.qB₂ N q₀ b'⟩
        tie' (T.qB₃ N q₀ b') QV'))

/-- The front's chain with honest sides. -/
def cVf :
    ChainV Unit N (⟨C.P.Sh6, T.tieF tie' x₀ y₀, T.qB₀ N q₀ b'⟩ : JV N (p.x₁ T.Q'.base).stage.J)
      (⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ : JV N (C.S.jointCf T.Q.base)) :=
  Front.onV p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ T.Q'.base)
    p.Rs₀ inferInstance ⟨_, p.base₁ T.Q'.base⟩ T.fF N C.P.Sh6
    (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b') T.rd (T.tie₁ tie' x₀ y₀)


/-- The honest side of the plan. -/
def QV (xB : T.StB) (xC : T.StC)
    (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩) :
    LdTcV N (T.QA cA' same') ⟨C.P.Sh6, T.tieF tie' x₀ y₀, T.qB₀ N q₀ b'⟩ :=
  LdTcV.front (p.x₁ T.Q'.base)
    (LdTcA.consSh T.D₁
      (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁')
    T.front (T.front.cA true) (frontB_forget E _ _ _ _ _ T.front true)
    ⟨C.P.Sh6, T.tieF tie' x₀ y₀, T.qB₀ N q₀ b'⟩
    ⟨C.P.Sh6, T.tie₁ tie' x₀ y₀, T.qB₀ N q₀ b'⟩ (T.cVf N q₀ b' tie' x₀ y₀)
    (frontOn_forget E C.S C.E₀ C.Wpa p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ T.Q'.base)
      p.Rs₀ inferInstance ⟨_, p.base₁ T.Q'.base⟩ T.fF N C.P.Sh6 (T.tieF tie' x₀ y₀)
      (T.qB₀ N q₀ b') T.rd (T.tie₁ tie' x₀ y₀))
    (T.QVt N q₀ b' tie' x₀ y₀ cA' same' xB xC QV')

/-- The closing for a batch, with its honest side, from the joint at which the core ends. -/
def cZV (xB : T.StB) (xC : T.StC) (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop)
    (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩) :
    ChainV Unit N (C.P.V6 Sn qa N) QV'.VT :=
  C.cZV (T.QA cA' same') (C.fqP T.fa) (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b')
    (T.QV N q₀ b' tie' x₀ y₀ cA' same' xB xC QV')

end LdLinPpT

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States, under the premises below: the step without rounds carries the core's tie to the start of
the front. -/
def ldLinPV_tie : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
      (x₀ : C.S.Smp) (y₀ : C.S.ext.Str) (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (N : ℕ)
      (s : C.P.Sh6) (x : C.P.X6) (y : C.P.E5.Str) (w : C.P.W5),
    p.Shared → p.Plain → (C.P.V6 Sn qa N).tie s x y w →
    tie' s (T.fa (C.toSt x).1.1.1.1,
        p.S₂.res (T := OMsg.Smp) p.kp₃
          (p.S₁.res (T := OMsg.Smp) p.kp₂ (C.S.res (T := OMsg.Smp) p.kp₁ (C.toSmp x))))
      (T.D₃.outY (T.D₂.outY (T.D₁.outY (C.toE.map y))))
      (T.D₃.outW (T.D₂.outW (T.D₁.outW (C.toW w)))) →
    T.tieF tie' x₀ y₀ s (C.fqP T.fa (C.toSt x), C.toSmp x) (C.toE.map y) (C.toW w)

/-- States, under the premises below: the honest side of the three tests and the rest is OK. -/
def ldLinPV_plan : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop)
      (b' : p.S₃.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
      (x₀ : C.S.Smp) (y₀ : C.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (_ : C.E₀.Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩),
    p.Shared → T.D₁.OK → T.D₂.OK → T.D₃.OK → QV'.OK →
    (T.QVt N q₀ b' tie' x₀ y₀ cA' same' xB xC QV').OK

/-- States, under the premises below: the closing meets all that the whole test asks of it on the
honest side of a batch. -/
def ldLinPV_all : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop)
      (b' : p.S₃.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
      (x₀ : C.S.Smp) (y₀ : C.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (_ : C.E₀.Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩)
      (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (ba : C.Sa.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (_ : C.Sh6),
    p.Shared → p.Plain → p.Kept →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.D₃.OK → QV'.OK →
    (∀ x y w, (C.P.V6 Sn qa N).rel x y w →
      tie' w.1 (T.fa (C.toSt x).1.1.1.1,
          p.S₂.res (T := OMsg.Smp) p.kp₃
            (p.S₁.res (T := OMsg.Smp) p.kp₂ (C.S.res (T := OMsg.Smp) p.kp₁ (C.toSmp x))))
        (T.D₃.outY (T.D₂.outY (T.D₁.outY (C.toE.map y))))
        (T.D₃.outW (T.D₂.outW (T.D₁.outW (C.toW w.2))))) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inl (.inl a))) ≤
      ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inl (.inr a))) ≤
      Sn.tW a) →
    (∀ a,
      T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inr a) ≤ Sn.tO a) →
    ((C.P.chainV Sn qa N on0 εf).snoc
        ((C.link (C.fqP T.fa) (p.x₁ T.Q'.base).A).loV
          N (C.P.V6 Sn qa N) (T.tieF tie' x₀ y₀) (T.qB₀ N q₀ b'))).FreshForV
      T.rd (fun _ => ()) E (fun u κ' => (p.k₀.put u κ'.1, κ'.2)) Unit (fun _ κ' => κ') →
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').OkFromV (C.P.chainV Sn qa N on0 εf) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').forget.Coh ∧
    (∀ Jn, QV'.VT.q Jn fun _ => ∅) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').forget =
      C.cZA (T.QA cA' same') (C.fqP T.fa) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').forget.forget =
      C.cZ (T.QA cA' same').Q (C.fqP T.fa)

end
end Spec

/-- States, under the premises below, the same at the standard senders: no hypothesis on a fresh
mask. -/
def Spec.ldLinPV_std (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop)
      (b' : p.S₃.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
      (x₀ : C.S.Smp) (y₀ : C.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (_ : C.E₀.Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩)
      (Ts : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ) (LO : C.P.NO.O → ℕ)
      (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ) (n₀ : Σ a, Ts.YO.Fr a)
      (qa : Finset C.P.Ea.Pos → Prop) (ba : C.Sa.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (_ : C.Sh6) (_ : C.P.X4)
      (_ : C.P.E4.Str),
    p.Shared → p.Plain → p.Kept →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.D₃.OK → QV'.OK →
    (∀ x y w, (C.P.V6 (Ts.snd LW LU LO tW tU tO) qa N).rel x y w →
      tie' w.1 (T.fa (C.toSt x).1.1.1.1,
          p.S₂.res (T := OMsg.Smp) p.kp₃
            (p.S₁.res (T := OMsg.Smp) p.kp₂ (C.S.res (T := OMsg.Smp) p.kp₁ (C.toSmp x))))
        (T.D₃.outY (T.D₂.outY (T.D₁.outY (C.toE.map y))))
        (T.D₃.outW (T.D₂.outW (T.D₁.outW (C.toW w.2))))) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inl (.inl a))) ≤
      ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inl (.inr a))) ≤
      tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inl (.inr a)) ≤ tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) (.inr a) ≤ tO a) →
    Ts.Places → Ts.YW.OK tW → Ts.YU.OK tU → Ts.YO.OK tO →
    (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) = C.eO (Ts.YO.entF n₀) → (∀ n, p.Rs₀ (C.eO n) → Ts.YO.NoPad n) →
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV').OkFromV
      (C.P.chainV (Ts.snd LW LU LO tW tU tO) qa N on0 εf) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV').forget.Coh ∧
    (∀ Jn, QV'.VT.q Jn fun _ => ∅) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV').forget =
      C.cZA (T.QA cA' same') (C.fqP T.fa) ∧
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV').forget.forget =
      C.cZ (T.QA cA' same').Q (C.fqP T.fa)

end Cb
