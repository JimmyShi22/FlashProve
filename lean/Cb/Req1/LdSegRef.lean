-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRef.lean: the reference segment, with one group, as a term: its body from the parts'
lists of moves, its closing from the data of a closing.

This file puts a body and a closing together into one segment (a chain of interactive oracle
reductions), and states that the segment's hypotheses follow from those of its parts.
Definitions and a statement (`Cb.Spec.ldSegRef_hyp`); the proof is in Cb/Req1/LdSegRefProofs.lean.
Cb/Req1/LdSeg.lean states a segment over arbitrary lists of moves; Cb/Req1/LdSegRefBody.lean makes
the body a term, in the order of a table of a segment in a write-up of ours that is not in this
repository (front; read; range; digits; rows;
tensor); Cb/Req1/LdSegWhole.lean makes the four parts after the body from the data of a closing
(`segOne`).

Main names:
  `LdSegRef`: the data: Y (the body's data); the closing: the evader Z for the rows, the group,
    what is kept (kp), what is claimed of the kept messages (A₀c, over the explicit part St₁), the
    folded complex with its form and radius, the held messages (`LdFoldD`, `LdHeld`,
    Cb/Req1/LdSegKit.lean).
  `R.c1`: the closing's data (`LdCl1`, Cb/Req1/LdSegClose.lean), with the rows of the body as its
    rows.
  `R.seg`: the segment (tensor: the body's last part; hT: the body holds sendings, sub-protocols
    and steps only; l: the link bridge-to-fold, a parameter; Qc: the one sending and the
    locations).
  `Spec.ldSegRef_hyp`: `(R.seg ..).Hyp` from the parts' hypotheses and nothing else (beside whatever
    the arguments hold as proofs): `front.Hyp`; `Y.Hyp pp` (Cb/Req1/LdSegRefBody.lean; pp the
    characteristic of E); every link of the digits' lookup has all of the bundle but zero knowledge;
    `tensor.Hyp`; the evader's law; all named places lie in members of the group (a condition on
    places: by Cb/Req1/LdSegRefSupp.lean the rows then vanish outside the group at all states); the
    hypotheses of bridge-to-fold and of the one sending; hT (as for `R.seg`).
  So `Spec.ldSeg_goodB`, `Spec.ldSeg_into`, `Spec.ldSeg_nums` (Cb/Req1/LdSeg.lean) apply to
    `R.seg`. Kinds, what zero knowledge asks of the body, beside its hypotheses, its numbers:
    Cb/Req1/LdSegRefBody.lean.

Limits: this file says nothing on two groups. It does not say that all hypotheses can be met
together.
The order of the parts restates a table of a segment in a write-up of ours that is not in this
repository, with its errata, in our own words (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefBody
import Cb.Req1.LdSegRefSupp
import Cb.Req1.LdSegWhole
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- The reference segment with one group: the data. -/
structure LdSegRef (E Kc : Type) [Field E] [Fintype E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Y   : LdBodyD E Kc E₀ Wp
  /-- the closing -/
  Z   : Evader E Y.G.B
  grp : Grp Y.G.Q.T
  kp  : Y.G.Q.T.O → Prop
  [decKp : DecidablePred kp]
  St₁ : Type
  A₀c : IOR.Rels Kc St₁ E₀ ((Y.G.Q.T.sub kp).Msg × Wp)
  Pf  : Type
  [finPf : Fintype Pf]
  Cf  : LdCode E Pf
  Stf : Type
  slf : Slf E Stf Cf.J
  e   : ℕ
  cl  : {o // kp o} → Prop
  [decCl : DecidablePred cl]
  sW  : ∀ k : {a // cl a}, Cf.Word → (Y.G.Q.T.om k.1.1).C.Word
  sJ  : ∀ k : {a // cl a}, (Y.G.Q.T.om k.1.1).C.J → Cf.J
  sQ  : ∀ k : {a // cl a}, (Y.G.Q.T.om k.1.1).C.Q → Cf.Q

attribute [instance] LdSegRef.decKp LdSegRef.finPf LdSegRef.decCl

namespace LdSegRef
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (R : LdSegRef E Kc E₀ Wp)

/-- The closing's data, with the rows of the body. -/
@[reducible] def c1 : LdCl1 E Kc :=
  { S := R.Y.G.Q.T, B := R.Y.G.B, Sb := fun _ => R.Y.G.Sx, sl := R.Y.G.sl, Z := R.Z, G := R.grp,
    kp := R.kp, St₀ := R.St₁, Wp := Wp, E₀ := E₀, A₀ := R.A₀c, Pf := R.Pf, Cf := R.Cf, Stf := R.Stf,
    slf := R.slf, e := R.e, cl := R.cl, sW := R.sW, sJ := R.sJ, sQ := R.sQ }

/-- The segment. -/
def seg (tensor : LdProg R.Y.tgt R.c1.bat.src)
    (hT : (R.Y.body R.c1.bat.src tensor).All fun t => t = .send ∨ t = .sub ∨ t = .step)
    (l : IOR.Link Kc R.c1.fold.src.J R.c1.fold.mid) (Qc : LdCloseD R.c1.fold) :
    LdSeg R.Y.a Qc.loc.tgt :=
  segOne R.c1 (R.Y.body R.c1.bat.src tensor) hT l Qc

end LdSegRef

namespace Spec
open IOR

/-- The reference segment's hypotheses, from the parts'. -/
def ldSegRef_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp]
      (R : LdSegRef E Kc E₀ Wp) (tensor : LdProg R.Y.tgt R.c1.bat.src)
      (hT : (R.Y.body R.c1.bat.src tensor).All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc R.c1.fold.src.J R.c1.fold.mid) (Qc : LdCloseD R.c1.fold),
    R.Y.front.Hyp → R.Y.Hyp pp → R.Y.lk.AllB → tensor.Hyp → R.Z.OK →
    (∀ n, R.Y.G.Named n → R.grp.mem n.1) → R.c1.fold.Hyp l → Qc.snd.Hyp → (R.seg tensor hT l Qc).Hyp

end Spec
end Cb
