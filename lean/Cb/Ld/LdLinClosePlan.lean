-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlan.lean: book-keeping for the last part of an interactive oracle proof. The linear
constraints (rows) that the test for linear constraints leaves open are arranged as the inputs of
two proximity tests, each on a group of oracles (the plan without a splitting).
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanProofs.lean.
It uses Cb/Ld/LdLinClosePre.lean (`LdLinC`: the test over a signature), Cb/Ld/LdLinCloseForms.lean
(`Slf.push`: coefficients on some entries of a vector as a form; `Grp.onMem`: a form on a member's
message as a form on a group's) and Cb/Ld/LdBatSig.lean (`Grp`).
W, G_u and Ω are the test's oracle messages that hold the vectors w, u and ω (`C.nW`, `C.nU`,
`C.nO`, Cb/Ld/LdLinClosePre.lean); Ab is the base joint that a preamble leaves (`C.Ab`).
The five kinds of rows that the test leaves: `C.RowsM`; "rest": `C.rest`, a function of the state
and of `C.Sa`'s messages (both Cb/Ld/LdLinClosePre.lean).
A base joint (`IOR.Rels`, Ior/Chain.lean) has an exact relation, for the honest side, a relaxed one,
of which knowledge soundness speaks, a condition on statements, and a core (`core`; in this file
with values in `Unit`: it says nothing here). Bq says the rows and Ab (`C.Says Bq fq`) if three
things hold: the rows and Ab's exact relation give Bq's exact relation; where Ab's condition holds,
Bq's relaxed relation gives the rows and Ab's relaxed relation; and there Bq's condition holds too.

This is not the plan of a write-up of ours (lean/CREDITS.md; that is
Cb/Ld/LdLinClosePlanP.lean): the write-up names one code for Ω and W and one for G_u, never
puts G_u and Ω into one group, and always splits the fold's row. This plan serves data in which all
three can be read together. Its second group and that group's two rows are the write-up's
instance group and rows (there: exactly Ω, W and the message of index masks; here the group may hold
more).

The plan. One instance. The codes of G_u and Ω can be read under one common reading, and so can
those of Ω and W: no row has to be split.
  First group G₁: a group of `C.S` that holds G_u and Ω (and whatever else). Its rows are the
    record's rows and the columns at the locations, on u, and the fold's row, on (ω, u): what all
    instances share.
  Second group G₂: a group of the kept oracle messages (`kp₁`) that holds Ω and W (and whatever
    "rest" reads: the instance's message of index masks). Its rows are the evaluation, on (w, rest),
    and the inner product, on (ω, w). They are the instance's own: its rows on Ω stand here, not in
    the first group.
  At its bridge what B' reads is kept (kp₂, a parameter). A member of G₂ that nothing reads later
    (the instance's message of index masks) is closed by this test and leaves here.
  Then comes whatever closes the rest: a base joint B', on the messages kept, that says Ab.
  Ω is a member of both groups; each test takes in its sample rows (Cb/Ld/LdBatSig.lean, by
  construction).

Main names:
  `restG` (a field of `LdLinPl C`): a form on the second group's message, meant for "rest"; no field
    asks that it is "rest": that is a premise of `Spec.ldLinPlan_rows₂` and `Spec.ldLinPlan_says`.
  `C.B₁`, `p.sl₁`, `C.tg₁`; `LinB₂`, `p.sl₂`, `C.tg₂`: names, forms and public targets of the rows
    on the two groups. The state of the rows on the first group is the part of the explicit part
    that all instances share (`C.Sh6`, `C.sh st`): they do not read the instance's own state. That
    of the rows on the second group is the whole explicit part without the samples (`C.St6`:
    (((state of the preamble, record), shared point), locations and folds read), ζ).
  `p.base B'`: the base joint, in the form in which tests on groups in a row take it.
  `Spec.ldLinPlan_rows₁`: the rows on G₁ hold if and only if the record's row, the columns and the
    fold's row do. `Spec.ldLinPlan_rows₂`: where `restG` is "rest", those on G₂ hold if and only if
    the evaluation and the inner product do.
  `Spec.ldLinPlan_says`: if `restG` is "rest" and B' says Ab, then `p.base B'` says the rows and Ab
    (Cb/Ld/LdLinClosePre.lean). So the step of that file leads from the test's last joint to
    `C.S.over (p.base B')`.

Limits: this file says nothing on the batch, but for `p.Shared`, which is defined for a batch and
asked by nothing here, and for `C.Sh6` and `C.sh`, the part of the explicit part that all instances
share. It says nothing on the tests themselves. This file says nothing on the plans with a
splitting. In one of them G_u's and Ω's codes differ: the fold's row is split under the shared
mask-only message: the write-up's plan. In another W's and Ω's differ too: the inner product
is split under a message of the instance's: wider than the write-up's; this wider plan is
ours.
The rows and the second group restate, in our own words, the write-up (lean/CREDITS.md); the
first group (G_u and Ω together, no splitting) does not.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinClosePre
import Cb.Ld.LdLinCloseForms

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- the sum of two forms with one state -/
def Slf.plus {E St J : Type} [Add E] (s₁ s₂ : Slf E St J) : Slf E St J := fun st j =>
  s₁ st j + s₂ st j

/-- the names of the rows on the second group: the evaluation, the inner product -/
abbrev LinB₂ : Type := Unit ⊕ Unit

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y)

/-- the names of the rows on the first group (the record's rows, the columns, the fold's row) -/
abbrev B₁ : Type := (C.D.X.Z.S ⊕ Fin C.t) ⊕ Unit

/-- the part of the explicit part that all instances share: ((record, shared point), locations and
folds read), ζ -/
abbrev Sh6 : Type := ((C.D.X.Rec × C.D.Pt) × ((Fin C.t → ι) × (Fin C.t → E))) × (Fin C.D.l → E)
def sh (st : C.St6) : C.Sh6 := (((st.1.1.1.2, st.1.1.2), st.1.2), st.2)

/-- the targets: the folded answers; the folds of the columns read; 0 -/
def tg₁ (s : C.Sh6) : C.B₁ → E
  | .inl (.inl z) => C.D.X.tgt s.1.1.1 s.1.1.2.1 z
  | .inl (.inr i) => s.1.2.2 i
  | .inr _ => 0

/-- the target of the tensor row; 0 -/
def tg₂ (st : C.St6) : LinB₂ → E
  | .inl _ => C.τ st.1.1.1.1
  | .inr _ => 0

/-- the explicit part: (targets and states of the first rows, (those of the second, fa (state of the
preamble))) -/
def fq {St' : Type} (fa : C.Sta → St') (st : C.St6) :
    ((C.B₁ → E) × (C.B₁ → C.Sh6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St') :=
  ((C.tg₁ (C.sh st), fun _ => C.sh st), ((C.tg₂ st, fun _ => st), fa st.1.1.1.1))

end LdLinC

/-- The plan without a splitting: the data. -/
structure LdLinPl {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) where
  /-- the first group holds G_u and Ω -/
  G₁  : Grp C.S
  hU  : G₁.mem C.nU
  hO  : G₁.mem C.nO
  /-- kept at its bridge: W, Ω, and whatever else is read later -/
  kp₁ : C.S.O → Prop
  [decKp₁ : DecidablePred kp₁]
  kW  : kp₁ C.nW
  kO  : kp₁ C.nO
  /-- the second group holds Ω and W -/
  G₂  : Grp (C.S.sub kp₁)
  hW₂ : G₂.mem ⟨C.nW, kW⟩
  hO₂ : G₂.mem ⟨C.nO, kO⟩
  /-- kept at its bridge: whatever is read later -/
  kp₂ : (C.S.sub kp₁).O → Prop
  [decKp₂ : DecidablePred kp₂]
  /-- "rest", as a form on the second group's message -/
  restG : Slf E C.Sta G₂.C.J

attribute [instance] LdLinPl.decKp₁ LdLinPl.decKp₂

namespace LdLinPl
variable {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPl C)

/-- the oracle messages after the first, after the second bridge -/
abbrev S₁ : Sig E := C.S.sub p.kp₁
abbrev S₂ : Sig E := p.S₁.sub p.kp₂

variable [Fintype Y] [Fintype κ] [Fintype J]

/-- The rows on the first group: the record's rows; the columns at the locations; the fold's row. -/
def sl₁ : ∀ _ : C.B₁, Slf E C.Sh6 p.G₁.C.J
  | .inl (.inl z) =>
    p.G₁.onMem C.nU p.hU
      (Slf.push (fun j => C.lU (C.D.X.pl j)) fun s j => C.D.X.Z.mat s.1.1.1.1 z j)
  | .inl (.inr i) => p.G₁.onMem C.nU p.hU (Slf.push C.lU fun s k => C.D.X.G (s.1.2.1 i) k)
  | .inr _ =>
    (p.G₁.onMem C.nO p.hO (Slf.push C.lO fun s y => Alg.eqk s.2 (C.D.py y))).sub
      (p.G₁.onMem C.nU p.hU
        (Slf.push (fun n : Y × (Fin C.D.klo → Bool) => C.lU (C.D.X.pl (C.D.lay n)))
          fun s n => Alg.eqk s.2 (C.D.py n.1) * Alg.eqk s.1.1.2.2 n.2))

/-- The rows on the second group: the evaluation; the inner product. -/
def sl₂ : ∀ _ : LinB₂, Slf E C.St6 p.G₂.C.J
  | .inl _ =>
    (p.G₂.onMem ⟨C.nW, p.kW⟩ p.hW₂
        (Slf.push C.lW fun st c => Alg.eqk (C.D.pt (C.ψ st.1.1.1.1)) c)).plus
      fun st => p.restG st.1.1.1.1
  | .inr _ =>
    (p.G₂.onMem ⟨C.nO, p.kO⟩ p.hO₂ (Slf.push C.lO fun st y => C.g st.1.1.1.1 y)).sub
      (p.G₂.onMem ⟨C.nW, p.kW⟩ p.hW₂ (Slf.push C.lW fun st c => Alg.eqk (C.D.pt st.1.1.2) c))

/-- The base joint: rows on G₁; of the kept messages: rows on G₂; of the messages kept then: B'. -/
abbrev base {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₂.Msg × C.Wpa)) :
    IOR.Rels Unit (((C.B₁ → E) × (C.B₁ → C.Sh6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St'))
      C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.sl₁ x (p.G₁.msg m))
    (onMsgRels (C.S.res (T := OMsg.Msg) p.kp₁)
      (claimRels (fun x m => Slf.All p.sl₂ x (p.G₂.msg m))
        (onMsgRels (p.S₁.res (T := OMsg.Msg) p.kp₂) B')))

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- every member of the first group is an oracle message that all instances share: one of those sent
with G_u or with Ω (asked by nothing here; for a batch) -/
def Shared : Prop := ∀ o, p.G₁.mem o → (∃ a, o = .inl (.inr a)) ∨ ∃ a, o = .inr a

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- the messages that are kept to the end -/
def last (m : C.S.Msg) : p.S₂.Msg :=
  p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- B' says Ab. -/
structure SaysA {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₂.Msg × C.Wpa)) (fa : C.Sta → St') :
    Prop where
  fwd : ∀ sa y m wp, C.Ab.rel sa y (C.aM m, wp) → B'.rel (fa sa) y (p.last m, wp)
  bwd : ∀ sa y m wp,
    C.Ab.on (sa, y) → B'.relR (fa sa, y) (p.last m, wp) → C.Ab.relR (sa, y) (C.aM m, wp)
  on  : ∀ sa y, C.Ab.on (sa, y) → B'.on (fa sa, y)

end LdLinPl

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinPlan_rows₁ : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (st : C.St6) (m : C.S.Msg),
    Slf.All p.sl₁ (C.tg₁ (C.sh st), fun _ => C.sh st) (p.G₁.msg m) ↔
    C.D.X.RecRow st.1.1.1.2 st.1.1.2.1 (C.uM m) ∧
    (∀ i, C.D.X.G.mulVec (C.uM m) (st.1.2.1 i) = st.1.2.2 i) ∧
    C.D.FoldR st.2 st.1.1.2.2 (C.D.X.msg (C.uM m)) (C.oM m)

def ldLinPlan_rows₂ : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (st : C.St6) (m : C.S.Msg),
    p.restG.val st.1.1.1.1 (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) =
      C.rest st.1.1.1.1 (C.aM m) →
    (Slf.All p.sl₂ (C.tg₂ st, fun _ => st) (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) ↔
      C.D.Eval (C.ψ st.1.1.1.1) (C.wM m) (C.rest st.1.1.1.1 (C.aM m)) (C.τ st.1.1.1.1) ∧
      C.D.Dot (C.g st.1.1.1.1) (C.oM m) st.1.1.2 (C.wM m))

/-- States: if `p.restG` is "rest" and B' says Ab (`p.SaysA B' fa`), the base joint of the plan says
the rows and Ab. -/
def ldLinPlan_says : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₂.Msg × C.Wpa)) (fa : C.Sta → St'),
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    p.SaysA B' fa → C.Says (p.base B') (C.fq fa)

end
end Spec
end Cb
