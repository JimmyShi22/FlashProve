-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePre.lean: a step without rounds of an interactive oracle reduction, from "the rows
that are left" of the test for linear constraints on the encoded index to a joint over one
signature: nested pairs of oracles and witnesses are re-bracketed into one indexed family; no round,
no error.

In standard terms: a signature (`Sig`, Cb/Ld/LdSig.lean) is a finite family of oracle messages, each
with its code, its sample map and its radius. `S.over A` is the joint that claims A of the messages
of these oracle messages: in the exact relation the oracles are encodings of them and the messages
have their samples' answers; in the relaxed relation each oracle decodes, with its sample, to the
witness's message.

Definitions and statements; the proofs are in Cb/Ld/LdLinClosePreProofs.lean.
It uses Cb/Ld/LdLin.lean (the test up to its last joint j6), Cb/Ld/LdSig.lean, Cb/Ld/LdSigSum.lean
(signatures side by side) and Ior/KnowCollRulesFrame.lean (`StepT`: a step without rounds leads from
A to B; the extractor may read the whole statement at which the step starts).

Why: Cb/Ld/LdLin.lean ends at the joint j6: three families of oracle messages (those sent with W,
with G_u, with Ω), nested one sending in another, beside any joint Aa that a preamble left; and five
kinds of rows (linear claims) on the vectors w, u, ω that are in their messages. The blocks that
close a statement (splits, batchings, tests on groups) speak of one signature and a base joint on
its messages (`S.over`).

Main names:
  `LdLinC`, the test over a signature: the data of Cb/Ld/LdLin.lean's `LdLinP`, with what the
    preamble left given as a joint over a signature Sa (base joint Ab, further oracles E₀, further
    witness Wpa), and "rest" a function of the state and of Sa's messages.
  `C.St6`: the explicit part without the samples: (((state of the preamble, record), shared point),
    locations and folds read), ζ.
  `C.RowsM st m`: the rows that are left, read off a tuple of messages of `C.S`: the record's row
    and the columns on u, the fold's row on (ω, u), the evaluation on (w, rest), the inner product
    on (ω, w).
  `C.Says Bq fq`: the base joint Bq says the rows and Ab, at the explicit part fq st. Three clauses,
    for each tuple of messages: forth for the exact forms; back for the relaxed forms, where
    `C.Ab.on` holds; the condition is handed on.
  `Spec.ldLinPre_rows`: `C.RowsM` is Cb/Ld/LdLin.lean's `Rows` at the re-bracketed statement.
  `Spec.ldLinPre_step`: for every base joint Bq that says the rows and Ab: the re-bracketing is a
    step without rounds from `C.P.j6` to `C.S.over Bq`.
  `Spec.ldLinPre_step_cf`: under `C.Says Bq fq`, the step of `Spec.ldLinPre_step` between the joints
    whose condition may fail (`Rels.cf`, Ior/KnowCollGood.lean: the condition is moved into the
    relaxed relation).

Limits: this file does not say which base joint: which groups there are, whether a row is split,
which tests follow: Cb/Ld/LdLinClosePlan.lean (a base joint and its groups, no split); its tests:
`LdLinPlT`, Cb/Ld/LdLinCloseDemand.lean.
It says nothing on the batch.
The step is glue in this library's Lean text.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinProofs
import Cb.Ld.LdLinWordsProofs
import Cb.Ld.LdSigSum
import Cb.Ld.LdLinCloseChain

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- The test over a signature: the data. -/
structure LdLinC (E ι κ J Y : Type) [Field E] where
  D  : LdLinW E ι κ J Y
  Sy : Type
  up : Sy → D.X.Row → E
  e' : ℕ
  t  : ℕ
  /-- what a preamble leaves: a signature, further oracles, the explicit part without the samples, a
  further witness, a base joint -/
  Sa  : Sig E
  E₀  : ExtSpec
  Sta : Type
  Wpa : Type
  Ab  : IOR.Rels Unit Sta E₀ (Sa.Msg × Wpa)
  /-- the tensor row -/
  g    : Sta → Y → E
  ψ    : Sta → D.Pt
  τ    : Sta → E
  rest : Sta → Sa.Msg → E
  /-- the three families of oracle messages, how their seeds are drawn, the members that hold w, u,
  ω, and where these are -/
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : D.Col → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : κ → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Y → (NO.om iO).C.J

namespace LdLinC
variable {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y)

/-- The data of Cb/Ld/LdLin.lean. -/
@[reducible] def P : LdLinP E ι κ J Y where
  D := C.D
  Sy := C.Sy
  up := C.up
  e' := C.e'
  t := C.t
  Ea := C.E₀.prod C.Sa.ext
  Xa := C.Sta × C.Sa.Smp
  Wa := C.Sa.Wit × C.Wpa
  Aa := C.Sa.over C.Ab
  g := fun x => C.g x.1
  ψ := fun x => C.ψ x.1
  τ := fun x => C.τ x.1
  rest := fun x wa => C.rest x.1 (C.Sa.msgs wa.1)
  NW := C.NW
  SdW := C.SdW
  iW := C.iW
  lW := C.lW
  NU := C.NU
  SdU := C.SdU
  iU := C.iU
  lU := C.lU
  NO := C.NO
  SdO := C.SdO
  iO := C.iO
  lO := C.lO

/-- All oracle messages at the end of the test. -/
abbrev S : Sig E := ((C.Sa.sum C.NW).sum C.NU).sum C.NO

/-- the names of the members that hold w, u, ω -/
abbrev nW : C.S.O := .inl (.inl (.inr C.iW))
abbrev nU : C.S.O := .inl (.inr C.iU)
abbrev nO : C.S.O := .inr C.iO

/-- a family over all oracle messages, from its four parts -/
def join4 {T : OMsg E → Type} (a : ∀ i, T (C.Sa.om i)) (w : ∀ i, T (C.NW.om i))
    (u : ∀ i, T (C.NU.om i)) (o : ∀ i, T (C.NO.om i)) : ∀ i, T (C.S.om i) :=
  ((C.Sa.sum C.NW).sum C.NU).join
    C.NO (T := T) ((C.Sa.sum C.NW).join C.NU (T := T) (C.Sa.join C.NW (T := T) a w) u) o

/-- the explicit part without the samples -/
abbrev St6 : Type :=
  (((C.Sta × C.D.X.Rec) × C.D.Pt) × ((Fin C.t → ι) × (Fin C.t → E))) × (Fin C.D.l → E)

/-- the vectors that a tuple of messages holds; the messages that the preamble left -/
def wM (m : C.S.Msg) : C.D.Col → E := fun c => m C.nW (C.lW c)
def uM (m : C.S.Msg) : κ → E := fun k => m C.nU (C.lU k)
def oM (m : C.S.Msg) : Y → E := fun y => m C.nO (C.lO y)
def aM (m : C.S.Msg) : C.Sa.Msg := fun i => m (.inl (.inl (.inl i)))

variable [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]

/-- The rows that are left, read off a tuple of messages. -/
def RowsM (st : C.St6) (m : C.S.Msg) : Prop :=
  C.D.X.RecRow st.1.1.1.2 st.1.1.2.1 (C.uM m) ∧
  (∀ i, C.D.X.G.mulVec (C.uM m) (st.1.2.1 i) = st.1.2.2 i) ∧
  C.D.FoldR st.2 st.1.1.2.2 (C.D.X.msg (C.uM m)) (C.oM m) ∧
  C.D.Eval (C.ψ st.1.1.1.1) (C.wM m) (C.rest st.1.1.1.1 (C.aM m)) (C.τ st.1.1.1.1) ∧
  C.D.Dot (C.g st.1.1.1.1) (C.oM m) st.1.1.2 (C.wM m)

omit [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]

/-- The re-bracketing: the explicit part. -/
def toSt (x : C.P.X6) : C.St6 :=
  ((((x.1.1.1.1.1.1.1.1, x.1.1.1.1.1.1.2), x.1.1.1.1.2), x.1.1.2), x.2)
def toSmp (x : C.P.X6) : C.S.Smp :=
  C.join4 (T := OMsg.Smp) x.1.1.1.1.1.1.1.2 x.1.1.1.1.1.2 x.1.1.1.2 x.1.2

/-- the oracles: a copy -/
def toE : ExtMap C.P.E5 (C.E₀.prod C.S.ext) where
  map := fun y => (y.1.1.1.1, C.join4 (T := OMsg.Str) y.1.1.1.2 y.1.1.2 y.1.2 y.2)
  src := fun q => match q with
    | .inl p => {.inl (.inl (.inl (.inl p)))}
    | .inr ⟨.inl (.inl (.inl a)), x⟩ => {.inl (.inl (.inl (.inr ⟨a, x⟩)))}
    | .inr ⟨.inl (.inl (.inr a)), x⟩ => {.inl (.inl (.inr ⟨a, x⟩))}
    | .inr ⟨.inl (.inr a), x⟩ => {.inl (.inr ⟨a, x⟩)}
    | .inr ⟨.inr a, x⟩ => {.inr ⟨a, x⟩}

/-- the witnesses, forth: the table of full messages of the index is dropped -/
def toW (w : C.P.W5) : C.S.Wit × C.Wpa :=
  (C.join4 (T := OMsg.Wit) w.2.2.2.2.1 w.2.2.1 w.2.1 w.1, w.2.2.2.2.2)

/-- the witnesses, back: the table of full messages of the index is filled with zeros (no relaxed
relation reads it) -/
def back (w : C.S.Wit × C.Wpa) : C.P.W5 :=
  (fun i => w.1 (.inr i),
    (fun i => w.1 (.inl (.inr i)),
      (fun i => w.1 (.inl (.inl (.inr i))),
        (fun _ _ => 0, (fun i => w.1 (.inl (.inl (.inl i))), w.2)))))

variable [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]

/-- The base joint Bq says the rows and Ab. -/
structure Says {Stq : Type} (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) (fq : C.St6 → Stq) :
    Prop where
  fwd : ∀ st y m wp, C.RowsM st m → C.Ab.rel st.1.1.1.1 y (C.aM m, wp) → Bq.rel (fq st) y (m, wp)
  bwd : ∀ st y m wp, C.Ab.on (st.1.1.1.1, y) → Bq.relR (fq st, y) (m, wp) →
    C.RowsM st m ∧ C.Ab.relR (st.1.1.1.1, y) (C.aM m, wp)
  on  : ∀ st y, C.Ab.on (st.1.1.1.1, y) → Bq.on (fq st, y)

omit [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]
variable {Stq : Type} (fq : C.St6 → Stq)

/-- the step's two maps that read fq: `stepF`, `stepM` (`C.toE` and `C.back` do not read it) -/
def stepF (x : C.P.X6) : Option (Stq × C.S.Smp) := some (fq (C.toSt x), C.toSmp x)
def stepM (a : C.P.X6 × C.P.W5) : (Stq × C.S.Smp) × (C.S.Wit × C.Wpa) :=
  ((fq (C.toSt a.1), C.toSmp a.1), C.toW a.2)

variable [Fintype Y] [Fintype ι] [Fintype κ] [Fintype J]

/-- the last joint of the test, with its types; the condition may fail -/
abbrev j6J : IOR.Joint Unit := ⟨C.P.X6, C.P.E5, C.P.W5, C.P.j6.cf⟩

/-- The step as a link, and as a chain. -/
def link (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) : IOR.Link Unit C.j6J (C.S.jointCf Bq) :=
  ⟨IOR.pure (C.stepF fq) C.toE,
    IOR.Honest.pure (C.stepF fq) C.toE (C.stepM fq),
    fun _ _ w => C.back w,
    IOR.Nums.pure Unit (C.stepF fq) C.toE⟩

def chain (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) : IOR.Chain Unit C.j6J (C.S.jointCf Bq) :=
  .one (C.link fq Bq)

end LdLinC

namespace Spec
open IOR
section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The rows, read off the messages, are the rows of Cb/Ld/LdLin.lean. -/
def ldLinPre_rows : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (x : C.P.X6) (w : C.P.W5),
    C.P.Rows x (C.P.wv (C.NW.msgs w.2.2.1)) (C.P.uv (C.NU.msgs w.2.1))
      (C.P.ov (C.NO.msgs w.1)) w.2.2.2.2 ↔
    C.RowsM (C.toSt x) (C.S.msgs (C.toW w).1)

/-- The step. States: if `C.Says Bq fq`, the re-bracketing is a step without rounds (`StepT`) from
`C.P.j6` to `C.S.over Bq`. -/
def ldLinPre_step : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Stq : Type)
      (Bq : Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) (fq : C.St6 → Stq),
    C.Says Bq fq → StepT (C.stepF fq) C.toE (C.stepM fq) (fun _ w => C.back w) C.P.j6 (C.S.over Bq)

def ldLinPre_step_cf : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Stq : Type)
      (Bq : Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa)) (fq : C.St6 → Stq),
    C.Says Bq fq →
    StepT (C.stepF fq) C.toE (C.stepM fq) (fun _ w => C.back w) C.P.j6.cf (C.S.over Bq).cf

end
end Spec
end Cb
