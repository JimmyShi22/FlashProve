-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanP.lean: the plan of the closing of the test for linear constraints as
a write-up of ours (lean/CREDITS.md) has it: one splitting, of the fold's row, in what the
instances share; two shared tests; then one test of the instance's own.

In standard terms: book-keeping for the last part of an interactive oracle proof. The linear
constraints (rows) that the test for linear constraints leaves open are arranged as the inputs of
three proximity tests, each on a group of oracles; the one constraint that spans two groups is first
replaced by one constraint on each.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanPProofs.lean.
This is the write-up's plan. The plans without a splitting (Cb/Ld/LdLinClosePlan.lean), with
two splittings (Cb/Ld/LdLinClosePlanS.lean) and with two in the order of a batch
(Cb/Ld/LdLinClosePlanT.lean) are not. The names of the shared part are those of
Cb/Ld/LdLinClosePlanT.lean; the instance's two rows are those of Cb/Ld/LdLinClosePlan.lean.
W, G_u and Ω are the test's oracle messages that hold the vectors w, u and ω (`C.nW`, `C.nU`,
`C.nO`, Cb/Ld/LdLinClosePre.lean); Ab is the base joint that a preamble leaves (`C.Ab`).
The five kinds of rows that the test leaves: `C.RowsM`; "rest": `C.rest`, a function of the state
and of `C.Sa`'s messages (both Cb/Ld/LdLinClosePre.lean). A splitting (`ldSplitR`,
Cb/Ld/LdSplit.lean) replaces one row a₁ + a₂ = t on two groups by two rows, a₁ + κ = τ' and
a₂ − κ = t − τ': the prover sends the scalar τ'; κ is an entry of a member of both groups.

The plan. One instance's chain. (The write-up names one code for W and Ω and one for G_u; it
does not say that they differ. The record (`LdLinPp`) asks nothing on codes: groups are any common
readings.)
  Shared. GU, with G_u in it, and GO, with Ω in it: groups of all oracle messages `C.S`. κ (`k₀`;
  not the type κ of `LdLinC E ι κ J Y`): an entry of a member of both.
    `front₁`: split the fold's row by κ; a step into the form that tests take.
    Test on GU: the record's rows, the columns, fU − κ; kept: kp₁.
    Test on GO: fO + κ (read among what is kept); kept: kp₂. Left: `p.S₂`, with Ω and W in it.
  The instance's. Gc, with Ω and W in it (and whatever "rest" reads; the write-up: exactly
  one further member; here any: wider): one group of what is left (`p.S₂`).
    Test on Gc: the evaluation (with "rest"), the inner product; kept: kp₃. Then whatever closes the
      rest (B', over `p.S₃`).
  All splittings come before all tests. The instance's two rows are carried through the shared
  tests as a claim on the kept messages, already in the form that a test takes (`p.base₃`).

Main names:
  `Spec.ldLinPp_says`: what the stage `p.x₁` says.
  `Spec.ldLinPp_hyp`: the hypotheses of the front's moves, from `p.Plain` (κ is in an oracle message
    other than G_u, Ω; Rs₀ holds what the splitting reads: the places lO, lU of the vectors in the
    named members and the mask entry; no pad entry need be read) and `p.Kept`.
  `Spec.ldLinPp_sd`: every step of the front has the budgets' half, for every demand
    (`(p.front₁ B').Sd q₁` for every q₁; `Front.Sd`, Cb/Ld/LdFront.lean: `SideC` from q₁ to q₁,
    Cb/Ld/LdTowerKitChain.lean).
  `Spec.ldLinPp_zk`: what is asked for the one splitting (`ZkOK`), from "its mask entry is fresh at
    the start of the front" and Rs₀ within Rd.
  `p.Plain.rsSh`: Rs₀ holds entries of shared oracle messages only. `Spec.ldLinPp_hyp` takes
    `p.Plain` whole, so it asks that clause; no proof of this file's statements reads it (that of
    `ldLinPV_tie`, Cb/Ld/LdLinClosePlanPVProofs.lean, does): it is there for a batch, where the
    shared part computes the splitting's scalar off what it holds. With `rs₀K` it says that κ's
    holder is a shared oracle message.

Notation: `p.Rs₀`, `Rd`: predicates on entries (`C.S.Ent`); `Rr`: a predicate on oracle messages
(`C.S.O`); `bs`: a predicate on values of `MaskFact ..` (Cb/Req1/LdSegFresh.lean).

Limits: this file does not say that κ is fresh (`Chain.FreshFor`, Ior/KnowCollRulesChain.lean; for a
batch `ChainV.FreshForV`, Cb/Ld/LdLinChainVMask.lean) after the test's core
(Cb/Ld/LdLinCloseSplit.lean, Cb/Ld/LdLinStdSp.lean; for a batch Cb/Ld/LdLinStdSpV.lean). It says
nothing on the tests themselves, the demands, the whole closing as a term
(Cb/Ld/LdLinCloseDemandP.lean, Cb/Ld/LdLinCloseDemandPA.lean), and nothing on the batch's two sides
(Cb/Ld/LdLinClosePlanPB.lean, Cb/Ld/LdLinClosePlanPV.lean).
The write-up's four conditions on κ, and what becomes of them here. (1) Its holder has no
data entries (is mask-only): not asked. (2) κ lies outside the holder's pad: asked at the senders
(Rs₀
within a set without pad entries), not of the plan. (3) The two forms of the split row do not read
it: asked (`ne₀O`, `ne₀U`). (4) The rest of what is claimed does not read it: not asked of "rest"
and B'; of the other rows it holds: they read places of Ω, G_u, W, and the holder is none of them
(not W, since it is shared: `rsSh` with `rs₀K`). What (1), (2), (4) are for is carried here by the
fact "κ is fresh at the start of the front". Wider.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinClosePlanTProofs
import Cb.Ld.LdLinCloseDemandV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The plan: the data. -/
structure LdLinPp {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) where
  GU  : Grp C.S
  GO  : Grp C.S
  hU  : GU.mem C.nU
  hO  : GO.mem C.nO
  k₀  : SplitAt GO GU
  Rs₀ : C.S.Ent → Prop
  [dRs₀ : DecidablePred Rs₀]
  /-- what is kept at the two shared bridges: Ω and W among it -/
  kp₁ : C.S.O → Prop
  [dKp₁ : DecidablePred kp₁]
  kp₂ : (C.S.sub kp₁).O → Prop
  [dKp₂ : DecidablePred kp₂]
  kO₁ : kp₁ C.nO
  kO₂ : kp₂ ⟨C.nO, kO₁⟩
  kW₁ : kp₁ C.nW
  kW₂ : kp₂ ⟨C.nW, kW₁⟩
  /-- the instance's group: a group of what is left -/
  Gc  : Grp ((C.S.sub kp₁).sub kp₂)
  hcO : Gc.mem ⟨⟨C.nO, kO₁⟩, kO₂⟩
  hcW : Gc.mem ⟨⟨C.nW, kW₁⟩, kW₂⟩
  kp₃ : ((C.S.sub kp₁).sub kp₂).O → Prop
  [dKp₃ : DecidablePred kp₃]
  restG : Slf E C.Sta Gc.C.J

attribute [instance] LdLinPp.dRs₀ LdLinPp.dKp₁ LdLinPp.dKp₂ LdLinPp.dKp₃

namespace LdLinPp
variable {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPp C)

abbrev S₁ : Sig E := C.S.sub p.kp₁
abbrev S₂ : Sig E := p.S₁.sub p.kp₂
abbrev S₃ : Sig E := p.S₂.sub p.kp₃

/-- the names of Ω and of W among what is left -/
abbrev nO₂ : p.S₂.O := ⟨⟨C.nO, p.kO₁⟩, p.kO₂⟩
abbrev nW₂ : p.S₂.O := ⟨⟨C.nW, p.kW₁⟩, p.kW₂⟩

/-- the second group, among what is kept at its test -/
abbrev G₂ : Grp p.S₁ := p.GO.sub p.kp₁

/-- the messages that are left after the shared tests; those that are kept to the end -/
def left₂ (m : C.S.Msg) : p.S₂.Msg :=
  p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)
def last₃ (m : C.S.Msg) : p.S₃.Msg := p.S₂.res (T := OMsg.Msg) p.kp₃ (p.left₂ m)

/-- the members of the group that is tested second are kept at the bridge before -/
structure Kept : Prop where
  o₁ : ∀ o, p.GO.mem o → p.kp₁ o

variable [Fintype Y] [Fintype κ] [Fintype J]

/-- the fold's row: its two parts; the record's rows and the columns -/
def fO : Slf E C.Sh6 p.GO.C.J :=
  p.GO.onMem C.nO p.hO (Slf.push C.lO fun s y => Alg.eqk s.2 (C.D.py y))
def fU : Slf E C.Sh6 p.GU.C.J :=
  p.GU.onMem C.nU p.hU
    (Slf.push (fun n : Y × (Fin C.D.klo → Bool) => C.lU (C.D.X.pl (C.D.lay n)))
      fun s n => -(Alg.eqk s.2 (C.D.py n.1) * Alg.eqk s.1.1.2.2 n.2))
def rc : ∀ _ : C.Brc, Slf E C.Sh6 p.GU.C.J
  | .inl z =>
    p.GU.onMem C.nU p.hU
      (Slf.push (fun j => C.lU (C.D.X.pl j)) fun s j => C.D.X.Z.mat s.1.1.1.1 z j)
  | .inr i => p.GU.onMem C.nU p.hU (Slf.push C.lU fun s k => C.D.X.G (s.1.2.1 i) k)

/-- The rows of the three tests. -/
def r₁ : ∀ _ : C.Brc ⊕ Unit, Slf E C.Sh6 p.GU.C.J
  | .inl b => p.rc b
  | .inr _ => p.fU.addAt (-1) p.k₀.e₂
def r₂ : ∀ _ : Unit, Slf E C.Sh6 p.G₂.C.J := fun _ => (p.fO.addAt 1 p.k₀.e₁).toSub p.kp₁
/-- the evaluation; the inner product: on the one group of what is left -/
def r₃ : ∀ _ : LinB₂, Slf E C.St6 p.Gc.C.J
  | .inl _ =>
    (p.Gc.onMem p.nW₂ p.hcW (Slf.push C.lW fun st c => Alg.eqk (C.D.pt (C.ψ st.1.1.1.1)) c)).plus
      fun st => p.restG st.1.1.1.1
  | .inr _ =>
    (p.Gc.onMem p.nO₂ p.hcO (Slf.push C.lO fun st y => C.g st.1.1.1.1 y)).sub
      (p.Gc.onMem p.nW₂ p.hcW (Slf.push C.lW fun st c => Alg.eqk (C.D.pt st.1.1.2) c))

variable {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₃.Msg × C.Wpa))

/-- The base joint in front of the instance's test: of what is left. -/
abbrev base₃ : IOR.Rels Unit (((LinB₂ → E) × (LinB₂ → C.St6)) × St') C.E₀ (p.S₂.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.r₃ x (p.Gc.msg m)) (onMsgRels (p.S₂.res (T := OMsg.Msg) p.kp₃) B')

/-- what is claimed beside the fold's row -/
abbrev Ar₁ :
    IOR.Rels Unit (((C.Brc → E) × (C.Brc → C.Sh6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St'))
      C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.rc x (p.GU.msg m)) (onMsgRels p.left₂ (p.base₃ B'))

/-- The stage at which the front starts: the rows that are left, the fold's row unsplit. -/
@[reducible] def x₁ : FSt C.S C.E₀ C.Wpa Unit := ⟨_, claimRels (splitIn p.fO p.fU) (p.Ar₁ B')⟩

/-- The base joint in front of the two shared tests; after them: `p.base₃`. -/
abbrev base₁ :
    IOR.Rels Unit
      (((C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) ×
        (((Unit → E) × (Unit → C.Sh6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St')))
      C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.r₁ x (p.GU.msg m))
    (onMsgRels (C.S.res (T := OMsg.Msg) p.kp₁)
      (claimRels (fun x m => Slf.All p.r₂ x (p.G₂.msg m))
        (onMsgRels (p.S₁.res (T := OMsg.Msg) p.kp₂) (p.base₃ B'))))

variable [Fintype E]

/-- The front: split the fold's row; each row goes to its test. -/
def front₁ : Front (p.x₁ B') ⟨_, p.base₁ B'⟩ :=
  LdLinPt.stepOn (.split p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ B')
      p.Rs₀ inferInstance (.nil (p.x₁ B')))
    _ fun s =>
      ((Sum.elim s.2.1.1 fun _ => s.1.2.1, Sum.elim s.2.1.2 fun _ => s.1.2.2),
        (oneClaim s.1.1, s.2.2))

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- B' says Ab. -/
structure SaysA (fa : C.Sta → St') : Prop where
  fwd : ∀ sa y m wp, C.Ab.rel sa y (C.aM m, wp) → B'.rel (fa sa) y (p.last₃ m, wp)
  bwd : ∀ sa y m wp,
    C.Ab.on (sa, y) → B'.relR (fa sa, y) (p.last₃ m, wp) → C.Ab.relR (sa, y) (C.aM m, wp)
  on  : ∀ sa y, C.Ab.on (sa, y) → B'.on (fa sa, y)

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- The mask entry is in an oracle message other than G_u, Ω; what the splitting reads. -/
structure Plain : Prop where
  ne₀O : p.k₀.o ≠ C.nO
  ne₀U : p.k₀.o ≠ C.nU
  rs₀O : ∀ y, p.Rs₀ ⟨C.nO, C.lO y⟩
  rs₀U : ∀ k, p.Rs₀ ⟨C.nU, C.lU k⟩
  rs₀K : p.Rs₀ ⟨p.k₀.o, p.k₀.j⟩
  /-- No proof of this file's statements uses this clause: for a batch: the splitting reads entries
  of shared oracle messages only -/
  rsSh : ∀ n, p.Rs₀ n → C.isSh n.1

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- all members of the two shared tests' groups are oracle messages that all instances share (asked
by nothing here; for a batch) -/
def Shared : Prop := ∀ o, p.GU.mem o ∨ p.GO.mem o → C.isSh o

end LdLinPp

/-- the explicit part at which the front starts -/
def LdLinC.fqP {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) {St' : Type}
    (fa : C.Sta → St') (st : C.St6) :
    (E × (C.Sh6 × C.Sh6)) ×
      (((C.Brc → E) × (C.Brc → C.Sh6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St')) :=
  ((0, (C.sh st, C.sh st)),
    ((C.tgRC (C.sh st), fun _ => C.sh st), ((C.tg₂ st, fun _ => st), fa st.1.1.1.1)))

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States: if `restG` is "rest" and B' says Ab (`p.SaysA B' fa`), the stage at which the front
starts says the rows and Ab. -/
def ldLinPp_says : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₃.Msg × C.Wpa)) (fa : C.Sta → St'),
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA B' fa → C.Says (p.x₁ B').A (C.fqP fa)

/-- The hypotheses of the front's moves, from `p.Plain` and `p.Kept`. -/
def ldLinPp_hyp : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₃.Msg × C.Wpa)),
    p.Plain → p.Kept → (p.front₁ B').prog.Hyp

def ldLinPp_sd : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₃.Msg × C.Wpa)) (q₁ : Finset (C.E₀.prod C.S.ext).Pos → Prop),
    (p.front₁ B').Sd q₁

/-- What is asked for the one splitting (`ZkOK`). -/
def ldLinPp_zk : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₃.Msg × C.Wpa)) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop)
      (bs : MaskFact (p.x₁ B').stage.J.W → Prop),
    (∀ n, p.Rs₀ n → Rd n) →
    bs ((p.x₁ B').stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u) →
    (p.front₁ B').ZkOK Rd Rr bs

end
end Spec
end Cb
