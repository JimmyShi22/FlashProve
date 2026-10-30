-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanT.lean: book-keeping for the last part of an interactive oracle proof. The
linear constraints (rows) that the test for linear constraints leaves open are arranged as the
inputs of four proximity tests, each on a group of oracles; a constraint that spans two groups is
first replaced by one constraint on each (a splitting; this plan has two). Here what all instances
of a batch share comes first.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanTProofs.lean.
It uses Cb/Ld/LdLinClosePlanS.lean (the same rows and the same four tests with both splittings in
front: the notation of the rows), Cb/Ld/LdFront.lean, Cb/Ld/LdLinClosePre.lean. The closing that
this plan is for is that of Cb/Ld/LdLinCloseAlt.lean (a closing in which fronts and whole tests
alternate); no name of it is used here.
W, G_u and Ω are the oracle messages of the test for linear constraints on the encoded index
(Cb/Ld/LdLin.lean) that hold the vectors w, u and ω (`C.nW`, `C.nU`, `C.nO`,
Cb/Ld/LdLinClosePre.lean); Ab is the base joint that a preamble leaves (`C.Ab`).
A splitting is an `ldSplitR` (Cb/Ld/LdSplit.lean; its two rows are told in the head of
Cb/Ld/LdLinClosePlanS.lean).

This is not the plan of a write-up of ours (lean/CREDITS.md; that is
Cb/Ld/LdLinClosePlanP.lean, whose shared part has the same names as this file's): the
write-up puts W and Ω under one code, has one
splitting, of the fold's row, and no scalar of an instance's own: so no front stands behind a test
in it. This plan is wider: it serves data in which W's and Ω's codes differ too.

The plan. One instance's chain. The codes of G_u and Ω differ, and so do those of W and Ω (no field
of `LdLinPt` asks that).
  Shared. GU, with G_u in it, and GO, with Ω in it: groups of all oracle messages `C.S`. κ° (`k₀`):
  an entry of a member of both.
    `front₁`: split the fold's row by κ°; a step into the form that tests take.
    Test on GU: the record's rows, the columns, fU − κ°; kept: kp₁.
    Test on GO: fO + κ° (read among what is kept); kept: kp₂. Left: `p.S₂`, with Ω and W in it.
  The instance's. GcO, with Ω in it, and GcW, with W (and whatever "rest" reads): groups of what is
  left (`p.S₂`). κ_c (`k₁`): an entry of a member of both.
    `front₂`: split the inner product by κ_c; a step.
    Test on GcO: dO + κ_c; kept: kp₃.
    Test on GcW: the evaluation, dW − κ_c (read among what is kept); kept: kp₄. Then whatever closes
      the rest (B').

Main names:
  `p.x₁`, `C.fqT fa`: the stage (`FSt`, Cb/Ld/LdFront.lean) at which `front₁` starts: the rows that
    are left, unsplit; its explicit part.
  `p.Shared`: all members of GU and GO are shared oracle messages (asked by nothing here; for a
    batch).
  `Spec.ldLinPt_says`: `p.x₁` says the rows and Ab (`C.Says`), if `restG` is "rest" (`C.rest`) and
    B' says Ab (`p.SaysA B' fa`).
  `Spec.ldLinPt_hyp`: the hypotheses of the moves of both fronts, from `p.Plain` (κ° is in an oracle
    message other than Ω, G_u, and κ_c in one other than Ω, W (`ne₀O`, `ne₀U`, `ne₁O`, `ne₁W`); the
    oracle message that holds κ_c is no member of GU or GO: no test on a group that holds it comes
    before its splitting; Rs₀, Rs₁ hold what the splittings read: the places lO, lU, lW of the
    vectors in the named members and the mask entry; no pad entry need be read) and `p.Kept` (the
    members of GO are kept at the first bridge, those of GcW at the third).
  `Spec.ldLinPt_sd`: every step of both fronts has the budgets' half, for every demand (`Front.Sd`,
    Cb/Ld/LdFront.lean; `IOR.SideC`, Cb/Ld/LdTowerKitChain.lean).
  `Spec.ldLinPt_zk`: what is asked for each front's one splitting (`ZkOK`, Cb/Ld/LdFront.lean), from
    "its mask entry is fresh at the start of that front" and Rs within Rd. (Each front has one
    splitting, so nothing is asked on the other's mask here.)

Limits: this file does not say that κ° is fresh after the test's core, and κ_c after the core,
`front₁` and the two shared tests. The tests themselves, the demands (but for `Spec.ldLinPt_sd`,
which runs over every demand), the whole closing as a term: not in this file. It says nothing on the
batch's two sides.
The rows and the shared part restate, in our own words, the write-up; the instance's
splitting and its place behind the shared tests are ours.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinClosePlanSProofs
import Cb.Ld.LdLinCloseAltProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- equality of entries of a group's message is decidable: the instance that is found for a group of
any signature, named, for groups of signatures at which the search does not find it -/
def Grp.decEnt {E : Type} {S : Sig E} (G : Grp S) : DecidableEq G.C.J := inferInstance

/-- The plan in the order of a batch: the data. -/
structure LdLinPt {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) where
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
  /-- the instance's groups: groups of what is left -/
  GcO : Grp ((C.S.sub kp₁).sub kp₂)
  GcW : Grp ((C.S.sub kp₁).sub kp₂)
  hcO : GcO.mem ⟨⟨C.nO, kO₁⟩, kO₂⟩
  hcW : GcW.mem ⟨⟨C.nW, kW₁⟩, kW₂⟩
  k₁  : SplitAt GcO GcW
  Rs₁ : ((C.S.sub kp₁).sub kp₂).Ent → Prop
  [dRs₁ : DecidablePred Rs₁]
  kp₃ : ((C.S.sub kp₁).sub kp₂).O → Prop
  [dKp₃ : DecidablePred kp₃]
  kp₄ : (((C.S.sub kp₁).sub kp₂).sub kp₃).O → Prop
  [dKp₄ : DecidablePred kp₄]
  restG : Slf E C.Sta GcW.C.J

attribute [instance] LdLinPt.dRs₀ LdLinPt.dRs₁ LdLinPt.dKp₁ LdLinPt.dKp₂ LdLinPt.dKp₃ LdLinPt.dKp₄

namespace LdLinPt
variable {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPt C)

abbrev S₁ : Sig E := C.S.sub p.kp₁
abbrev S₂ : Sig E := p.S₁.sub p.kp₂
abbrev S₃ : Sig E := p.S₂.sub p.kp₃
abbrev S₄ : Sig E := p.S₃.sub p.kp₄

instance : DecidableEq p.GcO.C.J := p.GcO.decEnt
instance : DecidableEq p.GcW.C.J := p.GcW.decEnt

/-- the names of Ω and of W among what is left -/
abbrev nO₂ : p.S₂.O := ⟨⟨C.nO, p.kO₁⟩, p.kO₂⟩
abbrev nW₂ : p.S₂.O := ⟨⟨C.nW, p.kW₁⟩, p.kW₂⟩

/-- the second and the fourth group, among what is kept at their tests -/
abbrev G₂ : Grp p.S₁ := p.GO.sub p.kp₁
abbrev G₄ : Grp p.S₃ := p.GcW.sub p.kp₃

/-- the messages that are left after the shared tests; those that are kept to the end -/
def left₂ (m : C.S.Msg) : p.S₂.Msg :=
  p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)
def last₂ (m : p.S₂.Msg) : p.S₄.Msg :=
  p.S₃.res (T := OMsg.Msg) p.kp₄ (p.S₂.res (T := OMsg.Msg) p.kp₃ m)

/-- the members of a group that is tested second are kept at the bridge before -/
structure Kept : Prop where
  o₁ : ∀ o, p.GO.mem o → p.kp₁ o
  w₃ : ∀ o, p.GcW.mem o → p.kp₃ o

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

/-- the inner product: its two parts; the evaluation: on groups of what is left -/
def dO : Slf E C.St6 p.GcO.C.J :=
  p.GcO.onMem p.nO₂ p.hcO (Slf.push C.lO fun st y => C.g st.1.1.1.1 y)
def dW : Slf E C.St6 p.GcW.C.J :=
  p.GcW.onMem p.nW₂ p.hcW (Slf.push C.lW fun st c => -Alg.eqk (C.D.pt st.1.1.2) c)
def ev : Slf E C.St6 p.GcW.C.J :=
  (p.GcW.onMem p.nW₂ p.hcW (Slf.push C.lW fun st c => Alg.eqk (C.D.pt (C.ψ st.1.1.1.1)) c)).plus
    fun st => p.restG st.1.1.1.1

/-- The rows of the four tests. -/
def r₁ : ∀ _ : C.Brc ⊕ Unit, Slf E C.Sh6 p.GU.C.J
  | .inl b => p.rc b
  | .inr _ => p.fU.addAt (-1) p.k₀.e₂
def r₂ : ∀ _ : Unit, Slf E C.Sh6 p.G₂.C.J := fun _ => (p.fO.addAt 1 p.k₀.e₁).toSub p.kp₁
def r₃ : ∀ _ : Unit, Slf E C.St6 p.GcO.C.J := fun _ => p.dO.addAt 1 p.k₁.e₁
def r₄ : ∀ _ : LinB₂, Slf E C.St6 p.G₄.C.J
  | .inl _ => p.ev.toSub p.kp₃
  | .inr _ => (p.dW.addAt (-1) p.k₁.e₂).toSub p.kp₃

variable {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa))

/-- what is claimed beside the inner product, of what is left -/
abbrev Ar₂ : IOR.Rels Unit ((E × C.St6) × St') C.E₀ (p.S₂.Msg × C.Wpa) :=
  claimRels (fun x m => p.ev.Holds x (p.GcW.msg m)) (onMsgRels p.last₂ B')

/-- The stage at which the instance's front starts: the instance's rows, unsplit, on what is left.
-/
@[reducible] def x₂ : FSt p.S₂ C.E₀ C.Wpa Unit := ⟨_, claimRels (splitIn p.dO p.dW) (p.Ar₂ B')⟩

/-- The base joint in front of the instance's two tests. -/
abbrev base₂ :
    IOR.Rels Unit (((Unit → E) × (Unit → C.St6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St'))
      C.E₀ (p.S₂.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.r₃ x (p.GcO.msg m))
    (onMsgRels (p.S₂.res (T := OMsg.Msg) p.kp₃)
      (claimRels (fun x m => Slf.All p.r₄ x (p.G₄.msg m))
        (onMsgRels (p.S₃.res (T := OMsg.Msg) p.kp₄) B')))

/-- what is claimed beside the fold's row -/
abbrev Ar₁ :
    IOR.Rels Unit (((C.Brc → E) × (C.Brc → C.Sh6)) × (p.x₂ B').St) C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.rc x (p.GU.msg m)) (onMsgRels p.left₂ (p.x₂ B').A)

/-- The stage at which the shared front starts: the rows that are left, unsplit. -/
@[reducible] def x₁ : FSt C.S C.E₀ C.Wpa Unit := ⟨_, claimRels (splitIn p.fO p.fU) (p.Ar₁ B')⟩

/-- The base joint in front of the two shared tests; after them: `p.x₂`. -/
abbrev base₁ :
    IOR.Rels Unit
      (((C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) ×
        (((Unit → E) × (Unit → C.Sh6)) × (p.x₂ B').St))
      C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.r₁ x (p.GU.msg m))
    (onMsgRels (C.S.res (T := OMsg.Msg) p.kp₁)
      (claimRels (fun x m => Slf.All p.r₂ x (p.G₂.msg m))
        (onMsgRels (p.S₁.res (T := OMsg.Msg) p.kp₂) (p.x₂ B').A)))

variable [Fintype E]

/-- a step of a front over any signature that only maps the explicit part -/
def stepOn {S : Sig E} {x y : FSt S C.E₀ C.Wpa Unit} (q : Front x y)
    (z : FSt S C.E₀ C.Wpa Unit) (f : y.St → z.St) : Front x z :=
  .step q z (sideF S f) (sideG S (ExtMap.id C.E₀))
    (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2)

/-- The shared front: split the fold's row; each row goes to its test. -/
def front₁ : Front (p.x₁ B') ⟨_, p.base₁ B'⟩ :=
  stepOn (.split p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (p.Ar₁ B')
      p.Rs₀ inferInstance (.nil (p.x₁ B')))
    _ fun s =>
      ((Sum.elim s.2.1.1 fun _ => s.1.2.1, Sum.elim s.2.1.2 fun _ => s.1.2.2),
        (oneClaim s.1.1, s.2.2))

/-- The instance's front: split the inner product; each row goes to its test. -/
def front₂ : Front (p.x₂ B') ⟨_, p.base₂ B'⟩ :=
  stepOn (.split p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW _ (p.Ar₂ B')
      p.Rs₁ inferInstance (.nil (p.x₂ B')))
    _ fun s =>
      (oneClaim s.1.1,
        ((Sum.elim (fun _ => s.2.1.1) fun _ => s.1.2.1,
            Sum.elim (fun _ => s.2.1.2) fun _ => s.1.2.2),
          s.2.2))

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- B' says Ab. -/
structure SaysA (fa : C.Sta → St') : Prop where
  fwd : ∀ sa y m wp, C.Ab.rel sa y (C.aM m, wp) → B'.rel (fa sa) y (p.last₂ (p.left₂ m), wp)
  bwd : ∀ sa y m wp,
    C.Ab.on (sa, y) → B'.relR (fa sa, y) (p.last₂ (p.left₂ m), wp) → C.Ab.relR (sa, y) (C.aM m, wp)
  on  : ∀ sa y, C.Ab.on (sa, y) → B'.on (fa sa, y)

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- The two mask entries stand in oracle messages other than those that the row which each splits
reads (`ne₀O`, `ne₀U`, `ne₁O`, `ne₁W`); what the splittings read. -/
structure Plain : Prop where
  ne₀O : p.k₀.o ≠ C.nO
  ne₀U : p.k₀.o ≠ C.nU
  ne₁O : p.k₁.o ≠ p.nO₂
  ne₁W : p.k₁.o ≠ p.nW₂
  /-- the oracle message that holds the instance's mask entry is no member of a shared test's
  group -/
  noU  : ¬ p.GU.mem p.k₁.o.1.1
  noO  : ¬ p.GO.mem p.k₁.o.1.1
  rs₀O : ∀ y, p.Rs₀ ⟨C.nO, C.lO y⟩
  rs₀U : ∀ k, p.Rs₀ ⟨C.nU, C.lU k⟩
  rs₀K : p.Rs₀ ⟨p.k₀.o, p.k₀.j⟩
  rs₁O : ∀ y, p.Rs₁ ⟨p.nO₂, C.lO y⟩
  rs₁W : ∀ c, p.Rs₁ ⟨p.nW₂, C.lW c⟩
  rs₁K : p.Rs₁ ⟨p.k₁.o, p.k₁.j⟩

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- all members of the two shared tests' groups are oracle messages that all instances share (asked
by nothing here; for a batch) -/
def Shared : Prop := ∀ o, p.GU.mem o ∨ p.GO.mem o → C.isSh o

end LdLinPt

/-- the explicit part at which the shared front starts -/
def LdLinC.fqT {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) {St' : Type}
    (fa : C.Sta → St') (st : C.St6) :
    (E × (C.Sh6 × C.Sh6)) ×
      (((C.Brc → E) × (C.Brc → C.Sh6)) × ((E × (C.St6 × C.St6)) × ((E × C.St6) × St'))) :=
  ((0, (C.sh st, C.sh st)),
    ((C.tgRC (C.sh st), fun _ => C.sh st), ((0, (st, st)), ((C.τ st.1.1.1.1, st), fa st.1.1.1.1))))

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States: if `restG` is "rest" and B' says Ab (`p.SaysA B' fa`), the stage at which the shared
front starts says the rows and Ab. -/
def ldLinPt_says : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St'),
    (∀ sa m, p.restG.val sa (p.GcW.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA B' fa → C.Says (p.x₁ B').A (C.fqT fa)

/-- The hypotheses of the moves of both fronts. -/
def ldLinPt_hyp : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)),
    p.Plain → p.Kept → (p.front₁ B').prog.Hyp ∧ (p.front₂ B').prog.Hyp

def ldLinPt_sd : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (q₁ : Finset (C.E₀.prod C.S.ext).Pos → Prop)
      (q₂ : Finset (C.E₀.prod p.S₂.ext).Pos → Prop),
    (p.front₁ B').Sd q₁ ∧ (p.front₂ B').Sd q₂

/-- What is asked for each front's one splitting. -/
def ldLinPt_zk : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)),
    (∀ (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop) (bs : MaskFact (p.x₁ B').stage.J.W → Prop),
      (∀ n, p.Rs₀ n → Rd n) →
      bs ((p.x₁ B').stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u) →
      (p.front₁ B').ZkOK Rd Rr bs) ∧
    ∀ (Rd : p.S₂.Ent → Prop) (Rr : p.S₂.O → Prop) (bs : MaskFact (p.x₂ B').stage.J.W → Prop),
      (∀ n, p.Rs₁ n → Rd n) →
      bs ((p.x₂ B').stage.wideFact Rd Rr (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u) →
      (p.front₂ B').ZkOK Rd Rr bs

end
end Spec
end Cb
