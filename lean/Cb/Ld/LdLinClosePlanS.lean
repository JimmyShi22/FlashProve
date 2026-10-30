-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanS.lean: book-keeping for the last part of an interactive oracle proof. The
linear constraints (rows) that the test for linear constraints leaves open are arranged as the
inputs of four proximity tests, each on a group of oracles; a constraint that spans two groups is
first replaced by one constraint on each (a splitting; this plan has two).
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanSProofs.lean.
It uses Cb/Ld/LdLinClosePre.lean, Cb/Ld/LdLinClosePlan.lean (the plan without a splitting: the
notation of the rows), Cb/Ld/LdFront.lean, Cb/Ld/LdLinCloseChain.lean (whole tests in a row; no name
of it is used here), Cb/Ld/LdBatPeel.lean (a claim written in another form; a group among the kept
oracle messages).
W, G_u and Ω are the test's oracle messages that hold the vectors w, u and ω (`C.nW`, `C.nU`,
`C.nO`, Cb/Ld/LdLinClosePre.lean); Ab is the base joint that a preamble leaves (`C.Ab`).
A splitting (`ldSplitR`, Cb/Ld/LdSplit.lean) replaces one row a₁ + a₂ = t on two groups by two rows,
a₁ + κ = τ' and a₂ − κ = t − τ': the prover sends the scalar τ'; κ is an entry of a member of both
groups.

This is not the plan of a write-up of ours (lean/CREDITS.md; that is
Cb/Ld/LdLinClosePlanP.lean): the write-up puts W and Ω under one code and has one splitting,
of the fold's row; no row of an instance's own is split. This plan is wider: it serves data in which
W's and Ω's codes differ too. Its first splitting and its two shared tests are the
write-up's.

The plan. The codes of G_u and Ω differ, and so do those of W and Ω (no field of `LdLinPs` asks
that). One instance. The four groups: `GU`, `GO`, `GcO`, `GcW` (fields of `LdLinPs`).
  Two mask entries: κ° (`k₀`): an entry of an oracle message that is a member of the groups GO and
    GU (the shared mask-only message; see "Limits:"); κ_c (`k₁`): one of a member of GcO and of GcW
    (the instance's). The test itself has sent both, with one of its three families (no field of
    `LdLinPs` asks that).
  The rows that are left, unsplit (`p.x`, the stage (`FSt`, Cb/Ld/LdFront.lean); `C.fqS`, its
    explicit part):
      the fold's row: fO (on GO: Ω's extension at ζ) + fU (on GU: minus the kernel on the layout's
        places of u) = 0;
      the inner product: dO (on GcO: ⟨g, ω⟩) + dW (on GcW: minus W's extension at ψ*, the point
        `C.D.pt st.1.1.2`: the shared point of `C.Sh6`, Cb/Ld/LdLinClosePlan.lean) = 0;
      the record's rows and the columns at the locations (`rc`), on GU; the evaluation (`ev`), on
        GcW; what the preamble left (Ab).
  The front (`p.front B' fa`): split the fold's row by κ°; a step (the two claims on two groups
    change places); split the inner product by κ_c; a step (into the form that tests in a row take).
    All splittings come before the tests. Two scalars are sent.
  The four tests, in this order (`p.base B'`: the base joint):
      on GU: the record's rows, the columns, fU − κ° (shared);
      on GO: fO + κ° (shared);
      on GcO: dO + κ_c (the instance's: its row on Ω stands here);
      on GcW: the evaluation, dW − κ_c (the instance's);
    then whatever closes the rest (B', on the messages kept).
  The states of the rows on GU and GO are the part of the explicit part that all instances share
    (`C.Sh6`). The targets of the four rows that come out of a splitting are the scalars sent and
    their complements; all others are those of Cb/Ld/LdLinClosePlan.lean.

Main names:
  `Spec.ldLinPs_says`: `p.x` says the rows and Ab (Cb/Ld/LdLinClosePre.lean: `C.Says`), if `restG`
    is "rest" (`C.rest`).
  `Spec.ldLinPs_hyp`: the hypotheses of the front's moves (Cb/Req1/LdSeg.lean), from: `p.Plain` (κ°
    is in an oracle message other than Ω, G_u, and κ_c in one other than Ω, W (`ne₀O`, `ne₀U`,
    `ne₁O`, `ne₁W`), so the two parts of the row that each splits do not read it; Rs₀, Rs₁ hold what
    the two splittings read: the places lO, lU, lW of the vectors in the named members and the mask
    entry, not all entries of these messages: no pad entry need be read); `p.Kept`; B' says Ab.
  `Spec.ldLinPs_sd`: every step of the front has the budgets' half, from q to q, for every q
    (`Front.Sd`, Cb/Ld/LdFront.lean; `IOR.SideC`, Cb/Ld/LdTowerKitChain.lean).
  `Spec.ldLinPs_zk`: under `p.Plain`: "what is asked for the splittings" (Cb/Ld/LdFront.lean:
    `ZkOK`) from the two facts "κ° is fresh", "κ_c is fresh" at the start of the front, κ° ≠ κ_c,
    and Rs₀, Rs₁ within Rd: the steps hand the witness on; the first splitting does not look at κ_c.

Limits:
This file does not say that κ° and κ_c are fresh (Cb/Ld/LdLinCloseSplit.lean). It says nothing on
the tests themselves, nothing on the demands on positions, but for `Spec.ldLinPs_sd`, which runs
over every demand q (what the four tests need: Cb/Ld/LdLinCloseDemandS.lean), and nothing on the
plans with one splitting.
`p.Plain` asks only that κ° and κ_c stand in oracle messages other than those that the row which
each splits reads (κ°: Ω, G_u; κ_c: Ω, W), and that Rs₀, Rs₁ hold the places of the vectors and the
mask entry (Rs₀: lO, lU, κ°; Rs₁: lO, lW, κ_c): less than the write-up's "mask-only message:
no main rows, a sample and a pad of its own"; it is enough for what is stated here. The order of the
four tests (the shared ones first) and "both splittings before all tests" are a choice for one
instance; in a batch the instance's splitting comes behind the shared tests
(Cb/Ld/LdLinClosePlanT.lean).
The rows, the splitting of a row on two groups and the shared part restate, in our own words, the
technical report (lean/CREDITS.md); the second splitting is added in this library's Lean text.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdLinClosePlanProofs
import Cb.Ld.LdLinCloseSplit
import Cb.Req1.LdSegCloseProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The plan with two splittings: the data. -/
structure LdLinPs {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) where
  GU  : Grp C.S
  GO  : Grp C.S
  GcO : Grp C.S
  GcW : Grp C.S
  hU  : GU.mem C.nU
  hO  : GO.mem C.nO
  hcO : GcO.mem C.nO
  hcW : GcW.mem C.nW
  /-- the shared mask entry; the instance's -/
  k₀  : SplitAt GO GU
  k₁  : SplitAt GcO GcW
  /-- the entries that the two splittings read -/
  Rs₀ : C.S.Ent → Prop
  [dRs₀ : DecidablePred Rs₀]
  Rs₁ : C.S.Ent → Prop
  [dRs₁ : DecidablePred Rs₁]
  /-- what is kept at the four bridges -/
  kp₁ : C.S.O → Prop
  [dKp₁ : DecidablePred kp₁]
  kp₂ : (C.S.sub kp₁).O → Prop
  [dKp₂ : DecidablePred kp₂]
  kp₃ : ((C.S.sub kp₁).sub kp₂).O → Prop
  [dKp₃ : DecidablePred kp₃]
  kp₄ : (((C.S.sub kp₁).sub kp₂).sub kp₃).O → Prop
  [dKp₄ : DecidablePred kp₄]
  /-- "rest", as a form on the last group's message -/
  restG : Slf E C.Sta GcW.C.J

attribute [instance] LdLinPs.dRs₀ LdLinPs.dRs₁ LdLinPs.dKp₁ LdLinPs.dKp₂ LdLinPs.dKp₃ LdLinPs.dKp₄

/-- the names of the record's rows and of the columns -/
abbrev LdLinC.Brc {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) : Type := C.D.X.Z.S ⊕ Fin C.t

/-- their targets -/
def LdLinC.tgRC {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) (s : C.Sh6) : C.Brc → E
  | .inl z => C.D.X.tgt s.1.1.1 s.1.1.2.1 z
  | .inr i => s.1.2.2 i

namespace LdLinPs
variable {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y} (p : LdLinPs C)

/-- the oracle messages after each bridge -/
abbrev S₁ : Sig E := C.S.sub p.kp₁
abbrev S₂ : Sig E := p.S₁.sub p.kp₂
abbrev S₃ : Sig E := p.S₂.sub p.kp₃
abbrev S₄ : Sig E := p.S₃.sub p.kp₄

/-- the later groups, among the oracle messages that are left at their tests -/
abbrev G₂ : Grp p.S₁ := p.GO.sub p.kp₁
abbrev G₃ : Grp p.S₂ := (p.GcO.sub p.kp₁).sub p.kp₂
abbrev G₄ : Grp p.S₃ := ((p.GcW.sub p.kp₁).sub p.kp₂).sub p.kp₃

/-- All members of a later group are kept until its test. -/
structure Kept : Prop where
  o₁ : ∀ o, p.GO.mem o → p.kp₁ o
  c₁ : ∀ o, p.GcO.mem o → p.kp₁ o
  c₂ : ∀ a : p.S₁.O, p.GcO.mem a.1 → p.kp₂ a
  w₁ : ∀ o, p.GcW.mem o → p.kp₁ o
  w₂ : ∀ a : p.S₁.O, p.GcW.mem a.1 → p.kp₂ a
  w₃ : ∀ a : p.S₂.O, p.GcW.mem a.1.1 → p.kp₃ a

variable [Fintype Y] [Fintype κ] [Fintype J]

/-- the two parts of the fold's row -/
def fO : Slf E C.Sh6 p.GO.C.J :=
  p.GO.onMem C.nO p.hO (Slf.push C.lO fun s y => Alg.eqk s.2 (C.D.py y))
def fU : Slf E C.Sh6 p.GU.C.J :=
  p.GU.onMem C.nU p.hU
    (Slf.push (fun n : Y × (Fin C.D.klo → Bool) => C.lU (C.D.X.pl (C.D.lay n)))
      fun s n => -(Alg.eqk s.2 (C.D.py n.1) * Alg.eqk s.1.1.2.2 n.2))

/-- the two parts of the inner product -/
def dO : Slf E C.St6 p.GcO.C.J :=
  p.GcO.onMem C.nO p.hcO (Slf.push C.lO fun st y => C.g st.1.1.1.1 y)
def dW : Slf E C.St6 p.GcW.C.J :=
  p.GcW.onMem C.nW p.hcW (Slf.push C.lW fun st c => -Alg.eqk (C.D.pt st.1.1.2) c)

/-- the record's rows and the columns -/
def rc : ∀ _ : C.Brc, Slf E C.Sh6 p.GU.C.J
  | .inl z =>
    p.GU.onMem C.nU p.hU
      (Slf.push (fun j => C.lU (C.D.X.pl j)) fun s j => C.D.X.Z.mat s.1.1.1.1 z j)
  | .inr i => p.GU.onMem C.nU p.hU (Slf.push C.lU fun s k => C.D.X.G (s.1.2.1 i) k)

/-- the evaluation -/
def ev : Slf E C.St6 p.GcW.C.J :=
  (p.GcW.onMem C.nW p.hcW (Slf.push C.lW fun st c => Alg.eqk (C.D.pt (C.ψ st.1.1.1.1)) c)).plus
    fun st => p.restG st.1.1.1.1

/-- what is claimed beside the two rows on two groups -/
abbrev Ar :
    IOR.Rels Unit (((C.Brc → E) × (C.Brc → C.Sh6)) × ((E × C.St6) × C.Sta))
      C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.rc x (p.GU.msg m))
    (claimRels (fun x m => p.ev.Holds x (p.GcW.msg m)) (onMsgRels C.aM C.Ab))

/-- The rows that are left, unsplit: the stage at which the front starts. -/
@[reducible] def x : FSt C.S C.E₀ C.Wpa Unit :=
  ⟨_, claimRels (splitIn p.fO p.fU) (claimRels (splitIn p.dO p.dW) p.Ar)⟩

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- its explicit part -/
def _root_.Cb.LdLinC.fqS (C : LdLinC E ι κ J Y) (st : C.St6) :
    (E × (C.Sh6 × C.Sh6)) ×
      ((E × (C.St6 × C.St6)) × (((C.Brc → E) × (C.Brc → C.Sh6)) × ((E × C.St6) × C.Sta))) :=
  ((0, (C.sh st, C.sh st)),
    ((0, (st, st)), ((C.tgRC (C.sh st), fun _ => C.sh st), ((C.τ st.1.1.1.1, st), st.1.1.1.1))))

/-- The rows of the four tests. -/
def r₁ : ∀ _ : C.Brc ⊕ Unit, Slf E C.Sh6 p.GU.C.J
  | .inl b => p.rc b
  | .inr _ => p.fU.addAt (-1) p.k₀.e₂
def r₂ : ∀ _ : Unit, Slf E C.Sh6 p.G₂.C.J := fun _ => (p.fO.addAt 1 p.k₀.e₁).toSub p.kp₁
def r₃ : ∀ _ : Unit, Slf E C.St6 p.G₃.C.J := fun _ =>
  ((p.dO.addAt 1 p.k₁.e₁).toSub p.kp₁).toSub p.kp₂
def r₄ : ∀ _ : LinB₂, Slf E C.St6 p.G₄.C.J
  | .inl _ => ((p.ev.toSub p.kp₁).toSub p.kp₂).toSub p.kp₃
  | .inr _ => (((p.dW.addAt (-1) p.k₁.e₂).toSub p.kp₁).toSub p.kp₂).toSub p.kp₃

/-- the explicit part in front of the four tests -/
abbrev StB (St' : Type) : Type :=
  ((C.Brc ⊕ Unit → E) × (C.Brc ⊕ Unit → C.Sh6)) ×
    (((Unit → E) × (Unit → C.Sh6)) ×
      (((Unit → E) × (Unit → C.St6)) × (((LinB₂ → E) × (LinB₂ → C.St6)) × St')))

/-- The base joint in front of the four tests. -/
abbrev base {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) :
    IOR.Rels Unit (StB (C := C) St') C.E₀ (C.S.Msg × C.Wpa) :=
  claimRels (fun x m => Slf.All p.r₁ x (p.GU.msg m))
    (onMsgRels (C.S.res (T := OMsg.Msg) p.kp₁)
      (claimRels (fun x m => Slf.All p.r₂ x (p.G₂.msg m))
        (onMsgRels (p.S₁.res (T := OMsg.Msg) p.kp₂)
          (claimRels (fun x m => Slf.All p.r₃ x (p.G₃.msg m))
            (onMsgRels (p.S₂.res (T := OMsg.Msg) p.kp₃)
              (claimRels (fun x m => Slf.All p.r₄ x (p.G₄.msg m))
                (onMsgRels (p.S₃.res (T := OMsg.Msg) p.kp₄) B')))))))

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- the messages that are kept to the end -/
def last (m : C.S.Msg) : p.S₄.Msg :=
  p.S₃.res (T := OMsg.Msg) p.kp₄
    (p.S₂.res (T := OMsg.Msg) p.kp₃
      (p.S₁.res (T := OMsg.Msg) p.kp₂ (C.S.res (T := OMsg.Msg) p.kp₁ m)))

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- B' says Ab. -/
structure SaysA {St' : Type} (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St') :
    Prop where
  fwd : ∀ sa y m wp, C.Ab.rel sa y (C.aM m, wp) → B'.rel (fa sa) y (p.last m, wp)
  bwd : ∀ sa y m wp,
    C.Ab.on (sa, y) → B'.relR (fa sa, y) (p.last m, wp) → C.Ab.relR (sa, y) (C.aM m, wp)
  on  : ∀ sa y, C.Ab.on (sa, y) → B'.on (fa sa, y)
  core : ∀ m wp, B'.core (p.last m, wp) = C.Ab.core (C.aM m, wp)

/-- the explicit part beside the two rows on two groups -/
abbrev Str : Type := ((C.Brc → E) × (C.Brc → C.Sh6)) × ((E × C.St6) × C.Sta)

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- the first step: the two claims on two groups change places -/
def swp (s : ((E × C.Sh6) × (E × C.Sh6)) × ((E × (C.St6 × C.St6)) × Str (C := C))) :
    (E × (C.St6 × C.St6)) × (((E × C.Sh6) × (E × C.Sh6)) × Str (C := C)) :=
  (s.2.1, (s.1, s.2.2))

omit [Fintype Y] [Fintype κ] [Fintype J] in
/-- the last step: each row goes to its test -/
def fin {St' : Type} (fa : C.Sta → St')
    (s : ((E × C.St6) × (E × C.St6)) × (((E × C.Sh6) × (E × C.Sh6)) × Str (C := C))) :
    StB (C := C) St' :=
  ((Sum.elim s.2.2.1.1 fun _ => s.2.1.2.1, Sum.elim s.2.2.1.2 fun _ => s.2.1.2.2),
    (oneClaim s.2.1.1,
      (oneClaim s.1.1,
        ((Sum.elim (fun _ => s.2.2.2.1.1) fun _ => s.1.2.1,
            Sum.elim (fun _ => s.2.2.2.1.2) fun _ => s.1.2.2),
          fa s.2.2.2.2))))

variable [Fintype E]

/-- a step of a front that only maps the explicit part -/
def stepOf {x y : FSt C.S C.E₀ C.Wpa Unit} (q : Front x y)
    (z : FSt C.S C.E₀ C.Wpa Unit) (f : y.St → z.St) : Front x z :=
  .step q z (sideF C.S f) (sideG C.S (ExtMap.id C.E₀))
    (sideM C.S f fun _ w => w.2) (sideB C.S fun _ w => w.2)

/-- The front, move by move: `f₁`, `f₂`, `f₃`, `front`. -/
def f₁ :
    Front p.x ⟨_, claimRels (splitOut p.k₀ p.fO p.fU) (claimRels (splitIn p.dO p.dW) p.Ar)⟩ :=
  .split p.GO p.GU p.k₀ C.Sh6 C.Sh6 p.fO p.fU _ (claimRels (splitIn p.dO p.dW) p.Ar)
    p.Rs₀ inferInstance (.nil p.x)

def f₂ :
    Front p.x ⟨_, claimRels (splitIn p.dO p.dW) (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar)⟩ :=
  stepOf p.f₁ _ swp

def f₃ :
    Front p.x ⟨_, claimRels (splitOut p.k₁ p.dO p.dW) (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar)⟩ :=
  .split p.GcO p.GcW p.k₁ C.St6 C.St6 p.dO p.dW _ (claimRels (splitOut p.k₀ p.fO p.fU) p.Ar)
    p.Rs₁ inferInstance p.f₂

def front {St' : Type}
    (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St') :
    Front p.x ⟨_, p.base B'⟩ :=
  stepOf p.f₃ _ (fin fa)

omit [Fintype Y] [Fintype κ] [Fintype J] [Fintype E] in
/-- The two mask entries stand in oracle messages other than those that the row which each splits
reads (`ne₀O`, `ne₀U`, `ne₁O`, `ne₁W`); what the splittings read. -/
structure Plain : Prop where
  ne₀O : p.k₀.o ≠ C.nO
  ne₀U : p.k₀.o ≠ C.nU
  ne₁O : p.k₁.o ≠ C.nO
  ne₁W : p.k₁.o ≠ C.nW
  rs₀O : ∀ y, p.Rs₀ ⟨C.nO, C.lO y⟩
  rs₀U : ∀ k, p.Rs₀ ⟨C.nU, C.lU k⟩
  rs₀K : p.Rs₀ ⟨p.k₀.o, p.k₀.j⟩
  rs₁O : ∀ y, p.Rs₁ ⟨C.nO, C.lO y⟩
  rs₁W : ∀ c, p.Rs₁ ⟨C.nW, C.lW c⟩
  rs₁K : p.Rs₁ ⟨p.k₁.o, p.k₁.j⟩

end LdLinPs

namespace Spec
section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States: if `restG` is "rest", the unsplit stage says the rows and Ab. -/
def ldLinPs_says : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C),
    (∀ sa m, p.restG.val sa (p.GcW.msg m) = C.rest sa (C.aM m)) → C.Says p.x.A C.fqS

/-- The hypotheses of the front's moves, from `p.Plain`, `p.Kept` and `p.SaysA B' fa`. -/
def ldLinPs_hyp : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St'),
    p.Plain → p.Kept → p.SaysA B' fa → (p.front B' fa).prog.Hyp

/-- States: every step of the front has the budgets' half. -/
def ldLinPs_sd : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St')
      (q : Finset (C.E₀.prod C.S.ext).Pos → Prop),
    (p.front B' fa).Sd q

/-- What is asked for the splittings, from the two facts on fresh masks.
(not all hypotheses are named here: see the statement below) -/
def ldLinPs_zk : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (St' : Type)
      (B' : IOR.Rels Unit St' C.E₀ (p.S₄.Msg × C.Wpa)) (fa : C.Sta → St') (Rd : C.S.Ent → Prop)
      (Rr : C.S.O → Prop) (bs : MaskFact p.x.stage.J.W → Prop),
    p.Plain → (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) ≠ ⟨p.k₁.o, p.k₁.j⟩ → (∀ n, p.Rs₀ n → Rd n) →
    (∀ n, p.Rs₁ n → Rd n) →
    bs (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u) →
    bs (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u) →
    (p.front B' fa).ZkOK Rd Rr bs

end
end Spec
end Cb
