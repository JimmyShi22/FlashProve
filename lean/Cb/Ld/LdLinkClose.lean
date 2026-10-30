-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkClose.lean: a last part (a closing, as a chain) for the interactive oracle reduction of
Cb/Ld/LdLink.lean: the linear claims that its first part leaves on the messages of the oracles sent
are batched into one claim, and one proximity test with that claim ends the protocol.

Definitions and statements; the proofs are in Cb/Ld/LdLinkCloseProofs.lean. It builds on
Cb/Ld/LdLink.lean, Cb/Ld/LdLinkChain.lean (the link: its last joint `j4`, its core as a chain),
Cb/Ld/LdLinCloseChain.lean (whole tests on groups as links of a chain) and
Cb/Ld/LdLinCloseForms.lean (rows as forms).
A form (`Slf E St J`) gives, for each state in St, the coefficients of a linear form on vectors
J → E; a row claims that a form at its state has its target as value (`Slf.All`, Cb/Ld/LdBat.lean).
A zero-evader (`Evader`, Cb/Gen/BatEvader.lean) is a seeded family of coefficient vectors with a
number `err`; it evades (`Evader.OK`, a hypothesis, not a field) if at most `err` seeds annihilate
any given vector other than 0: with it many linear claims are batched into one.

What the core leaves (`j4`). A family N of oracle messages with their samples; two named members
(`i₀`, `i₁`; G_u0 and G_u1 below) hold, at the places l₀ and l₁, the folded full messages u₀ and u₁
of the two encoded indices.

The rows as forms (`P.rows G all`). G: a group that holds all members of N.
  record's row s of the first index: state: the record's seed; coefficients: row s of the index's
    sample map, at the places of the message part of u₀; target: the folded answer.
  column i of the first index: state: the i-th drawn location; coefficients: the row of the
    generator matrix at that location, on all of u₀; target: the fold of the column read.
  the same two kinds for the further index, on u₁.
  the equality row: state: φ; coefficients: the equality kernel at φ on the layout's places of u₀,
    minus the same on those of u₁; target: 0.
All targets are public. The sample rows of all members of N are added by the bridge
(Cb/Ld/LdBatSig.lean), not here.

The closing (`P.Cl`: the data; `K.cZ d`: the chain). No splitting: no row lies on two groups. Three
links:
  `lStep`, no round: the explicit part is replaced by what is computed from it: (targets and states
    of the rows; the samples); the words are copied.
  the test, T's rounds + 1: the bridge (all rows and all sample rows into one form; seed of a
    zero-evader), then any whole proximity test T on the group's complex (an end block of
    Cb/Ld/LdTower.lean); nothing is kept: all members leave the statement. Its errors, in a row:
    `K.L` · `K.Z.err`, then T's (`LdRunD.link`, Cb/Ld/LdLinCloseChain.lean; `Spec.ldClose_run_data`,
    Cb/Ld/LdLinCloseRun.lean).
  the end, no round: no oracle message is left.

Main names:
  `K.OK`: what the test asks (`LdRunD.OK`, Cb/Ld/LdLinCloseRuns.lean): the evader evades; the
    complex has lists of at most L members at the joint radius; the joint radius implies each
    member's own; T is a tail that needs at most t long positions.
  `Spec.ldLkC_chain`: `K.OK`, and t is at most what every member's encoding bears ⇒ the closing
    stands behind every chain (`OkFrom`) and has the budgets' halves from the core's demand `q3`
    (`SidesCT`).
  `Spec.ldLkC_tail`: so the link with this closing, `P.linkC` at `K.cZ d`, is a tail from the claim
    on the two encoded indices (`P.j0 on0 on1`: on the statements with the conditions `on0`, `on1`)
    to the trivial statement (`ldLc_tail`, Cb/Ld/LdLinkChain.lean), from the core's hypotheses
    (`P.FoldErr on0 on1 ε₀ ε₁`, `P.D.pl` injective, `S.OK`; ι is not empty), `K.OK`, and
    `K.t ≤ S.t a` for every member a.
In every `K : P.Cl` the type `K.G.P` of common long positions is not empty (field `neP`).

`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Limits: no test T is given here (Cb/Ld/LdTower*.lean); no bound on a list. This file says nothing on
batches.
Declared differences to a note of ours that is not in this repository. The note puts G_u0 and G_u1
into one group of one code;
here the group is any common reading of all members of the family (Cb/Ld/LdBatSig.lean (a)); further
members of N, if any, are closed by the same test.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinkChain
import Cb.Ld.LdLinCloseChain
import Cb.Ld.LdLinCloseForms
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLkP
variable {E ι κ J Λ : Type} (P : LdLkP E ι κ J Λ)

/-- The names of the rows: record's rows and columns of the first index; of the further one; the
equality row. -/
abbrev RowB : Type := (P.D.X.Z.S ⊕ Fin P.t₀) ⊕ ((P.D.X.Z.S ⊕ Fin P.t₁) ⊕ Unit)

/-- The states of the rows. -/
def RowS : P.RowB → Type
  | .inl (.inl _) => P.D.X.Z.D
  | .inl (.inr _) => ι
  | .inr (.inl (.inl _)) => P.D.X.Z.D
  | .inr (.inl (.inr _)) => ι
  | .inr (.inr _) => Fin P.D.l → E

variable [Field E]

/-- The three kinds of forms, on the message of a member i that holds a folded full message at the
places l. -/
def recF [Fintype J] (i : P.N.O) (l : κ → (P.N.om i).C.J) (s : P.D.X.Z.S) :
    Slf E P.D.X.Z.D (P.N.om i).C.J :=
  Slf.push (fun j => l (P.D.X.pl j)) fun ρ j => P.D.X.Z.mat ρ s j
def colF [Fintype κ] (i : P.N.O) (l : κ → (P.N.om i).C.J) : Slf E ι (P.N.om i).C.J :=
  Slf.push l fun x k => P.D.X.G x k
def layF [Fintype Λ] (i : P.N.O) (l : κ → (P.N.om i).C.J) : Slf E (Fin P.D.l → E) (P.N.om i).C.J :=
  Slf.push (fun a => l (P.D.X.pl (P.D.lay a))) fun φ a => Alg.eqk φ (P.D.pl a)

variable [Fintype κ] [Fintype J] [Fintype Λ]

/-- The rows as forms on the message of the complex of a group that holds all members. -/
def rows (G : Grp P.N) (all : ∀ o, G.mem o) : ∀ b, Slf E (P.RowS b) G.C.J
  | .inl (.inl s) => G.onMem P.i₀ (all _) (P.recF P.i₀ P.l₀ s)
  | .inl (.inr _) => G.onMem P.i₀ (all _) (P.colF P.i₀ P.l₀)
  | .inr (.inl (.inl s)) => G.onMem P.i₁ (all _) (P.recF P.i₁ P.l₁ s)
  | .inr (.inl (.inr _)) => G.onMem P.i₁ (all _) (P.colF P.i₁ P.l₁)
  | .inr (.inr _) => (G.onMem P.i₀ (all _) (P.layF P.i₀ P.l₀)).sub (G.onMem P.i₁ (all _) (P.layF P.i₁ P.l₁))

/-- Targets and states, read off the explicit part. The parts of x: `x.1.1.1.1`: the two records (a
record's first part is its seed); `x.1.1.1.2`: γ; `x.1.1.2`: the samples; `x.1.2.1`, `x.1.2.2`: the
drawn locations and the folds of the columns read, of the first index and of the further one;
`x.2`: φ. -/
def claims (x : P.X4) : (P.RowB → E) × (∀ b, P.RowS b) :=
  (fun b => match b with
    | .inl (.inl s) => P.D.X.tgt x.1.1.1.1.1 x.1.1.1.2 s
    | .inl (.inr i) => x.1.2.1.2 i
    | .inr (.inl (.inl s)) => P.D.X.tgt x.1.1.1.1.2 x.1.1.1.2 s
    | .inr (.inl (.inr i)) => x.1.2.2.2 i
    | .inr (.inr _) => 0,
   fun b => match b with
    | .inl (.inl _) => x.1.1.1.1.1.1
    | .inl (.inr i) => x.1.2.1.1 i
    | .inr (.inl (.inl _)) => x.1.1.1.1.2.1
    | .inr (.inl (.inr i)) => x.1.2.2.1 i
    | .inr (.inr _) => x.2)

variable [Fintype E]

/-- The closing: the data. -/
structure Cl where
  /-- the one group: all members of the family, read at common long positions, with a joint
  radius -/
  G   : Grp P.N
  [neP : Nonempty G.P]
  all : ∀ o, G.mem o
  /-- the zero-evader of the bridge -/
  Z   : Evader E (G.Row P.RowB)
  /-- the whole test on the complex -/
  T   : LdEnd (G.joint P.RowS (P.rows G all) Z)
  L   : ℕ
  t   : ℕ

attribute [instance] Cl.neP

variable {P}

/-- The test, as a record `LdRunD` of Cb/Ld/LdLinCloseRuns.lean: nothing is kept. -/
@[reducible] def Cl.run (K : P.Cl) : LdRunD P.N :=
  { G := K.G, kp := fun _ => False, decKp := fun _ => instDecidableFalse,
    hc := fun o => Or.inl (K.all o), B := P.RowB, Sb := P.RowS, sl := P.rows K.G K.all, Z := K.Z,
    T := K.T, L := K.L, t := K.t }

/-- What is asked of the closing. -/
def Cl.OK (K : P.Cl) : Prop := K.run.OK

/-- The tests as a chain: the one test, then nothing is left. d: values of extractors where nothing
was output. -/
def Cl.tc (K : P.Cl) (d : P.W2) : LdTc P.N extNone P.W0 :=
  LdTc.cons K.run (LdTc.nil (P.N.sub fun _ => False) extNone P.W0 (fun a => a.2.elim, d.2))
    d (K.G.wit d.1, (fun a => a.2.elim, d.2))

variable (P)

/-- The step without rounds: explicit part, oracles. -/
def stepF (x : P.X4) : ((((P.RowB → E) × (∀ b, P.RowS b)) × Unit) × P.N.Smp) :=
  ((P.claims x, ()), x.1.1.2)
def stepG : ExtMap P.E3 (extNone.prod P.N.ext) := (ExtMap.toNone _).pair (ExtMap.id _)

variable {P}

/-- The step without rounds, as a link. -/
def Cl.lStep (K : P.Cl) (d : P.W2) : Link Unit P.J4 (P.N.jointCf (K.tc d).base) :=
  ⟨IOR.pure (fun x => some (P.stepF x)) P.stepG,
    IOR.Honest.pure _ _ fun a => (P.stepF a.1, a.2),
    fun _ _ w => w,
    IOR.Nums.pure Unit _ _⟩

/-- The closing of the link, as a chain. -/
def Cl.cZ (K : P.Cl) (d : P.W2) : Chain Unit P.J4 ldJT :=
  (Chain.one (K.lStep d)).append (K.tc d).c

end LdLkP

namespace Spec
section
variable (E ι κ J Λ : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

/-- The forms say what the core's rows say. -/
def ldLkC_rows : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (G : Grp P.N) (all : ∀ o, G.mem o) (x : P.X4) (m : P.N.Msg),
    Slf.All (P.rows G all) (P.claims x) (G.msg m) ↔ P.Rows x (P.uv₀ m) (P.uv₁ m)

/-- The step without rounds is a piece of a chain, if `K.t ≤ S.t a` for every member a. -/
def ldLkC_step : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (K : P.Cl) (d : P.W2) (S : P.Snd), (∀ a, K.t ≤ S.t a) →
    PieceTr (K.lStep d).R (K.lStep d).H P.j4 (P.N.over (K.tc d).base) (K.lStep d).ext
      (K.lStep d).P (P.q3 S) (K.tc d).q

/-- Under the hypotheses below: the closing stands behind every chain, and its budgets fit the
core's. -/
def ldLkC_chain : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (K : P.Cl) (d : P.W2) (S : P.Snd)
      (A : Joint Unit) (c₀ : Chain Unit A P.J4),
    K.OK → (∀ a, K.t ≤ S.t a) → (K.cZ d).OkFrom c₀ ∧ (K.cZ d).SidesCT (P.q3 S)

/-- For ι not empty and under the hypotheses below: the link with this closing is a tail. -/
def ldLkC_tail : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ) (S : P.Snd)
      (K : P.Cl) (d : P.W2) (d₀ : P.W0),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK → K.OK → (∀ a, K.t ≤ S.t a) →
    TailTr (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d) d₀).R (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d) d₀).H
      (P.j0 on0 on1) trivRels (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d) d₀).ext
      (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d) d₀).P P.q0

end
end Spec
end Cb
