-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTowerThird.lean: without hypotheses on lists or agreement: a concrete tower, any
number of stages, all of whose radii lie within a third of the distances.

In standard terms: the proximity test of Cb/Obj/LdObjectTower.lean where every proximity parameter
is below a third of the minimum distance. There, for codes that have their laws, lists have at most
one member and mutual correlated agreement has at most e + 1 exceptions, both by theorems
(Cb/Ld/LdTowerThird.lean), so neither is assumed.

Definitions, statements and proofs.
No file proves bounds on lists and on agreement beyond a third of the distance, but for some cases.
Among them are lists below the Johnson radius (`ld_list_johnson`, Cb/Ld/LdRelJohnsonProofs.lean),
agreement of Reed-Solomon codes within half the distance (Cb/Gl/GlAgreeHalf.lean), and a weak bound
on agreement at every radius, on which no parameter of a real protocol can rest (`ld_mca_sets`,
Cb/Ld/LdRelAny.lean). Bounds on lists and on agreement are among the blocks' own hypotheses, under
which a concrete tower (`LdTowC`, Cb/Obj/LdObjectTower.lean) is a tail of a chain.
Lists: `LdCode.ListAt`; agreement: `LdCode.MCAat` (both in Cb/Ld/LdRel.lean); tail of a chain:
`LdEnd.OK` (Cb/Ld/LdTower.lean).

Main names:
  `LdTow3 a`: as `LdTowC`, without the numbers for lists and agreement; with a distance d of each
    stage's three codes as read, a distance d' of each new code as read, a distance d of the last
    code.
  `T.toC`: the concrete tower: lists 1, agreement e + 1 at every stage of every fold; list 1 at
    every switch; (e + 1, 1) at the base case.
  `Y.Third d e t`, `D.Third d' e' t'`: what is asked of a fold and of a switch: laws; distances;
    3 e < d (fold), 2 e' < d' (switch); and what has nothing to do with lists: challenges are
    distinct, degree at least 2, the packing's law and degrees, the fresh mask's encoding hides t
    positions; the new code is read by its reading, sample and evader are what they should be, the
    sample is private, the new encoding hides t' positions.
  `T.Third`: by recursion; at the base case: laws, distance, 3 e < d, transparent.
  `Spec.ldTow3_tail`: `T.Third` → the whole test is a tail of a chain.
  `LdTowG3 G Sb sl Z`, `T.Third`, `Spec.ldTowG3_tail`: the same on a group's complex (`G.P`
    non-empty; in the case `shaped`: `Sh.OK` too).
  `Spec.ldTowG3_run`: one test on a group: `D.OK` from: its whole test is such a tower, its number
    of positions the tower's; D.L = 1; the members' codes at the group's positions have laws and a
    distance d with 2 G.e < d; the bridge's evader; Fits; `T.Third`. No clause on a list or on
    agreement is left.

The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. Here they are hypotheses: clauses of `Y.Third`, `D.Third`
and `T.Third`, and a premise of `Spec.ldTowG3_run`.

Limits: this file says nothing beyond a third of the distance (but for the lists of a switch's new
code and of a group's complex, which it has within half the distance: `LdSw.Third`,
`Spec.ldTowG3_run`).
That `T.Third` can be met is not shown in this file.
The errors are those of Cb/Ld/LdTowerThird.lean (`Spec.ldThird_err`), block by block, in a row; they
are not gathered into one list here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectTower
import Cb.Ld.LdTowerThird
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- A fold within a third of the distance. -/
structure SumPar.Third {E P : Type} [Field E] [Fintype E] [Fintype P] (Y : SumPar E P) (d e t : ℕ) :
    Prop where
  lawsC : Y.C.Laws
  lawsZ : Y.Z.Laws
  lawsW : Y.Zw.Laws
  distC : Y.C.Dist d
  distZ : Y.Z.Dist d
  distW : Y.Zw.Dist d
  third : 3 * e < d
  inj   : Function.Injective Y.val
  deg   : 2 ≤ Y.n
  pack  : Y.PackOK
  qw    : Y.QwDeg
  zk    : Y.Cw.Zk t

/-- A code switch into a code that is uniquely decoded at the new radius. -/
structure LdSw.Third {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
    [Nonempty P'] (D : LdSw E P P' St) (d' e' t' : ℕ) : Prop where
  lawsO : D.Cout.Laws
  distO : D.Cout.Dist d'
  half  : 2 * e' < d'
  lawsI : D.Cin.Laws
  reads : D.Cout.Reads
  okO   : D.Zo.OK
  okB   : D.Zb.OK
  priv  : D.Zo.PrivateSim E
  zk    : D.Cout.Zk t'

/-- A tower within a third of the distances: the data. -/
inductive LdTow3 {E : Type} [Field E] [Fintype E] : LdJoint E → Type 1
  | base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d : ℕ) : LdTow3 a
  | step {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (Y : SumPar E P) (sl : Slf E St Y.Cin.J) (e : ℕ) (S : LdSwD (Y.reform sl) P')
      (d e' d' : ℕ) (rest : LdTow3 ((S.D e).jOut e')) :
      LdTow3 (ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)

namespace LdTow3
variable {E : Type} [Field E] [Fintype E]

/-- The concrete tower. -/
def toC : {a : LdJoint E} → LdTow3 a → LdTowC a
  | _, .base a t cov d => .base a t cov d (a.e + 1) 1
  | _, @LdTow3.step _ _ _ _ _ _ _ _ _ _ Y sl e S d e' _ rest =>
    .step Y sl e S d (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) e' 1 rest.toC

/-- All radii within a third of the distances. -/
def Third : {a : LdJoint E} → LdTow3 a → Prop
  | _, .base a _ _ d => a.C.Laws ∧ a.C.Dist d ∧ 3 * a.e < d ∧ a.C.Transparent
  | _, @LdTow3.step _ _ _ _ _ _ _ _ _ _ Y sl e S d e' d' rest =>
    (Y.reform sl).Third d e S.ts ∧ (S.D e).Third d' e' rest.toC.q ∧ rest.Third

end LdTow3

/-- The same on a group's complex: the data. -/
inductive LdTowG3 {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S)
    [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) : Type 1
  | plain (T : LdTow3 (G.joint Sb sl Z)) : LdTowG3 G Sb sl Z
  | shaped {P' : Type} [Fintype P'] [Nonempty P'] (Sh : GShape G) (Sw : LdSwD (Sh.fold Sb sl Z) P')
      (d e' d' : ℕ) (rest : LdTow3 ((Sw.D G.e).jOut e')) : LdTowG3 G Sb sl Z

namespace LdTowG3
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

def toG : LdTowG3 G Sb sl Z → LdTowG G Sb sl Z
  | .plain T => .plain T.toC
  | @LdTowG3.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d e' _ rest =>
    .shaped Sh Sw d (fun _ => 1) (fun _ => G.e + 1) (fun _ => G.e + 1)
      (fun _ => G.e + 1) e' 1 rest.toC

def Third : LdTowG3 G Sb sl Z → Prop
  | .plain T => T.Third
  | @LdTowG3.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d e' d' rest =>
    Sh.OK ∧ Sh.par.Third d G.e Sw.ts ∧ (Sw.D G.e).Third d' e' rest.toC.q ∧ rest.Third

end LdTowG3

namespace Spec

def ldTow3_hyp : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTow3 a), T.Third → T.toC.Hyp

/-- States: a tower within a third of the distances is a tail of a chain: from laws and distances
and what else `T.Third` asks, no hypothesis on lists or agreement. -/
def ldTow3_tail : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTow3 a),
    T.Third → T.toC.toEnd.OK T.toC.q

def ldTowG3_tail : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowG3 G Sb sl Z),
    T.Third → T.toG.toEnd.OK T.toG.q

/-- One test on a group, within a third. -/
def ldTowG3_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S)
      (T : LdTowG3 D.G D.Sb D.sl D.Z) (d : ℕ),
    D.T = T.toG.toEnd → D.t = T.toG.q → D.L = 1 →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws) →
    (∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d) →
    2 * D.G.e < d → D.Z.OK → D.G.Fits → T.Third → D.OK

end Spec

theorem SumPar.Third.hyp {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e t : ℕ} (h : Y.Third d e t) :
    Y.Hyp d e t (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) :=
  ldThird_fold E P Y d e t h.lawsC h.lawsZ h.lawsW h.distC h.distZ h.distW h.third
    h.inj h.deg h.pack h.qw h.zk

theorem LdSw.Third.hyp {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]
    [Fintype P'] [Nonempty P'] {D : LdSw E P P' St} {d' e' t' : ℕ} (h : D.Third d' e' t') :
    D.Hyp e' 1 t' :=
  ldThird_switch E P P' St D d' e' t' h.lawsO h.distO h.half h.lawsI h.reads h.okO h.okB h.priv h.zk

theorem ldTow3_hyp : Spec.ldTow3_hyp := by
  intro E _ _ a T
  induction T with
  | base a t cov d => exact fun h => ldThird_base E a d h.1 h.2.1 h.2.2.1 h.2.2.2
  | step Y sl e S d e' d' rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨h1.hyp, h2.hyp, ih h3⟩

theorem ldTow3_tail : Spec.ldTow3_tail := fun E _ _ a T h =>
  ldTowC_tail E a T.toC (ldTow3_hyp E a T h)

theorem ldTowG3_hyp {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
    [Nonempty G.P] {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}
    (T : LdTowG3 G Sb sl Z) (h : T.Third) : T.toG.Hyp := by
  cases T with
  | plain T => exact ldTow3_hyp E _ T h
  | shaped Sh Sw d e' d' rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1.hyp, h2.hyp, ldTow3_hyp E _ rest h3⟩

theorem ldTowG3_tail : Spec.ldTowG3_tail := fun E B _ _ _ S G _ Sb sl Z T h =>
  ldTowG_tail E B S G Sb sl Z T.toG (ldTowG3_hyp T h)

theorem ldTowG3_run : Spec.ldTowG3_run := fun E _ _ S D T d hT ht hL hl hd h2 hZ hF h =>
  ldTowG_run E S D T.toG hT ht hZ
    (by rw [hL]; exact ldThird_bridge E S D.G d hl hd h2) hF (ldTowG3_hyp T h)

end Cb
