-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectTowerJohn.lean: towers below the Johnson radius: under `T.John` a whole test (cut,
fold, switch, .., base case) is a tail of a chain with no hypothesis on lists; agreement is asked of
the codes in the records only, whatever the number of rows (`MCArows`; at the base case `MCAat`).

In standard terms: the proximity test of Cb/Obj/LdObjectTower.lean below the Johnson radius. List
sizes are bounded by the Johnson bound, a theorem; mutual correlated agreement of the codes stays a
hypothesis.

Definitions, statements (`Cb.Spec.ldTowJ_hyp` to `Cb.Spec.ldTowGJ_run`) and proofs (an assembly).
Generic: any finite field, any codes; no assumed theorem. For radii beyond a third of the distances,
on the blocks of
Cb/Ld/LdTowerJohn.lean. Lists: `LdCode.ListAt`; agreement: `LdCode.MCAat` (both in
Cb/Ld/LdRel.lean).

Main names:
  `Y.John d e t bC bZ bW`: a fold: the three codes: laws, distance d as read; e below the Johnson
    radius (`InJohnson` |P| d e); agreement whatever the number of rows (`MCArows e b`,
    Cb/Ld/LdRelRows.lean) with counts bC, bZ, bW; and what does not speak of codes' lists or
    agreement: challenges, degree, packing, the fresh mask's encoding.
  `D.John d' e' t'`: a code switch: the new code: laws, distance d', e' below its Johnson radius: no
    agreement is asked; the remaining clauses as in `LdSw.Third`.
  `LdTowJ a`, `LdTowGJ G ..`: the data of a tower, of a tower on a group's complex (`G.P`
    non-empty): as `LdTow3`, `LdTowG3`, with the counts of agreement as data (b at the base case;
    bC, bZ, bW at a fold). The bounds on lists are no data: they are `listMax` |P| d e at every
    joint.
  `T.John`: by recursion: each fold, each switch; the base case: laws, distance, below the Johnson
    radius, `a.C.MCAat a.e b`, transparent; on a group's complex, in the case `shaped`: `Sh.OK` too.
  `Spec.ldTowJ_hyp`, `Spec.ldTowJ_tail`, `Spec.ldTowGJ_tail`: `T.John` ⇒ the blocks' own hypotheses
    ⇒ the whole test is a tail of a chain.
  `D.TowJ`, `D.PreJ T d`: one test on a group with the tower T (its fields: see the record): its
    list bound is `listMax` |G.P| d G.e; the members' codes as read at the group's positions: laws,
    distance d.
  `Spec.ldTowGJ_run`: `D.PreJ T d` ⇒ `D.Pre T.toG` (Cb/Obj/LdObjectTowers.lean), so `D.OK`.

Limits: this file does not say that any code has `MCArows` beyond a third (Cb/Gl/GlLdJ.lean:
Reed-Solomon families, under a hypothesis by name), or that the errors are small. It says nothing
between the Johnson radius and capacity.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectTowers
import Cb.Ld.LdTowerJohn
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- A fold below the Johnson radius. -/
structure SumPar.John {E P : Type} [Field E] [Fintype E] [Fintype P]
    (Y : SumPar E P) (d e t bC bZ bW : ℕ) : Prop where
  lawsC : Y.C.Laws
  lawsZ : Y.Z.Laws
  lawsW : Y.Zw.Laws
  distC : Y.C.Dist d
  distZ : Y.Z.Dist d
  distW : Y.Zw.Dist d
  john  : InJohnson (Fintype.card P) d e
  mcaC  : Y.C.MCArows e bC
  mcaZ  : Y.Z.MCArows e bZ
  mcaW  : Y.Zw.MCArows e bW
  inj   : Function.Injective Y.val
  deg   : 2 ≤ Y.n
  pack  : Y.PackOK
  qw    : Y.QwDeg
  zk    : Y.Cw.Zk t

/-- A code switch into a code whose new radius lies below its Johnson radius. -/
structure LdSw.John {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
    [Nonempty P'] (D : LdSw E P P' St) (d' e' t' : ℕ) : Prop where
  lawsO : D.Cout.Laws
  distO : D.Cout.Dist d'
  john  : InJohnson (Fintype.card P') d' e'
  lawsI : D.Cin.Laws
  reads : D.Cout.Reads
  okO   : D.Zo.OK
  okB   : D.Zb.OK
  priv  : D.Zo.PrivateSim E
  zk    : D.Cout.Zk t'

/-- A tower below the Johnson radius: the data. -/
inductive LdTowJ {E : Type} [Field E] [Fintype E] : LdJoint E → Type 1
  | base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d b : ℕ) : LdTowJ a
  | step {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (Y : SumPar E P) (sl : Slf E St Y.Cin.J) (e : ℕ) (S : LdSwD (Y.reform sl) P')
      (d bC bZ bW e' d' : ℕ) (rest : LdTowJ ((S.D e).jOut e')) :
      LdTowJ (ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)

namespace LdTowJ
variable {E : Type} [Field E] [Fintype E]

/-- The concrete tower: the bounds on lists are the Johnson bounds. -/
def toC : {a : LdJoint E} → LdTowJ a → LdTowC a
  | _, .base a t cov d b => .base a t cov d b (listMax (Fintype.card a.P) d a.e)
  | _, @LdTowJ.step _ _ _ P P' _ _ _ _ _ Y sl e S d bC bZ bW e' d' rest =>
      .step Y sl e S d (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ)
        (fun _ => bW) e' (listMax (Fintype.card P') d' e') rest.toC

/-- All radii below the Johnson radii. -/
def John : {a : LdJoint E} → LdTowJ a → Prop
  | _, .base a _ _ d b =>
    a.C.Laws ∧ a.C.Dist d ∧ InJohnson (Fintype.card a.P) d a.e ∧ a.C.MCAat a.e b ∧ a.C.Transparent
  | _, @LdTowJ.step _ _ _ _ _ _ _ _ _ _ Y sl e S d bC bZ bW e' d' rest =>
    (Y.reform sl).John d e S.ts bC bZ bW ∧ (S.D e).John d' e' rest.toC.q ∧ rest.John

end LdTowJ

/-- The same on a group's complex: the data. -/
inductive LdTowGJ {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S)
    [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) : Type 1
  | plain (T : LdTowJ (G.joint Sb sl Z)) : LdTowGJ G Sb sl Z
  | shaped {P' : Type} [Fintype P'] [Nonempty P'] (Sh : GShape G) (Sw : LdSwD (Sh.fold Sb sl Z) P')
      (d bC bZ bW e' d' : ℕ) (rest : LdTowJ ((Sw.D G.e).jOut e')) : LdTowGJ G Sb sl Z

namespace LdTowGJ
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

def toG : LdTowGJ G Sb sl Z → LdTowG G Sb sl Z
  | .plain T => .plain T.toC
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ P' _ _ Sh Sw d bC bZ bW e' d' rest =>
      .shaped Sh Sw d (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC) (fun _ => bZ)
        (fun _ => bW) e' (listMax (Fintype.card P') d' e') rest.toC

def John : LdTowGJ G Sb sl Z → Prop
  | .plain T => T.John
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d bC bZ bW e' d' rest =>
    Sh.OK ∧ Sh.par.John d G.e Sw.ts bC bZ bW ∧ (Sw.D G.e).John d' e' rest.toC.q ∧ rest.John

end LdTowGJ

/-- a tower below the Johnson radius on the complex of the test's group -/
abbrev LdRunD.TowJ {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : Type 1 :=
  LdTowGJ D.G D.Sb D.sl D.Z

/-- as a concrete tower on the test's complex -/
def LdRunD.upJ
    {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (T : D.TowJ) : D.Tow := T.toG

/-- What is asked of one test with the tower T, below the Johnson radius of the group's complex. -/
structure LdRunD.PreJ {E : Type} [Field E] [Fintype E] {S : Sig E}
    (D : LdRunD S) (T : D.TowJ) (d : ℕ) : Prop where
  isT  : D.T = T.toG.toEnd
  isQ  : D.t = T.toG.q
  isL  : D.L = listMax (Fintype.card D.G.P) d D.G.e
  laws : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Laws
  dist : ∀ a : D.G.A, ((S.om a.1).C.atPos (D.G.pos a)).Dist d
  john : InJohnson (Fintype.card D.G.P) d D.G.e
  ev   : D.Z.OK
  fits : D.G.Fits
  tow  : T.John

namespace Spec

def ldTowJ_hyp : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.John → T.toC.Hyp

/-- States, under `T.John`: a tower below the Johnson radius is a tail of a chain: no hypothesis on
lists. -/
def ldTowJ_tail : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (T : LdTowJ a), T.John → T.toC.toEnd.OK T.toC.q

def ldTowGJ_tail : Prop :=
  ∀ (E B : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    T.John → T.toG.toEnd.OK T.toG.q

/-- One test on a group, below the Johnson radius. -/
def ldTowGJ_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (T : D.TowJ) (d : ℕ),
    D.PreJ T d → D.Pre (D.upJ T) ∧ D.OK

end Spec

theorem SumPar.John.hyp {E P : Type} [Field E] [Fintype E] [Fintype P] {Y : SumPar E P}
    {d e t bC bZ bW : ℕ} (h : Y.John d e t bC bZ bW) :
    Y.Hyp d e t (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW) :=
  ldJohn_fold E P Y d e t bC bZ bW h.lawsC h.lawsZ h.lawsW h.distC h.distZ h.distW h.john h.mcaC
    h.mcaZ h.mcaW h.inj h.deg h.pack h.qw h.zk

theorem LdSw.John.hyp {E P P' St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
    [Nonempty P'] {D : LdSw E P P' St} {d' e' t' : ℕ} (h : D.John d' e' t') :
    D.Hyp e' (listMax (Fintype.card P') d' e') t' :=
  ldJohn_switch E P P' St D d' e' t' h.lawsO h.distO h.john h.lawsI h.reads h.okO h.okB h.priv h.zk

theorem ldTowJ_hyp : Spec.ldTowJ_hyp := by
  intro E _ _ a T
  induction T with
  | base a t cov d b => exact fun h => ldJohn_base E a d b h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ⟨h1.hyp, h2.hyp, ih h3⟩

theorem ldTowJ_tail : Spec.ldTowJ_tail := fun E _ _ a T h =>
  ldTowC_tail E a T.toC (ldTowJ_hyp E a T h)

theorem ldTowGJ_hyp {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
    [Nonempty G.P] {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}
    (T : LdTowGJ G Sb sl Z) (h : T.John) : T.toG.Hyp := by
  cases T with
  | plain T => exact ldTowJ_hyp E _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨h0, h1, h2, h3⟩ := h
    exact ⟨h0, h1.hyp, h2.hyp, ldTowJ_hyp E _ rest h3⟩

theorem ldTowGJ_tail : Spec.ldTowGJ_tail := fun E B _ _ _ S G _ Sb sl Z T h =>
  ldTowG_tail E B S G Sb sl Z T.toG (ldTowGJ_hyp T h)

theorem ldTowGJ_run : Spec.ldTowGJ_run := by
  intro E _ _ S D T d h
  have hp : D.Pre (D.upJ T) :=
    ⟨h.isT, h.isQ, h.ev, by rw [h.isL]; exact ldJohn_bridge E S D.G d h.laws h.dist h.john,
      h.fits, ldTowGJ_hyp T h.tow⟩
  exact ⟨hp, hp.ok⟩

end Cb
