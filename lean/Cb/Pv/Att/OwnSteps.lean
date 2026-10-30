-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/OwnSteps.lean: the letters of an attention sub-proof's own rounds (Cb/Pv/Att/Gaps.lean)
at a value: the eight sumchecks of the library's own description of an attention segment, with the
challenges gathered from the statement as it grows.

Definitions, statements and proofs. Cb/Pv/Att/Gaps.lean proves knowledge soundness of the chain of
the own rounds for every record `TailG`, whose seven equations whoever gives a value must prove.
Here the value is given. Each sumcheck is a step of Inst/Model/Att/Sums.lean (through
Cb/Pv/Att/Steps.lean, Step18.lean and BitsSc3.lean). Its public state `AttSeg.Pub` is put together
from what the statement holds at that stage. Its target is the public part of the form from which
it starts, and its incoming form has that form's mask entries.

Main names:
  `OwnPar E M X`: what stays free: the sizes D and C; the entries J, how a tuple of messages is read
    as entries (msg) and the entries as cells (rd); the lookup's end point in the first statement
    (zOf); the number of plane messages (npl); the number of variables that number a bit (kap); the
    places of all mask entries; three linear claims on further scalars that no equation reads.
  `Means E D C kap`: four equations on the description's sums, for all challenges and all contents
    of the cells. hV: the two value products together are aV + th cV. hF: the score's sum is the
    batch of the row maxima's rule values (`AttSeg.rvM6`) plus the extensions of a family d1 at
    (tg | ti). hD: the sum of step 18 is the batch of the second maps of step s16 at (fi | fg | fn).
    hH: the bits' sum is the batch of the extensions of a family d2 at (tk | tbg | tbi).
    Cb/Pv/Att/OwnAt.lean gives the value of this record.
  `P.pub0`, `pubV`, `pubZ`, `pubF`, `pubD`, `pubH`: the challenges, stage by stage. z is the first
    statement's; th is the draw before the value products; (tg | ti) and (tk | tbg | tbi) are the
    two cuts of the point drawn; o, o', o'' are the powers of the three later draws; (fi | fg | fn)
    is the point of the score's sumcheck, read off its output (`SumL.ptOf`).
  `P.uM`, `uD`, `sE`, `sVM`, `sVD`, `sF`, `sD`, `sH`: the eight sumchecks. The further scalars are
    3 npl + 7, 7, 5 + lT + 2, 2, 0, 0, 0, 0. uM and uD start from the last of theirs; sE from its
    second (ZO); sVM from its first and sVD from sVM's second; sF from the batch of the pairs'
    scalars; sD from the batch of the hidden second end values of sF; sH from 0.
  `PlainSc.pull`: a plain sumcheck read at other public states. sD needs it: its incoming form has
    the further challenge of sF (`SumL.lstOf`), for which `AttSeg.Pub` has no field.
  `P.gV`, `d1`, `d2`, `h1`, `h2`, `lF`, `fF`: the gaps and the families. gV: aV less the hidden ACC,
    cV less the hidden ZC. h1, h2: the extensions of d1, d2 at the cuts of the point. lF: the hidden
    value of a pair's scalar is `AttSeg.rvM6`.
  `P.eV`, `eF1`, `eF`, `eD`, `eH`: five of the seven equations; the two others hold by definition.
  `P.tail Mn : TailG`, `P.own Mn : AttOwn`: the record, and the letters of the whole chain.
  `ownSteps_knowAt`: `KnowAt` for the chain at the value, under no premise but the record Mn.
  `P.own_todo`: what is claimed at the chain's start: there are further scalars of uM, uD and sE of
    which the free linear claims hold; the three sums are the hidden start values; both gaps gV are
    0; both families vanish on their cubes.
  `P.own_nums`: the list of the chain's errors.

Limits: those of Cb/Pv/Att/Gaps.lean and Cb/Pv/Att/Steps.lean. That the programs' sumchecks, further
scalars and claims are these is not stated here: which scalar is which follows a reading of the
verifier on bytes (OnBytes/Model/AttentionScores.lean, OnBytes/Model/AttentionDivide.lean), and no
theorem ties the two. A hidden value is what was sent less a mask entry; hidden is the name of a
value's part in the protocol. The claims that tie further scalars and end values to committed tables
are not here: they are the free linear claims and what the chain's end owes (`Ch.Last`). The chain
tests no linear claim: the two that are written out here, sVM's (the two hidden sums add up to ACC +
th ZC) and lF, are owed at the chain's end too, like the free ones. What it means for the cells that
gV is 0 and that d1 and d2 vanish is not said here. Three things on that. kap is free: with fewer
than enough variables to number all lT bits of a position (lT > 2 ^ kap) the bits from 2 ^ kap on
are read by no map of sH. That cV is the hidden ZC speaks of one point, the lookup's: that the
denominator is the row's sum at every head and position does not follow inside this chain. And the
value has two score units, each of D.nb pairs, with all plane messages before the first: a list of
calls of another form has another chain. Nothing is said on an honest prover or on hiding.
-/
import Cb.Pv.Att.Gaps
import Cb.Pv.Att.Steps
import Cb.Pv.Att.Step18
import Cb.Pv.Att.BitsSc3
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Inst.Model

/-! ### Small tools -/

section Tools
variable {E : Type} [Field E]

/-- The form that reads the one entry a. -/
def inc1 {J : Type} [DecidableEq J] (a : J) : J → E := fun j => if a = j then 1 else 0

theorem inc1_sum {J : Type} [Fintype J] [DecidableEq J] (a : J) (m : J → E) :
    ∑ j, inc1 a j * m j = m a := by
  simp [inc1, ite_mul]

/-- The form with the coefficient c i at the entry k i. -/
def incAt {J : Type} [DecidableEq J] {n : ℕ} (k : Fin n → J) (c : Fin n → E) : J → E :=
  fun j => ∑ i, if k i = j then c i else 0

theorem incAt_sum {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (k : Fin n → J) (c : Fin n → E)
    (m : J → E) : ∑ j, incAt k c j * m j = ∑ i, c i * m (k i) := by
  unfold incAt
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_mul]

omit [Field E] in
theorem cat_sh (n : ℕ) (u : ℕ → E) : AttSeg.cat n u (AttSeg.sh u n) = u := by
  funext t
  unfold AttSeg.cat AttSeg.sh
  split_ifs with h
  · rfl
  · rw [Nat.add_sub_of_le (not_lt.mp h)]

omit [Field E] in
theorem cat_sh3 (a b : ℕ) (u : ℕ → E) :
    AttSeg.cat a u (AttSeg.cat b (AttSeg.sh u a) (AttSeg.sh u (a + b))) = u := by
  have e : AttSeg.sh u (a + b) = AttSeg.sh (AttSeg.sh u a) b := by
    funext t
    unfold AttSeg.sh
    rw [Nat.add_assoc]
  rw [e, cat_sh, cat_sh]

end Tools

/-! ### A plain sumcheck at other public states -/

namespace PlainSc
variable {E : Type} [Field E] [Fintype E] (T : PlainSc E)

/-- The same sumcheck, read at states St' through f, with an incoming form of its own. -/
def pull {St' : Type} (f : St' → T.St) (inc' : St' → T.J → E) : PlainSc E where
  nv := T.nv
  deg := T.deg
  A := T.A
  finA := T.finA
  DY := T.DY
  St := St'
  J := T.J
  finJ := T.finJ
  map := fun st => T.map (f st)
  S := fun st => T.S (f st)
  inc := inc'
  wAt := T.wAt
  cAt := T.cAt

theorem pull_ok {St' : Type} (f : St' → T.St) (inc' : St' → T.J → E) (h : T.OK) :
    (T.pull f inc').OK :=
  ⟨h.one, fun st m u => h.degX (f st) m u, fun st x v u => h.degY (f st) x v u⟩

end PlainSc

/-! ### The point and the further challenge in a sumcheck's output -/

namespace SumL
variable {E : Type} [Field E] [Fintype E] {M X : Type} (S : SumL E M X)

/-- The point of the variables' challenges. -/
noncomputable def ptOf (b : S.Nx) : Fin S.T.nv → E :=
  ldPartFn S.T.nv S.T.deg S.T.dat (S.T.our.ini b.2.st (S.T.our.par.hp b.2.st b.2.pt))

/-- The challenge of the further variable. -/
noncomputable def lstOf (b : S.Nx) : E := S.T.our.lst b.2.st (S.T.our.par.hp b.2.st b.2.pt)

theorem eGap_eq (b : S.Nx) (m : M) (a : S.T.A) :
    S.eGap b m a =
      S.T.map b.2.st (S.msg m) a (S.ptOf b) + S.msg m (S.T.cAt a) * S.lstOf b - b.2.vals a := rfl

end SumL

/-! ### The sums over the cube -/

section Sums
variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) (C : AttSeg.Calls) {J : Type}
  [Fintype J] (rd : (J → E) → AttSeg.Raw → E)

/-- The sum over the corners of step s is the description's own sum. -/
theorem step_core (s : AttSeg.Step) (inc : AttSeg.Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J)
    (cAt : Fin D.nb × Bool → J) (p : AttSeg.Pub E) (m : J → E) :
    ∑ b : Fin (s.g D) → Bool,
        (stepSc3 D C rd s inc wAt cAt).plain.S p (Alg.corner b)
          (fun a => (stepSc3 D C rd s inc wAt cAt).plain.map p m a (Alg.corner b)) =
      AttSeg.sumPhi D C p (rd m) s := by
  have h := (step_sum D C rd s inc wAt cAt
    (∑ b : Fin (s.g D) → Bool,
        (stepSc3 D C rd s inc wAt cAt).plain.S p (Alg.corner b)
          (fun a => (stepSc3 D C rd s inc wAt cAt).plain.map p m a (Alg.corner b)) +
      ∑ j, inc p j * m j, p) m).1
    ((plain_sum (stepSc3 D C rd s inc wAt cAt).plain _ m).2 rfl)
  exact (add_right_cancel h).symm

/-- The gap of step s. -/
theorem step_gap {M X : Type} (s : AttSeg.Step) (inc : AttSeg.Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J)
    (cAt : Fin D.nb × Bool → J) (n : ℕ) (cl : X → (Fin n → E) → E × AttSeg.Pub E)
    (msg : M → J → E) (L : X → (Fin n → E) → M → Prop) (x : X) (r : Fin n → E) (m : M) :
    (SumL.of3 (stepSc3 D C rd s inc wAt cAt) n cl msg L).gap x r m =
      AttSeg.sumPhi D C (cl x r).2 (rd (msg m)) s + ∑ j, inc (cl x r).2 j * msg m j -
        (cl x r).1 := by
  rw [← step_core D C rd s inc wAt cAt (cl x r).2 (msg m)]
  rfl

/-- The sum over the corners of step 18 is the description's own sum. -/
theorem step18_core (inc : AttSeg.Pub E → J → E)
    (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J)
    (cAt : (size18 D).A → J) (p : AttSeg.Pub E) (m : J → E) :
    ∑ b : Fin (size18 D).k → Bool,
        (step18 D rd inc wAt cAt).plain.S p (Alg.corner b)
          (fun a => (step18 D rd inc wAt cAt).plain.map p m a (Alg.corner b)) =
      ∑ X ∈ Finset.range (2 ^ AttSeg.g18 D),
        AttSeg.Phi18 D p (rd m) (Blocks.cubePt (AttSeg.g18 D) X) := by
  have h := (step18_sum D rd inc wAt cAt
    (∑ b : Fin (size18 D).k → Bool,
        (step18 D rd inc wAt cAt).plain.S p (Alg.corner b)
          (fun a => (step18 D rd inc wAt cAt).plain.map p m a (Alg.corner b)) +
      ∑ j, inc p j * m j, p) m).1
    ((plain_sum (step18 D rd inc wAt cAt).plain _ m).2 rfl)
  exact (add_right_cancel h).symm

end Sums

/-! ### The parameters -/

/-- What is free at the value: the sizes, the entries and how they are read, the first statement's
point, the places of the mask entries, and the linear claims that tie further scalars to tables. -/
structure OwnPar (E M X : Type) [Field E] [Fintype E] where
  D : AttSeg.Dim
  C : AttSeg.Calls
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- the entries in a tuple of messages; the cells' content in the entries -/
  msg : M → J → E
  rd : (J → E) → AttSeg.Raw → E
  /-- the end point of the lookup's product tree, in the first statement -/
  zOf : X → ℕ → E
  /-- the plane messages, of three scalars each, before the first score unit's seven scalars -/
  npl : ℕ
  /-- the variables that number a bit of a position, in the last sumcheck -/
  kap : ℕ
  /-- the mask entries of the sumchecks -/
  wAt : ∀ s : AttSeg.Step, PIdx (ldPartFmt E (s.g D) (fun _ => 3) ++ [pDummy E 2]) → J
  cAt : AttSeg.Step → Fin D.nb × Bool → J
  w18 : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J
  c18 : (size18 D).A → J
  wH : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J
  cH : Fin D.nb × Bool → J
  /-- the mask entries of the further scalars -/
  kM : Fin (3 * npl + 7) → J
  kD : Fin 7 → J
  kE : Fin (5 + D.lT + 2) → J
  kV : Fin 2 → J
  kF : Fin D.nb → J
  /-- linear claims on further scalars that no equation here reads -/
  LM : Seen E X → (Fin (3 * npl + 7) → E) → M → Prop
  LD : Seen E X → (Fin 7 → E) → M → Prop
  LE : Seen E X → (Fin (5 + D.lT + 2) → E) → M → Prop

attribute [instance] OwnPar.finJ OwnPar.decJ

/-- What the description's sums are, as equations on all challenges and all contents of the
cells. -/
structure Means (E : Type) [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls) (kap : ℕ) where
  /-- the two value products together are affine in the challenge th -/
  aV : (ℕ → E) → (AttSeg.Raw → E) → E
  cV : (ℕ → E) → (AttSeg.Raw → E) → E
  hV : ∀ (p : AttSeg.Pub E) t, AttSeg.sumPhi D C p t .s11 + AttSeg.sumPhi D C p t .s12 =
    aV p.z t + p.th * cV p.z t
  /-- the first family, on the cube (g | i) -/
  d1 : (AttSeg.Raw → E) → ℕ → ℕ → E
  hF : ∀ (p : AttSeg.Pub E) t, AttSeg.sumPhi D C p t .s16 =
    ∑ b ∈ Finset.range D.nb, p.o b * (AttSeg.rvM6 D p t b +
      Blocks.ext (D.lg + D.lT) (d1 t b) (AttSeg.cat D.lg p.tg p.ti))
  hD : ∀ (p : AttSeg.Pub E) t,
    ∑ X ∈ Finset.range (2 ^ AttSeg.g18 D), AttSeg.Phi18 D p t (Blocks.cubePt (AttSeg.g18 D) X) =
      ∑ b ∈ Finset.range D.nb, p.o' b *
        AttSeg.Bext D C p t .s16 b (AttSeg.cat D.lT p.fi (AttSeg.cat D.lg p.fg p.fn))
  /-- the second family, on the cube (k | g | i) -/
  d2 : (AttSeg.Raw → E) → ℕ → ℕ → E
  hH : ∀ (p : AttSeg.Pub E) t, bitSum kap D p t =
    ∑ b ∈ Finset.range D.nb, p.o'' b *
      Blocks.ext (kap + D.lg + D.lT) (d2 t b)
        (AttSeg.cat kap p.tk (AttSeg.cat D.lg p.tbg p.tbi))

namespace OwnPar
variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X)

/-- the cells' content in a tuple of messages -/
def tOf (m : M) : AttSeg.Raw → E := P.rd (P.msg m)

/-- The parameters of step s, with an incoming form. -/
noncomputable abbrev st3 (s : AttSeg.Step) (inc : AttSeg.Pub E → P.J → E) : Sc3 E :=
  stepSc3 P.D P.C P.rd s inc (P.wAt s) (P.cAt s)

/-! ### The challenges, stage by stage, and the eight sumchecks -/

/-- At the first statement: the lookup's end point alone. -/
def pub0 (x : Seen E X) : AttSeg.Pub E :=
  ⟨P.zOf x.1, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The score unit of region M. It starts from the last of its further scalars. -/
noncomputable def uM : SumL E M (Seen E X) :=
  .of3 (P.st3 .s6b fun _ => inc1 (P.kM (Fin.last _))) (3 * P.npl + 7)
    (fun x r => (r (Fin.last _), P.pub0 x)) P.msg P.LM

/-- The score unit of region D. -/
noncomputable def uD : SumL E M (Seen E X) :=
  .of3 (P.st3 .s6d fun _ => inc1 (P.kD (Fin.last _))) 7
    (fun x r => (r (Fin.last _), P.pub0 x)) P.msg P.LD

/-- the places of ACC, ZO and ZC among the further scalars of the next sumcheck -/
def iACC : Fin (5 + P.D.lT + 2) := ⟨0, by omega⟩
def iZO : Fin (5 + P.D.lT + 2) := ⟨1, by omega⟩
def iZC : Fin (5 + P.D.lT + 2) := ⟨2, by omega⟩

/-- The denominator times the output. It starts from ZO. -/
noncomputable def sE : SumL E M (Seen E X) :=
  .of3 (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)) (5 + P.D.lT + 2)
    (fun x r => (r P.iZO, P.pub0 x)) P.msg P.LE

/-- The hidden value of a further scalar of sE: what was sent less its mask entry. -/
def hidE (y : P.sE.Nx) (m : M) (j : Fin (5 + P.D.lT + 2)) : E := y.1.2 j - P.msg m (P.kE j)

/-- Behind the draw for the value products. -/
def pubV (x : P.sE.Nx × E) : AttSeg.Pub E := { P.pub0 x.1.1.1 with th := x.2 }

/-- The value product below the diagonal. Its two further scalars are its own start and the next
sumcheck's. The linear claim: the two hidden sums add up to ACC + th ZC. -/
noncomputable def sVM : SumL E M (P.sE.Nx × E) :=
  .of3 (P.st3 .s11 fun _ => inc1 (P.kV 0)) 2 (fun x r => (r 0, P.pubV x)) P.msg
    fun x r m => (r 0 - P.msg m (P.kV 0)) + (r 1 - P.msg m (P.kV 1)) =
      P.hidE x.1 m P.iACC + x.2 * P.hidE x.1 m P.iZC

/-- The value product on the diagonal. -/
noncomputable def sVD : SumL E M P.sVM.Nx :=
  .of3 (P.st3 .s12 fun _ => inc1 (P.kV 1)) 0 (fun y _ => (y.1.2 (1 : Fin 2), P.pubV y.1.1)) P.msg
    fun _ _ _ => True

/-- the variables of the two cubes: (g | i) and (k | g | i) -/
def g1 : ℕ := P.D.lg + P.D.lT
def g2 : ℕ := P.kap + P.D.lg + P.D.lT

/-- Behind the draw of the point: its first cut is (tg | ti), its second (tk | tbg | tbi). -/
noncomputable def pubZ (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) : AttSeg.Pub E :=
  { P.pubV (P.sVM.pre (P.sVD.pre z.1)) with
    tg := Blocks.nat (cutPt P.g1 P.g2 z.2).1
    ti := AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 z.2).1) P.D.lg
    tk := Blocks.nat (cutPt P.g1 P.g2 z.2).2
    tbg := AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 z.2).2) P.kap
    tbi := AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 z.2).2) (P.kap + P.D.lg) }

/-- the statements before the score's sumcheck -/
abbrev XF : Type := ((P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) × (Fin P.D.nb → E)) × E

/-- Behind the pairs' scalars and the draw: o is the powers of the element drawn. -/
noncomputable def pubF (w : P.XF) : AttSeg.Pub E := { P.pubZ w.1.1 with o := fun b => w.2 ^ b }

/-- The score at the index. It starts from the batch of the pairs' scalars. -/
noncomputable def sF : SumL E M P.XF :=
  .of3 (P.st3 .s16 fun p => incAt P.kF fun b => p.o b) 0
    (fun w _ => (∑ i : Fin P.D.nb, w.2 ^ (i : ℕ) * w.1.2 i, P.pubF w)) P.msg fun _ _ _ => True

/-- Behind the next draw: o' is the powers; (fi | fg | fn) is the point of the score's sumcheck. -/
noncomputable def pubD (w : P.sF.Nx × E) : AttSeg.Pub E :=
  { P.pubF w.1.1.1 with
    o' := fun b => w.2 ^ b
    fi := Blocks.nat (P.sF.ptOf w.1)
    fg := AttSeg.sh (Blocks.nat (P.sF.ptOf w.1)) P.D.lT
    fn := AttSeg.sh (Blocks.nat (P.sF.ptOf w.1)) (P.D.lT + P.D.lg) }

/-- The second end value of pair i of the score's sumcheck. -/
def iB (i : Fin P.D.nb) : P.sF.T.A := (i, true)

/-- The key at the index. It starts from the batch of the hidden second end values of the score's
sumcheck: the public part is the batch of what was shown, and the incoming form has each one's mask
entry, times the further challenge of that sumcheck. The public states carry that form. -/
noncomputable def sD : SumL E M (P.sF.Nx × E) where
  T := (step18 P.D P.rd (fun _ _ => 0) P.w18 P.c18).plain.pull
    (St' := AttSeg.Pub E × (P.J → E)) Prod.fst Prod.snd
  ok := PlainSc.pull_ok _ _ _ (scd_ok _)
  n := 0
  cl := fun w _ => (∑ i : Fin P.D.nb, w.2 ^ (i : ℕ) * w.1.2.vals (P.iB i),
    (P.pubD w, incAt (fun i => P.cAt .s16 (i, true)) fun i => w.2 ^ (i : ℕ) * P.sF.lstOf w.1))
  msg := P.msg
  L := fun _ _ _ => True

/-- Behind the last draw: o'' is the powers. -/
noncomputable def pubH (w : P.sD.Nx × E) : AttSeg.Pub E :=
  { P.pubD w.1.1.1 with o'' := fun b => w.2 ^ b }

/-- The bits. It starts from 0. -/
noncomputable def sH : SumL E M (P.sD.Nx × E) :=
  .of3 (bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH) 0 (fun w _ => (0, P.pubH w)) P.msg
    fun _ _ _ => True

/-! ### The gaps and the families -/

variable (Mn : Means E P.D P.C P.kap)

/-- The two gaps before the draw for the value products. -/
def gV (y : P.sE.Nx) (m : M) (i : Fin 2) : E :=
  if i = 0 then Mn.aV (P.zOf y.1.1.1) (P.tOf m) - P.hidE y m P.iACC
  else Mn.cV (P.zOf y.1.1.1) (P.tOf m) - P.hidE y m P.iZC

def d1 (_ : P.sE.Nx) (m : M) (i : Fin P.D.nb) : ℕ → E := Mn.d1 (P.tOf m) i
def d2 (_ : P.sE.Nx) (m : M) (i : Fin P.D.nb) : ℕ → E := Mn.d2 (P.tOf m) i

/-- The families' extensions at the point drawn. -/
def h1 (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (m : M) (i : Fin P.D.nb) : E :=
  Blocks.ext P.g1 (Mn.d1 (P.tOf m) i) (Blocks.nat (cutPt P.g1 P.g2 z.2).1)
def h2 (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (m : M) (i : Fin P.D.nb) : E :=
  Blocks.ext P.g2 (Mn.d2 (P.tOf m) i) (Blocks.nat (cutPt P.g1 P.g2 z.2).2)

/-- What is claimed of the pairs' scalars: the hidden value of each is the row maximum's extension
at (tg | ti), the description's rule value M6. -/
def lF (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (s : Fin P.D.nb → E) (m : M) : Prop :=
  ∀ i : Fin P.D.nb, s i - P.msg m (P.kF i) = AttSeg.rvM6 P.D (P.pubZ z) (P.tOf m) i

/-- The gaps that the score's sumcheck batches. -/
noncomputable def fF (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (s : Fin P.D.nb → E) (m : M)
    (i : Fin P.D.nb) : E :=
  AttSeg.rvM6 P.D (P.pubZ z) (P.tOf m) i + P.h1 Mn z m i - (s i - P.msg m (P.kF i))

/-! ### The seven equations -/

theorem eV (x : P.sE.Nx) (β : E) (r : Fin 2 → E) (o : P.sVM.T.our.par.Out) (r' : Fin 0 → E)
    (m : M) (hL : P.sVM.L (x, β) r m) :
    P.sVM.gap (x, β) r m + P.sVD.gap (((x, β), r), o) r' m =
      P.gV Mn x m 0 + β * P.gV Mn x m 1 := by
  have a : P.sVM.gap (x, β) r m = AttSeg.sumPhi P.D P.C (P.pubV (x, β)) (P.tOf m) .s11 +
      P.msg m (P.kV 0) - r 0 := by
    refine (step_gap P.D P.C P.rd .s11 _ _ _ _ _ _ _ _ _ _).trans ?_
    rw [inc1_sum]
    rfl
  have b : P.sVD.gap (((x, β), r), o) r' m =
      AttSeg.sumPhi P.D P.C (P.pubV (x, β)) (P.tOf m) .s12 + P.msg m (P.kV 1) - r 1 := by
    refine (step_gap P.D P.C P.rd .s12 _ _ _ _ _ _ _ _ _ _).trans ?_
    rw [inc1_sum]
    rfl
  have c := Mn.hV (P.pubV (x, β)) (P.tOf m)
  have c' : AttSeg.sumPhi P.D P.C (P.pubV (x, β)) (P.tOf m) .s11 +
      AttSeg.sumPhi P.D P.C (P.pubV (x, β)) (P.tOf m) .s12 =
      Mn.aV (P.zOf x.1.1.1) (P.tOf m) + β * Mn.cV (P.zOf x.1.1.1) (P.tOf m) := c
  have d : (r 0 - P.msg m (P.kV 0)) + (r 1 - P.msg m (P.kV 1)) =
      P.hidE x m P.iACC + β * P.hidE x m P.iZC := hL
  have g0 : P.gV Mn x m 0 = Mn.aV (P.zOf x.1.1.1) (P.tOf m) - P.hidE x m P.iACC := by
    simp [gV]
  have g1 : P.gV Mn x m 1 = Mn.cV (P.zOf x.1.1.1) (P.tOf m) - P.hidE x m P.iZC := by
    simp [gV]
  rw [a, b, g0, g1]
  linear_combination c' - d

theorem eF1 (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (s : Fin P.D.nb → E) (m : M)
    (i : Fin P.D.nb) (h : P.lF z s m) : P.fF Mn z s m i = P.h1 Mn z m i := by
  unfold fF
  rw [h i]
  ring

theorem eF (z : P.sVD.Nx × (Fin (P.g1 + P.g2) → E)) (s : Fin P.D.nb → E) (β : E)
    (r : Fin 0 → E) (m : M) :
    P.sF.gap ((z, s), β) r m = ∑ i : Fin P.D.nb, β ^ (i : ℕ) * P.fF Mn z s m i := by
  refine (step_gap P.D P.C P.rd .s16 _ _ _ _ _ _ _ _ _ _).trans ?_
  rw [incAt_sum, Mn.hF, Finset.sum_range]
  show ∑ i : Fin P.D.nb, β ^ (i : ℕ) * (AttSeg.rvM6 P.D (P.pubZ z) (P.tOf m) i +
        Blocks.ext (P.D.lg + P.D.lT) (Mn.d1 (P.tOf m) i)
          (AttSeg.cat P.D.lg (Blocks.nat (cutPt P.g1 P.g2 z.2).1)
            (AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 z.2).1) P.D.lg))) +
      ∑ i : Fin P.D.nb, β ^ (i : ℕ) * P.msg m (P.kF i) - ∑ i : Fin P.D.nb, β ^ (i : ℕ) * s i = _
  rw [cat_sh, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold fF h1
  show _ = β ^ (i : ℕ) * (AttSeg.rvM6 P.D (P.pubZ z) (P.tOf m) i +
    Blocks.ext (P.D.lg + P.D.lT) (Mn.d1 (P.tOf m) i) (Blocks.nat (cutPt P.g1 P.g2 z.2).1) -
    (s i - P.msg m (P.kF i)))
  ring

include Mn in
theorem eD (b : P.sF.Nx) (β : E) (r : Fin 0 → E) (m : M) :
    P.sD.gap (b, β) r m = ∑ i : Fin P.D.nb, β ^ (i : ℕ) * P.sF.eGap b m (P.iB i) := by
  have a : P.sD.gap (b, β) r m =
      ∑ X ∈ Finset.range (2 ^ AttSeg.g18 P.D),
          AttSeg.Phi18 P.D (P.pubD (b, β)) (P.tOf m) (Blocks.cubePt (AttSeg.g18 P.D) X) +
        ∑ j, incAt (fun i => P.cAt .s16 (i, true))
          (fun i : Fin P.D.nb => β ^ (i : ℕ) * P.sF.lstOf b) j * P.msg m j -
        ∑ i : Fin P.D.nb, β ^ (i : ℕ) * b.2.vals (P.iB i) := by
    unfold tOf
    rw [← step18_core P.D P.rd (fun _ _ => 0) P.w18 P.c18 (P.pubD (b, β)) (P.msg m)]
    rfl
  rw [a, incAt_sum, Mn.hD, Finset.sum_range]
  show ∑ i : Fin P.D.nb, β ^ (i : ℕ) * Blocks.ext (AttSeg.Step.s16.g P.D)
        (AttSeg.Bcube P.D P.C (P.pubD (b, β)) (P.tOf m) .s16 i)
        (AttSeg.cat P.D.lT (Blocks.nat (P.sF.ptOf b))
          (AttSeg.cat P.D.lg (AttSeg.sh (Blocks.nat (P.sF.ptOf b)) P.D.lT)
            (AttSeg.sh (Blocks.nat (P.sF.ptOf b)) (P.D.lT + P.D.lg)))) + _ - _ = _
  rw [cat_sh3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SumL.eGap_eq]
  show _ = β ^ (i : ℕ) * (Blocks.ext (AttSeg.Step.s16.g P.D)
      (AttSeg.Bcube P.D P.C b.2.st (P.tOf m) .s16 i) (Blocks.nat (P.sF.ptOf b)) +
    P.msg m (P.cAt .s16 (i, true)) * P.sF.lstOf b - b.2.vals (P.iB i))
  have e : AttSeg.Bcube P.D P.C (P.pubD (b, β)) (P.tOf m) .s16 i =
      AttSeg.Bcube P.D P.C b.2.st (P.tOf m) .s16 i := rfl
  rw [e]
  ring

theorem eH (c : P.sD.Nx) (β : E) (r : Fin 0 → E) (m : M) :
    P.sH.gap (c, β) r m =
      ∑ i : Fin P.D.nb, β ^ (i : ℕ) * P.h2 Mn (P.sF.pre (P.sD.pre c).1).1.1 m i := by
  have a : P.sH.gap (c, β) r m = bitSum P.kap P.D (P.pubH (c, β)) (P.tOf m) := by
    have h : bitSum P.kap P.D (P.pubH (c, β)) (P.rd (P.msg m)) + ∑ j, (0 : E) * P.msg m j =
        P.sH.tot (P.pubH (c, β)) m :=
      (bits_sum P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH
        (P.sH.tot (P.pubH (c, β)) m, P.pubH (c, β)) (P.msg m)).1
        ((plain_sum (bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH).plain _ (P.msg m)).2 rfl)
    have h' : P.sH.gap (c, β) r m = P.sH.tot (P.pubH (c, β)) m - 0 := rfl
    rw [h', ← h]
    simp [tOf]
  rw [a, Mn.hH, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  show β ^ (i : ℕ) * Blocks.ext (P.kap + P.D.lg + P.D.lT) (Mn.d2 (P.tOf m) i)
    (AttSeg.cat P.kap (Blocks.nat (cutPt P.g1 P.g2 (P.sF.pre (P.sD.pre c).1).1.1.2).2)
      (AttSeg.cat P.D.lg
        (AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 (P.sF.pre (P.sD.pre c).1).1.1.2).2) P.kap)
        (AttSeg.sh (Blocks.nat (cutPt P.g1 P.g2 (P.sF.pre (P.sD.pre c).1).1.1.2).2)
          (P.kap + P.D.lg)))) = _
  rw [cat_sh3]
  rfl

/-! ### The record, and the chain -/

/-- The letters of the eleven stages behind the score units, at the value. -/
noncomputable def tail : TailG E M (Seen E X) where
  sE := P.sE
  gV := P.gV Mn
  np := P.D.nb
  g1 := P.g1
  g2 := P.g2
  d1 := P.d1 Mn
  d2 := P.d2 Mn
  sVM := P.sVM
  sVD := P.sVD
  eV := fun x β r o r' m hL _ => P.eV Mn x β r o r' m hL
  h1 := P.h1 Mn
  h2 := P.h2 Mn
  e1 := fun _ _ _ _ => rfl
  e2 := fun _ _ _ _ => rfl
  lF := P.lF
  fF := P.fF Mn
  eF1 := fun z s m i h => P.eF1 Mn z s m i h
  sF := P.sF
  eF := fun z s β r m _ => P.eF Mn z s β r m
  iB := P.iB
  sD := P.sD
  eD := fun b β r m _ => P.eD Mn b β r m
  sH := P.sH
  eH := fun c β r m _ => P.eH Mn c β r m

/-- The letters of the own rounds: the two score units, then the tail. -/
noncomputable def own : AttOwn E M X := ⟨[P.uM, P.uD], (P.tail Mn).toTail⟩

/-! ### What is claimed at the start -/

theorem uM_sum (x : Seen E X) (r : Fin (3 * P.npl + 7) → E) (m : M) :
    P.uM.T.our.par.SumHolds (P.uM.cl x r) (P.uM.msg m) ↔
      AttSeg.sumPhi P.D P.C (P.pub0 x) (P.tOf m) .s6b =
        r (Fin.last _) - P.msg m (P.kM (Fin.last _)) := by
  refine (step_sum P.D P.C P.rd .s6b _ _ _ _ _).trans ?_
  rw [inc1_sum]
  exact eq_sub_iff_add_eq.symm

theorem uD_sum (x : Seen E X) (r : Fin 7 → E) (m : M) :
    P.uD.T.our.par.SumHolds (P.uD.cl x r) (P.uD.msg m) ↔
      AttSeg.sumPhi P.D P.C (P.pub0 x) (P.tOf m) .s6d =
        r (Fin.last _) - P.msg m (P.kD (Fin.last _)) := by
  refine (step_sum P.D P.C P.rd .s6d _ _ _ _ _).trans ?_
  rw [inc1_sum]
  exact eq_sub_iff_add_eq.symm

theorem sE_sum (x : Seen E X) (r : Fin (5 + P.D.lT + 2) → E) (m : M) :
    P.sE.T.our.par.SumHolds (P.sE.cl x r) (P.sE.msg m) ↔
      AttSeg.sumPhi P.D P.C (P.pub0 x) (P.tOf m) .s8 = r P.iZO - P.msg m (P.kE P.iZO) := by
  refine (step_sum P.D P.C P.rd .s8 _ _ _ _ _).trans ?_
  rw [inc1_sum]
  exact eq_sub_iff_add_eq.symm

theorem gV_zero (y : P.sE.Nx) (m : M) : (∀ i, P.gV Mn y m i = 0) ↔
    Mn.aV (P.zOf y.1.1.1) (P.tOf m) = P.hidE y m P.iACC ∧
      Mn.cV (P.zOf y.1.1.1) (P.tOf m) = P.hidE y m P.iZC := by
  rw [Fin.forall_fin_two]
  simp [gV, sub_eq_zero]

/-- The claim at the start of the chain, down to the first draw. -/
theorem own_todo_raw (x : X) (m : M) : (P.own Mn).ch.Todo x m ↔
    ∃ rM, P.LM (x, []) rM m ∧ P.uM.T.our.par.SumHolds (P.uM.cl (x, []) rM) (P.uM.msg m) ∧
      ∃ _ : P.uM.T.our.par.Out,
    ∃ rD, P.LD (x, [List.ofFn rM]) rD m ∧
      P.uD.T.our.par.SumHolds (P.uD.cl (x, [List.ofFn rM]) rD) (P.uD.msg m) ∧
      ∃ _ : P.uD.T.our.par.Out,
    ∃ rE, P.LE (x, [List.ofFn rM, List.ofFn rD]) rE m ∧
      P.sE.T.our.par.SumHolds (P.sE.cl (x, [List.ofFn rM, List.ofFn rD]) rE) (P.sE.msg m) ∧
      ∃ oE : P.sE.T.our.par.Out,
        (∀ i, P.gV Mn (((x, [List.ofFn rM, List.ofFn rD]), rE), oE) m i = 0) ∧
        (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, Mn.d1 (P.tOf m) i Y = 0) ∧
        ∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, Mn.d2 (P.tOf m) i Y = 0 :=
  Iff.rfl

/-- The same, with the three sum claims in the description's words. -/
theorem own_todo (x : X) (m : M) : (P.own Mn).ch.Todo x m ↔
    ∃ rM, P.LM (x, []) rM m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b =
        rM (Fin.last _) - P.msg m (P.kM (Fin.last _)) ∧
      ∃ _ : P.uM.T.our.par.Out,
    ∃ rD, P.LD (x, [List.ofFn rM]) rD m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM])) (P.tOf m) .s6d =
        rD (Fin.last _) - P.msg m (P.kD (Fin.last _)) ∧
      ∃ _ : P.uD.T.our.par.Out,
    ∃ rE, P.LE (x, [List.ofFn rM, List.ofFn rD]) rE m ∧
      AttSeg.sumPhi P.D P.C (P.pub0 (x, [List.ofFn rM, List.ofFn rD])) (P.tOf m) .s8 =
        rE P.iZO - P.msg m (P.kE P.iZO) ∧
      ∃ _ : P.sE.T.our.par.Out,
        (Mn.aV (P.zOf x) (P.tOf m) = rE P.iACC - P.msg m (P.kE P.iACC) ∧
          Mn.cV (P.zOf x) (P.tOf m) = rE P.iZC - P.msg m (P.kE P.iZC)) ∧
        (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, Mn.d1 (P.tOf m) i Y = 0) ∧
        ∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, Mn.d2 (P.tOf m) i Y = 0 := by
  rw [own_todo_raw]
  simp only [uM_sum, uD_sum, sE_sum, gV_zero, hidE]

/-- The list of the chain's errors. -/
theorem own_nums (Ex : ExtSpec) : errList ((P.own Mn).ch.eps Ex) =
    (1 :: (List.replicate (AttSeg.Step.s6b.g P.D) 3 ++ [2] ++ [0])) ++
    (1 :: (List.replicate (AttSeg.Step.s6d.g P.D) 3 ++ [2] ++ [0])) ++
    ((1 :: (List.replicate (AttSeg.Step.s8.g P.D) 3 ++ [2] ++ [0])) ++ ([1] ++
    ((1 :: (List.replicate (AttSeg.Step.s11.g P.D) 3 ++ [2] ++ [0])) ++
    ((1 :: (List.replicate (AttSeg.Step.s12.g P.D) 3 ++ [2] ++ [0])) ++
    ([(P.g1 + P.g2) * Fintype.card E ^ (P.g1 + P.g2 - 1)] ++ ([P.D.nb - 1] ++
    ((1 :: (List.replicate (AttSeg.Step.s16.g P.D) 3 ++ [2] ++ [0])) ++ ([P.D.nb - 1] ++
    ((1 :: (List.ofFn (size18 P.D).deg ++ [P.D.lT + 1] ++ [0])) ++ ([P.D.nb - 1] ++
    ((1 :: (List.replicate (P.D.lT + P.D.lg + P.kap) 3 ++ [2] ++ [0])) ++ []))))))))))) := by
  rw [attOwn_nums]
  show (([P.uM, P.uD].map SumL.nums).flatten) ++ (P.tail Mn).toTail.nums = _
  have e1 : P.uM.nums = _ := nums_of3 _ _ _ _ _
  have e2 : P.uD.nums = _ := nums_of3 _ _ _ _ _
  have e3 : P.sE.nums = _ := nums_of3 _ _ _ _ _
  have e4 : P.sVM.nums = _ := nums_of3 _ _ _ _ _
  have e5 : P.sVD.nums = _ := nums_of3 _ _ _ _ _
  have e6 : P.sF.nums = _ := nums_of3 _ _ _ _ _
  have e7 : P.sH.nums = _ := nums_of3 _ _ _ _ _
  show (P.uM.nums ++ (P.uD.nums ++ [])) ++ (P.sE.nums ++ ([1] ++ (P.sVM.nums ++ (P.sVD.nums ++
    ([(P.g1 + P.g2) * Fintype.card E ^ (P.g1 + P.g2 - 1)] ++ ([P.D.nb - 1] ++ (P.sF.nums ++
    ([P.D.nb - 1] ++ (P.sD.nums ++ ([P.D.nb - 1] ++ (P.sH.nums ++ []))))))))))) = _
  rw [e1, e2, e3, e4, e5, e6, e7, List.append_nil]
  rfl

end OwnPar

/-- Knowledge soundness of an attention sub-proof's own rounds at the value. -/
theorem ownSteps_knowAt {E M X Kc X0 Wp : Type} [Field E] [Fintype E] (P : OwnPar E M X)
    (Mn : Means E P.D P.C P.kap) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt ((P.own Mn).ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ (P.own Mn).ch.Todo x m)
      (jt A0 (fun e => pr ((P.own Mn).ch.back e)) ((P.own Mn).ch.Last Dn))
      (fun _ _ _ wp => wp) ((P.own Mn).ch.eps Ex) :=
  attOwnG_knowAt [P.uM, P.uD] (P.tail Mn) Ex A0 pr Dn

end Cb.Pv.Att

#print axioms Cb.Pv.Att.ownSteps_knowAt
#print axioms Cb.Pv.Att.OwnPar.own_todo
#print axioms Cb.Pv.Att.OwnPar.own_nums
