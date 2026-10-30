-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Blocks/TieF.lean: the tie of a lookup, with its first step as the programs run it.

Definitions, statements (in `Cb.Spec`) and proofs. As Cb/Ld/LdLkpTie.lean (`TieP`), whose steps 0
and 1 are one step here, with a public factor.
The tie is for PK = a PT_0 PT_1^2 PT_2^4 .., where PK is the product on the keys' side, a the public
factor and PT_j the product of plane j of the table's side. Q_j is a field of the record; in the
lookup's use it is the product over the planes i ≥ j of PT_i ^ 2^(i - j) (`LkHeadF.tie`,
Cb/Pv/Lookup/Blocks/HeadF.lean). The tie is a chain of sumchecks without variables, one for each
step.
Step 0 is for PK - a Q_1^2 PT_0 = target and shows three values (PK, Q_1, PT_0). Step j + 1 is for
Q_(j+1) = Q_(j+2)^2 PT_(j+1) and shows two. Every step has degree 3.
The programs' tie: OnBytes/Model/Look.lean, `Forest.tieStep` (there Z, P_j, G_j for PK, Q_j, PT_j).

Main names:
  `PscBk`: the sumcheck as a parameter: any family of blocks with the property in its field `good`.
    `PscBk.lib`: the sumcheck of Cb/Ld/LdPsc.lean.
  `TieF`, `D.lv`, `D.tieA`: the data; the steps; the steps 0, .., n as one block.
  `Spec.tieF_ok`: the conditions of the sumcheck hold at every step (`tieF_deg3z`: the summand of
    step 0 has degree 3 along every line).
  `tieF_jt`: under `D.StepTo l`, the joint before step l is the input joint of its sumcheck.
  `tieF_next`: the row on the value that the next step takes up is the next joint's own claim.
  `Spec.tieF_step`, `Spec.tieF_chain`: under `D.StepTo`: one step, and the steps 0, .., n, are good
    (`BkA.Good`, Cb/Ld/LdLkpTreeP.lean) between their joints.
  `Spec.tieF_ll`, `Spec.tieF_errs31`, `Spec.tieF_small`: with `PscBk.lib`: the lists of errors and
    of numbers of challenge values.
Limits: `D.StepTo n` (Q_(j+1) = Q_(j+2)^2 PT_(j+1) for j < n) is a premise. That PK, PT_j are the
products of a lookup, and `D.StepTo` for them, is the caller's matter; which values the planes'
products have is the trees' part. After the steps 0, .., n the claim on Q_(n+1) is open. The target
of step 0 is any value. That the programs run these steps is read off their text: no statement here
says so.

-/
import Cb.Ld.LdLkpTieProofs
import Cb.Ld.LdLkpFormat
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

/-- The sumcheck's block as a parameter: for every record T a block at the base that leads from T's
sum claim to T's output rows, beside any joint. -/
structure PscBk (E : Type) [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type) where
  bk : (T : PscOur E) → (M → T.J → E) → BkA Kc M (E × T.St) T.par.Out Ex Wp
  good : ∀ (T : PscOur E) (A0 : Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E),
    T.VarsOK → T.DegX → T.DegY → T.ValInj →
    (bk T msg).Good (T.baseIn A0 fun w => msg w.1) (T.par.baseOut A0 fun w => msg w.1)

/-- The sumcheck of Cb/Ld/LdPsc.lean. -/
def PscBk.lib (E : Type) [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type) :
    PscBk E Ex M Wp Kc :=
  ⟨fun T msg => ⟨T.par.psc Ex, T.par.hon Ex fun w => msg w.1, T.par.nums Ex Kc⟩,
    fun T A0 msg h1 h2 h3 h4 => psc_our_goodAt E T Ex M Wp Kc A0 msg h1 h2 h3 h4⟩

/-- The data of a tie whose first step does the work of the first two of `TieP`
(Cb/Ld/LdLkpTie.lean). -/
structure TieF (E : Type) [Field E] [Fintype E] where
  St0 : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- The public factor. -/
  a  : St0 → E
  /-- The virtual scalars. Q is read at 1, 2, .. alone. -/
  PK : St0 → (J → E) → E
  PT : St0 → (J → E) → ℕ → E
  Q  : St0 → (J → E) → ℕ → E
  /-- Own masks of step l: the coefficients of the hiding polynomial; one entry for each value:
  cAt l false for Q_(l+1), cAt l true for PT_l; cZ for PK (step 0). -/
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cZ  : J
  cAt : ℕ → Bool → J

attribute [instance] TieF.finJ TieF.decJ

variable {E : Type} [Field E] [Fintype E]

namespace TieF
variable (D : TieF E)

/-- The one condition, below n: Q_(j+1) = Q_(j+2)^2 * PT_(j+1). -/
def StepTo (n : ℕ) : Prop :=
  ∀ st m j, j < n → D.Q st m (j + 1) = D.Q st m (j + 2) ^ 2 * D.PT st m (j + 1)

/-- A step with its readers. -/
structure Lv where
  T : PscOur E
  toJ : T.J → D.J
  base : T.St → D.St0
  /-- The value that the next step takes up; the values whose claims ride along. -/
  nx : T.A
  pts : List T.A

/-- Step 0, fused: PK - a * (Q_1^2 * PT_0). -/
def TS : PscOur E where
  St := D.St0
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Option Bool
  B := Empty
  F := fun st m x _ =>
    match x with
    | none => D.PK st m
    | some b => if b then D.PT st m 0 else D.Q st m 1
  Fb := fun _ _ b _ => b.elim
  S0 := fun st _ v => v none - D.a st * (v (some false) ^ 2 * v (some true))
  S1 := fun _ _ _ b => b.elim
  DY := 3
  slS := fun _ _ => 0
  wAt := D.wAt 0
  cAt := fun x =>
    match x with
    | none => D.cZ
    | some b => D.cAt 0 b

def lv0 : D.Lv := ⟨D.TS, id, id, some false, [none, some true]⟩

/-- Step j + 1, after the step L: Q_(j+2)^2 * PT_(j+1), with the form β of L at the mask entry of
the value taken up. -/
def TN (j : ℕ) (L : D.Lv) : PscOur E where
  St := L.T.par.Out
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun o m b _ => if b then D.PT (L.base o.st) m (j + 1) else D.Q (L.base o.st) m (j + 2)
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false ^ 2 * v true
  S1 := fun _ _ _ b => b.elim
  DY := 3
  slS := fun o i => if i = L.toJ (L.T.cAt L.nx) then L.T.lst o.st (L.T.par.hp o.st o.pt) else 0
  wAt := D.wAt (j + 1)
  cAt := D.cAt (j + 1)

def lvS (j : ℕ) (L : D.Lv) : D.Lv := ⟨D.TN j L, id, fun o => L.base o.st, false, [true]⟩

/-- The steps. -/
def lv : ℕ → D.Lv
  | 0 => D.lv0
  | j + 1 => D.lvS j (lv j)

/-- The joint's own claim before step l. -/
def claim : (l : ℕ) → E × (D.lv l).T.St → (D.J → E) → Prop
  | 0 => fun x m => D.PK x.2 m - D.a x.2 * (D.Q x.2 m 1 ^ 2 * D.PT x.2 m 0) = x.1
  | l + 1 =>
    fun x m =>
      D.Q ((D.lv (l + 1)).base x.2) m (l + 1) +
          ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1

section Base
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)

/-- The entries in the naming of step l. -/
def msgAt (l : ℕ) : M → (D.lv l).T.J → E := fun ms j => msg ms ((D.lv l).toJ j)

variable {Ex M Wp Kc}

/-- What rides along after step l: what rode before, the row on the hiding coefficients, the masked
claims on the values that are not taken up. -/
def after (l : ℕ) (A : Rels Kc (D.lv l).T.St Ex (M × Wp)) :
    Rels Kc (D.lv l).T.par.Out Ex (M × Wp) :=
  ⟨fun o y w =>
      A.rel o.st y w ∧
      (D.lv l).T.par.UHolds o (D.msgAt M msg l w.1) ∧
      ∀ a ∈ (D.lv l).pts, (D.lv l).T.par.EHolds o (D.msgAt M msg l w.1) a,
    fun a w =>
      A.relR (a.1.st, a.2) w ∧
      (D.lv l).T.par.UHolds a.1 (D.msgAt M msg l w.1) ∧
      ∀ c ∈ (D.lv l).pts, (D.lv l).T.par.EHolds a.1 (D.msgAt M msg l w.1) c,
    fun a => A.on (a.1.st, a.2),
    A.core⟩

/-- What rides along before step l. -/
def ride (A0 : Rels Kc D.St0 Ex (M × Wp)) : (l : ℕ) → Rels Kc (D.lv l).T.St Ex (M × Wp)
  | 0 => A0
  | l + 1 => D.after msg l (ride A0 l)

/-- The joint before step l: the step's own claim, and what rides along. -/
def jtAt (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ) : Rels Kc (E × (D.lv l).T.St) Ex (M × Wp) :=
  ⟨fun x y w => (D.ride msg A0 l).rel x.2 y w ∧ D.claim l x (msg w.1),
    fun a w => (D.ride msg A0 l).relR (a.1.2, a.2) w ∧ D.claim l a.1 (msg w.1),
    fun a => (D.ride msg A0 l).on (a.1.2, a.2),
    (D.ride msg A0 l).core⟩

/-- The step without rounds after step l: the scalar sent for the value taken up is the next target.
-/
def nxt (l : ℕ) : (D.lv l).T.par.Out → E × (D.lv (l + 1)).T.St := fun o => (o.vals (D.lv l).nx, o)

variable (S : PscBk E Ex M Wp Kc)

/-- Step l, with the step without rounds after it. -/
def stepA (l : ℕ) : BkA Kc M (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex Wp :=
  (S.bk (D.lv l).T (D.msgAt M msg l)).postM (D.nxt l)

/-- The tie: the steps 0, .., n. -/
def tieA (n : ℕ) : BkA Kc M (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex Wp :=
  BkA.chain (fun l => E × (D.lv l).T.St) (D.stepA msg S) n

end Base
end TieF
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The first joint's own claim is the sum claim of step 0. -/
def tieF_sum0 : Prop :=
  ∀ (D : TieF E) (x : E × (D.lv 0).T.St) (m : D.J → E),
    (D.lv 0).T.SumHolds x (fun j => m ((D.lv 0).toJ j)) ↔ D.claim 0 x m

/-- The masked claim on Q_(l+1) is the sum claim of step l + 1, where Q_(l+1) = Q_(l+2)² · PT_(l+1).
-/
def tieF_sum : Prop :=
  ∀ (D : TieF E) (l : ℕ) (x : E × (D.lv (l + 1)).T.St) (m : D.J → E),
    D.Q ((D.lv (l + 1)).base x.2) m (l + 1) =
      D.Q ((D.lv (l + 1)).base x.2) m (l + 2) ^ 2 * D.PT ((D.lv (l + 1)).base x.2) m (l + 1) →
    ((D.lv (l + 1)).T.SumHolds x (fun j => m ((D.lv (l + 1)).toJ j)) ↔ D.claim (l + 1) x m)

/-- The form of the claim before step l + 1: β of step l at the mask entry of the value taken up, 0
elsewhere. -/
def tieF_form : Prop :=
  ∀ (D : TieF E) (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E), ∑ j,
      (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) =
    (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt) *
      m ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx))

/-- The conditions of the sumcheck hold at every step. -/
def tieF_ok : Prop :=
  ∀ (D : TieF E) (l : ℕ), (D.lv l).T.VarsOK ∧ (D.lv l).T.ValInj ∧ (D.lv l).T.DegX ∧ (D.lv l).T.DegY

/-- One step. -/
def tieF_step : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (S : PscBk E Ex M Wp Kc) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ),
    D.StepTo l → (D.stepA msg S l).Good (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1))

/-- The tie, at the base. -/
def tieF_chain : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (S : PscBk E Ex M Wp Kc) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (n : ℕ),
    D.StepTo n → (D.tieA msg S n).Good (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1))

/-- The tie over a signature, under D.StepTo n. -/
def tieF_sig : Prop :=
  ∀ (D : TieF E) (Sg : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (S : PscBk E E₀ Sg.Msg Wp Kc)
      (msg : Sg.Msg → D.J → E) (A0 : Rels Kc D.St0 E₀ (Sg.Msg × Wp)) (n : ℕ),
    D.StepTo n →
    GoodB ((D.tieA msg S n).R.keep Sg.Smp Sg.ext) (Sg.liftH (D.tieA msg S n).H)
      (Sg.over (D.jtAt msg A0 0)) (Sg.over (D.jtAt msg A0 (n + 1))) (fun _ _ w => w)
      ((D.tieA msg S n).P.keep Sg.Smp Sg.ext)

/-- With `PscBk.lib`: 3 (n + 1) rounds. -/
def tieF_rounds : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ),
    (D.tieA msg (PscBk.lib E Ex M Wp Kc) n).R.shape.length = 3 * (n + 1)

/-- With `PscBk.lib`: errors and numbers of values, round by round: (1, 3, 0) of (q, q - 1, 1),
n + 1 times; q = |E|. -/
def tieF_ll : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ),
    LL (D.tieA msg (PscBk.lib E Ex M Wp Kc) n) ((List.range (n + 1)).flatMap fun _ => [1, 3, 0])
      ((List.range (n + 1)).flatMap fun _ => [Fintype.card E, Fintype.card E - 1, 1])

/-- At the programs' 32 planes (n + 2 = 32; said so, and not with the numeral 30 in n's place,
because Lean then unfolds 31 nested states while it reads the statement): 31 sumchecks, 93 rounds;
the errors are these numerals: 1 of |E|, 3 of |E| - 1, none. That they are the shipped planner's
numbers is no part of this statement. -/
def tieF_errs31 : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ), n + 2 = 32 →
    (D.tieA msg (PscBk.lib E Ex M Wp Kc) n).P.err.toList = (List.replicate 31 [1, 3, 0]).flatten ∧
    (D.tieA msg (PscBk.lib E Ex M Wp Kc) n).R.shape.chalList =
      (List.replicate 31 [Fintype.card E, Fintype.card E - 1, 1]).flatten ∧
    (D.tieA msg (PscBk.lib E Ex M Wp Kc) n).R.shape.length = 93

/-- No bound is at least 1: if 5 ≤ |E|, every error is below its number of values. -/
def tieF_small : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ),
    5 ≤ Fintype.card E → (D.tieA msg (PscBk.lib E Ex M Wp Kc) n).P.err.Small

/-- What rides along after a step, written out: the masked claims on PK and on PT_0 (after step 0),
on PT_(j+1) (after step j + 1). -/
def tieF_ride : Prop :=
  ∀ (D : TieF E) (m : D.J → E),
    (∀ o : (D.lv 0).T.par.Out,
      ((D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (none : Option Bool) ↔
        D.PK o.st m + m D.cZ * (D.lv 0).T.lst o.st ((D.lv 0).T.par.hp o.st o.pt) =
          o.vals (none : Option Bool)) ∧
      ((D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (some true : Option Bool) ↔
        D.PT o.st m 0 + m (D.cAt 0 true) * (D.lv 0).T.lst o.st ((D.lv 0).T.par.hp o.st o.pt) =
          o.vals (some true : Option Bool))) ∧
    ∀ (j : ℕ) (o : (D.lv (j + 1)).T.par.Out),
      (D.lv (j + 1)).T.par.EHolds o (fun i => m ((D.lv (j + 1)).toJ i)) true ↔
      D.PT ((D.lv (j + 1)).base o.st) m (j + 1) +
          m (D.cAt (j + 1) true) * (D.lv (j + 1)).T.lst o.st ((D.lv (j + 1)).T.par.hp o.st o.pt) =
        o.vals true

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E] (D : TieF E)

theorem LdLkp.TieF.cover : ∀ (l : ℕ) (a : (D.lv l).T.A), a = (D.lv l).nx ∨ a ∈ (D.lv l).pts
  | 0, none => Or.inr (show (none : Option Bool) ∈ [none, some true] from List.mem_cons_self)
  | 0, some false => Or.inl rfl
  | 0, some true =>
    Or.inr (show (some true : Option Bool) ∈ [none, some true] from
      List.mem_cons_of_mem _ List.mem_cons_self)
  | _ + 1, false => Or.inl rfl
  | _ + 1, true => Or.inr (show true ∈ [true] from List.mem_cons_self)

/-- The value that the next step takes up is Q_(l+1). -/
theorem LdLkp.TieF.F_nx :
    ∀ (l : ℕ) (st : (D.lv l).T.St) (m : D.J → E) (X : HPt ((D.lv l).T.vars st)),
      (D.lv l).T.F st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx X =
        D.Q ((D.lv l).base st) m (l + 1)
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

theorem LdLkp.TieF.fmt_nil : ∀ l, (D.lv l).T.fmt = []
  | 0 => rfl
  | _ + 1 => rfl

theorem LdLkp.TieF.dy3 : ∀ l, (D.lv l).T.DY = 3
  | 0 => rfl
  | _ + 1 => rfl

/-- The place of the mask of the value taken up. -/
theorem LdLkp.TieF.c_nx : ∀ l, (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) = D.cAt l false
  | 0 => rfl
  | _ + 1 => rfl

end

section
variable (E : Type) [Field E] [Fintype E]

theorem tieF_sum0 : Spec.tieF_sum0 E := by
  intro D x m
  show (D.PK x.2 m - D.a x.2 * (D.Q x.2 m 1 ^ 2 * D.PT x.2 m 0) +
          ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
        ∑ j : D.J, (0 : E) * m j = x.1 ↔
    D.PK x.2 m - D.a x.2 * (D.Q x.2 m 1 ^ 2 * D.PT x.2 m 0) = x.1
  simp

theorem tieF_sum : Spec.tieF_sum E := by
  intro D l x m h
  show (D.Q ((D.lv (l + 1)).base x.2) m (l + 2) ^ 2 * D.PT ((D.lv (l + 1)).base x.2) m (l + 1) +
          ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
        ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1 ↔
    D.Q ((D.lv (l + 1)).base x.2) m (l + 1) +
        ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) =
      x.1
  rw [h, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

theorem tieF_form : Spec.tieF_form E := by
  intro D l o m
  show ∑ j : D.J,
      (if j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) then
            (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)
          else 0) * m j = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype E] in
variable {E} in
/-- The fused summand has degree 3 along every line. -/
theorem tieF_deg3z (a : E) (v u : Option Bool → E) :
    ∃ c : Fin (3 + 1) → E, ∀ y : E,
      (v none + u none * y) -
          a * ((v (some false) + u (some false) * y) ^ 2 * (v (some true) + u (some true) * y)) =
        hev c y :=
  ⟨![v none - a * (v (some false) ^ 2 * v (some true)),
      u none - a * (2 * v (some false) * u (some false) * v (some true) +
        v (some false) ^ 2 * u (some true)),
      - (a * (u (some false) ^ 2 * v (some true) +
        2 * v (some false) * u (some false) * u (some true))),
      - (a * (u (some false) ^ 2 * u (some true)))], fun y => by
    simp [hev, Fin.sum_univ_four]
    ring⟩

theorem tieF_ok : Spec.tieF_ok E := by
  intro D l
  cases l with
  | zero =>
    refine ⟨fun _ _ hv => absurd hv (List.not_mem_nil),
      fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial,
      fun st _ v u r => ?_⟩
    obtain ⟨c, hc⟩ := tieF_deg3z (D.a st) v u
    refine ⟨c, fun y => ?_⟩
    show (v none + u none * y) -
          D.a st * ((v (some false) + u (some false) * y) ^ 2 *
            (v (some true) + u (some true) * y)) +
        ∑ b : Empty, (b.elim : E) * r b = hev c y
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact hc y
  | succ l =>
    refine ⟨fun _ _ hv => absurd hv (List.not_mem_nil),
      fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial,
      fun _ _ v u r => ?_⟩
    obtain ⟨c, hc⟩ := ldLkpTie_deg3 v u
    refine ⟨c, fun y => ?_⟩
    show (v false + u false * y) ^ 2 * (v true + u true * y) + ∑ b : Empty, (b.elim : E) * r b =
      hev c y
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact hc y

/-- The row on the value taken up is the next joint's own claim. -/
theorem tieF_next (D : TieF E) (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    (D.lv l).T.par.EHolds o (fun j => m ((D.lv l).toJ j)) (D.lv l).nx ↔
    D.claim (l + 1) (D.nxt l o) m := by
  refine (psc_our_val E (D.lv l).T o _ (D.lv l).nx).trans ?_
  have hF : (D.lv l).T.F o.st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx
        ((D.lv l).T.ini o.st ((D.lv l).T.par.hp o.st o.pt)) =
      D.Q ((D.lv l).base o.st) m (l + 1) :=
    D.F_nx l o.st m _
  show _ ↔ D.Q ((D.lv l).base o.st) m (l + 1) +
        ∑ j, (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) =
      o.vals (D.lv l).nx
  have h2 := (tieF_form E D l o m).trans (mul_comm _ _)
  exact ⟨fun h => (congrArg₂ (· + ·) hF.symm h2).trans h,
    fun h => (congrArg₂ (· + ·) hF h2.symm).trans h⟩

/-- Under `D.StepTo l`: the input joint of the sumcheck of step l is the joint before step l. -/
theorem tieF_jt (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
    (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ) (hS : D.StepTo l) :
    (D.lv l).T.baseIn (D.ride msg A0 l) (fun w => D.msgAt M msg l w.1) = D.jtAt msg A0 l := by
  have h : ∀ (x : E × (D.lv l).T.St) (m : D.J → E),
      (D.lv l).T.SumHolds x (fun j => m ((D.lv l).toJ j)) ↔ D.claim l x m := by
    cases l with
    | zero => exact tieF_sum0 E D
    | succ l => exact fun x m => tieF_sum E D l x m (hS _ m l (Nat.lt_succ_self l))
  exact rels_ext
    (funext fun x =>
      funext fun y => funext fun w => propext (and_congr_right fun _ => h x (msg w.1)))
    (funext fun a => funext fun w => propext (and_congr_right fun _ => h a.1 (msg w.1))) rfl rfl

theorem tieF_step : Spec.tieF_step E := by
  intro D Ex M Wp Kc S msg A0 l hS
  have ok := tieF_ok E D l
  have g1 := S.good (D.lv l).T (D.ride msg A0 l) (D.msgAt M msg l) ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
  rw [tieF_jt E D Ex M Wp Kc msg A0 l hS] at g1
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ (D.jtAt msg A0 (l + 1)) _ _ (D.nxt l) g1 ?_
    (fun _ _ h => h) (fun _ => rfl) ?_
  · intro o y w h
    exact ⟨⟨h.1, h.2.1, fun a _ => h.2.2 a⟩, (tieF_next E D l o (msg w.1)).1 (h.2.2 _)⟩
  · intro o y w _ h
    refine ⟨h.1.1, h.1.2.1, fun a => ?_⟩
    rcases D.cover l a with rfl | ha
    · exact (tieF_next E D l o (msg w.1)).2 h.2
    · exact h.1.2.2 a ha

theorem tieF_chain : Spec.tieF_chain E := by
  intro D Ex M Wp Kc S msg A0 n hS
  exact ldLkpP_chain Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.stepA msg S)
      (D.jtAt msg A0) n fun l hl =>
    tieF_step E D Ex M Wp Kc S msg A0 l fun st m j hj => hS st m j (Nat.lt_of_lt_of_le hj hl)

theorem tieF_sig : Spec.tieF_sig E := by
  intro D Sg E₀ Wp Kc S msg A0 n hS
  exact sigLift_goodB E Sg Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (tieF_chain E D E₀ Sg.Msg Wp Kc S msg A0 n hS)

theorem tieF_llStep (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (l : ℕ) :
    LL (D.stepA msg (PscBk.lib E Ex M Wp Kc) l) [1, 3, 0]
      [Fintype.card E, Fintype.card E - 1, 1] := by
  have h := ll_psc (D.lv l).T 0 2 (D.fmt_nil l) Ex Kc
  rw [D.dy3 l] at h
  exact h

theorem tieF_ll : Spec.tieF_ll E := fun D Ex M Wp Kc msg n =>
  ll_chain _ _ _ _ (tieF_llStep E D Ex M Wp Kc msg) n

theorem chalList_len : ∀ s : Shape, s.chalList.length = s.length
  | [] => rfl
  | _ :: s => congrArg (· + 1) (chalList_len s)

theorem tieF_rounds : Spec.tieF_rounds E := by
  intro D Ex M Wp Kc msg n
  have h := congrArg List.length (tieF_ll E D Ex M Wp Kc msg n).2
  rw [chalList_len] at h
  rw [h, flat_len]
  simp
  ring

theorem flat_rep (c : List ℕ) :
    ∀ k, (List.range k).flatMap (fun _ => c) = (List.replicate k c).flatten
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, flat_rep c k, List.replicate_succ',
      List.flatten_append]
    simp

theorem tieF_errs31 : Spec.tieF_errs31 E := by
  intro D Ex M Wp Kc msg n hn
  have h := tieF_ll E D Ex M Wp Kc msg n
  have h31 : n + 1 = 31 := by omega
  refine ⟨h.1.trans ?_, h.2.trans ?_, (tieF_rounds E D Ex M Wp Kc msg n).trans (by omega)⟩
  · rw [flat_rep, h31]
  · rw [flat_rep, h31]

theorem tieF_small : Spec.tieF_small E := by
  intro D Ex M Wp Kc msg n hq
  rw [chainErr_small, (tieF_ll E D Ex M Wp Kc msg n).1, (tieF_ll E D Ex M Wp Kc msg n).2]
  refine f2_flat _ _ (fun _ => ?_) (n + 1)
  exact List.Forall₂.cons (by omega) (List.Forall₂.cons (by omega)
    (List.Forall₂.cons (by omega) List.Forall₂.nil))

theorem tieF_ride : Spec.tieF_ride E := by
  intro D m
  exact ⟨fun o => ⟨psc_our_val E (D.lv 0).T o _ (none : Option Bool),
      psc_our_val E (D.lv 0).T o _ (some true : Option Bool)⟩,
    fun j o => psc_our_val E (D.lv (j + 1)).T o _ true⟩

end
end Cb
