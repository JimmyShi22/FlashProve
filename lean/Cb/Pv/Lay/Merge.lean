-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Merge.lean: the merge of a sub-proof's claims on the committed weights, as an interactive
oracle reduction with its knowledge soundness.

A layers' sub-proof ends with claims "the weights of a unit, under given factors, sum to v". After
they have been combined under the powers of one element (Cb/Pv/Lay/Draws.lean), one sumcheck over
the column bits of the committed matrix is left. The claim is
    (sum over the corners x of the cube of f(x)) + < inc, m > = target,
where f is treated as ONE map of the point, of degree at most 2 in each variable, inc reads the
masks of the combined values, and the target is public. The rounds, as the programs have them: the
sum of the hiding polynomial, then a coefficient; one round for each column bit, under the plain sum
g(0) + g(1), in which the constant and the quadratic coefficient are sent and the LINEAR one is left
out; one round in a further variable, with one scalar; the one end value.

The mask of the end value may be an entry of another message than the block's other masks: `cAt` is
any name in J. (In the programs it is an entry of the request's index-mask message.)

Main names:
  `MergeL`: the parameters. `deg` is a condition on f, held in the record.
  `MergeL.T`: the sumcheck's record, a value of the library's builder: every variable under the
    plain form; one revealed map; degree 1 in the further variable.
  `MergeL.conds`, `MergeL.sum_iff`, `MergeL.out_iff`: the four conditions; what the input claim
    says; what the output claims say: one row on names, and the row f(point) + m (cAt) * beta = the
    end value.
  `MergeL.blk V`, `MergeL.knowAt`, `MergeL.know`, `MergeL.errs`: the reduction for any short
    sumcheck V; its knowledge soundness for each fixed tuple of messages; its errors: 1, then 2 for
    each variable, then 1, 0.
  `pick`, `MergeL.pick_ok`: which coefficient is left out: the linear one in a plain round, the
    constant one in the further variable; that choice is lawful. `MergeL.V1`: the short sumcheck
    with that choice.

Limits: nothing is said on what f is in the model, nor on the fate of the row on the end value. The
field `deg` (f has degree at most 2 in each variable) is to be paid by whoever fills the record.
Nothing is said on the honest prover, on completeness or on zero knowledge. V is any short sumcheck
in the sense of Cb/G6/Letter.lean. That record lays no law on what V's verifier accepts: one that
refuses everything fills it, and the statements here hold of it too. The errors are counts of bad
draws in a round, out of the set that is drawn from: all of E; in the round of the further variable,
E without 0. "As the programs have them" is by reading the programs: nothing here compares the
rounds with them (the planner's lists: OnBytes/Tie/Pv/Lay/Rounds.lean). No file of this folder joins
this block's output claims to another block's input claims.

-/
import Cb.G6.Pick
import Cb.G6.Join
import Cb.Part.LdPartPost
import Cb.Part.LdPartPscProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-- The parameters of the merge. -/
structure MergeL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the number of column bits -/
  k : ℕ
  St : Type
  /-- the summand, as one map of the point -/
  f : St → (J → E) → (Fin k → E) → E
  deg : ∀ st m, Alg.DegLE (fun _ : Fin k => 2) (f st m)
  inc : Slf E St J
  tg : St → E
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 1]) → J
  cAt : J
  Rd : St → (J → E) → Prop

attribute [instance] MergeL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace MergeL
variable (L : MergeL E)

@[reducible] def Sm : LdPartSm E L.St L.J where
  k := L.k
  A := Unit
  F := fun st m _ z => L.f st m z
  terms := [⟨fun _ _ => 1, [()]⟩]
  w := fun _ _ => none

@[reducible] def Mk : LdPartMk L.Sm := ⟨fun _ => 2, 1, L.inc, L.wAt, fun _ => L.cAt⟩

theorem ok : L.Sm.OK L.Mk (fun _ _ => 2) where
  map := fun st m _ => L.deg st m
  fit := fun t ht => by
    rw [List.mem_singleton.1 ht]
    exact ⟨fun _ => 0, fun st => Alg.DegLE.const _ _, fun _ => by simp⟩
  plain := fun _ _ _ => by norm_num
  dy := fun t ht => by
    rw [List.mem_singleton.1 ht]
    simp

/-- The sumcheck's record. -/
abbrev T : PscOur E := L.Sm.our L.Mk

theorem conds : L.T.VarsOK ∧ L.T.ValInj ∧ L.T.DegX ∧ L.T.DegY := ldPartPsc_ok E _ _ _ _ _ L.ok

/-- The input claim. -/
def Sg (st : L.St) (m : L.J → E) : Prop :=
  ∑ b : Fin L.k → Bool, L.f st m (Alg.corner b) + ∑ j, L.inc st j * m j = L.tg st

theorem sum_iff (t : E) (st : L.St) (m : L.J → E) :
    L.T.SumHolds (t, st) m ↔
      ∑ b : Fin L.k → Bool, L.f st m (Alg.corner b) + ∑ j, L.inc st j * m j = t := by
  rw [ldPartPsc_sum E]
  have hc : ∀ b : Fin L.k → Bool,
      (∏ i, ldPartWt (L.Sm.w st i) (b i)) * L.Sm.val st m (Alg.corner b) = L.f st m
          (Alg.corner b) := by
    intro b
    unfold LdPartSm.val LdPartSm.pol
    simp [ldPartWt]
  simp only [hc]

abbrev oPt (o : L.T.par.Out) : Fin L.k → E := L.Sm.outPt L.Mk o
abbrev oBe (o : L.T.par.Out) : E := L.Sm.outB L.Mk o

/-- the one row on names -/
@[reducible] def Rw1 : LdPartRw E L.T.par.Out L.J where
  Jr := Unit
  co := fun o _ n => L.T.par.slU (fun _ b => b.elim) o n
  tg := fun o _ => L.T.par.tU o

/-- the row on the end value -/
def EV (o : L.T.par.Out) (m : L.J → E) : Prop :=
  L.f o.st m (L.oPt o) + m L.cAt * L.oBe o = o.vals ()

theorem ev_iff (o : L.T.par.Out) (m : L.J → E) : L.T.par.EHolds o m () ↔ L.EV o m :=
  ldPartPsc_val E _ _ L.Sm L.Mk o m ()

theorem row_iff (o : L.T.par.Out) (m : L.J → E) : L.T.par.UHolds o m ↔ L.Rw1.Says o m := by
  rw [psc_row_U E L.T.par (fun _ b => b.elim) (fun _ _ b => b.elim) o m]
  exact ⟨fun h _ => h, fun h => h ()⟩

theorem out_iff (o : L.T.par.Out) (m : L.J → E) : L.T.par.OutHolds o m
    ↔ L.Rw1.Says o m ∧ L.EV o m :=
  and_congr (L.row_iff o m) ⟨fun h => (L.ev_iff o m).1 (h ()), fun h _ => (L.ev_iff o m).2 h⟩

/-! ### The reduction -/

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)

/-- what rides: the base, and what else is claimed -/
@[reducible] def A0 : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ L.Rd st (msg w.1), fun a w => R0.relR a w ∧ L.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

/-- the joint before the block: what rides, and the sum claim -/
@[reducible] def relIn : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => (L.A0 R0 msg).rel st y w ∧ L.Sg st (msg w.1),
    fun a w => (L.A0 R0 msg).relR a w ∧ L.Sg a.1 (msg w.1), R0.on, R0.core⟩

/-- the joint behind the block: what rides, and the output claims -/
@[reducible] def relOut : Rels Kc L.T.par.Out Ex (M × Wp) :=
  ⟨fun o y w => (L.A0 R0 msg).rel o.st y w ∧ L.Rw1.Says o (msg w.1) ∧ L.EV o (msg w.1),
    fun a w => (L.A0 R0 msg).relR (a.1.st, a.2) w ∧ L.Rw1.Says a.1 (msg w.1) ∧ L.EV a.1 (msg w.1),
    fun a => R0.on (a.1.st, a.2), R0.core⟩

variable (V : ShortK L.T.par Ex)

/-- The reduction: the target is read off the state; the short sumcheck. -/
def blk : IOR L.St Ex L.T.par.Out Ex := V.R.pre (fun st => some (L.tg st, st)) (ExtMap.id Ex)

theorem knowAt :
    KnowAt (L.blk V) (L.relIn R0 msg) (L.relOut R0 msg) (fun _ _ _ wp => wp) V.ε := by
  obtain ⟨hV, hI, hX, hY⟩ := L.conds
  have h1 := V.know ((psc_our_ok E L.T).1 hV) (psc_our_deg E L.T hX hY) ((psc_our_ok E L.T).2 hI)
    M Wp Kc (L.A0 R0 msg) msg
  have h2 : KnowAt (L.blk V) (L.relIn R0 msg)
      (L.T.par.baseOut (L.A0 R0 msg) fun w => msg w.1) (fun _ _ _ wp => wp) V.ε :=
    knowAt_preMap (A' := L.relIn R0 msg) (A := L.T.par.baseIn (L.A0 R0 msg) fun w => msg w.1)
      (fun st => (L.tg st, st)) (fun _ _ h => h)
      (fun st _ w _ h => ⟨h.1, (L.sum_iff (L.tg st) st _).1 ((psc_our_sum E L.T _ _).1 h.2)⟩) h1
  exact knowAt_mono h2 (fun _ h => h) (fun _ _ _ h => h)
    (fun b w _ h => ⟨h.1, (L.out_iff b.1 _).2 h.2⟩) (fun _ h => h)

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk V).red.Know (L.relIn R0 msg).on (fun a wp => (L.relIn R0 msg).relR a (m, wp))
      (fun b wp => (L.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp) V.ε :=
  (L.knowAt R0 msg V).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList V.ε = 1 :: (List.replicate L.k 2 ++ [1, 0]) := by
  rw [V.nums]
  have h : L.T.par.fmt.map PFmt.n = List.replicate L.k 2 ++ [1] := by
    show ((ldPartFmt E L.k fun _ => 2) ++ [pDummy E 1]).map PFmt.n = _
    rw [List.map_append, ldPartVars_degs E]
    simp [List.ofFn_const]
    rfl
  rw [h]
  simp

end Block

end MergeL

/-! ### Which coefficient is left out -/

open Classical in
/-- Where the sum of the constant 1 is 1, the constant coefficient; else the linear one. -/
def pick {R : Type} [CommRing R] : (l : List (HVar R)) → HFixs l
  | [] => ()
  | v :: l => ((if v.mon 0 = 1 then 0 else if h : 1 ≤ v.n then
      ⟨1, Nat.lt_succ_of_le h⟩ else 0, 1), pick l)

theorem pick_ok {R : Type} [CommRing R] : ∀ l : List (HVar R),
    (∀ v ∈ l, v.mon 0 = 1 ∨ ∃ h : 1 ≤ v.n, v.mon ⟨1, Nat.lt_succ_of_le h⟩ = 1) → HFixs.OK l (pick l)
  | [], _ => trivial
  | v :: l, h =>
    ⟨by
      classical
      show (1 : R) * v.mon (if v.mon 0 = 1 then 0 else if h : 1 ≤ v.n then
          ⟨1, Nat.lt_succ_of_le h⟩ else 0) = 1
      rw [one_mul]
      by_cases h0 : v.mon 0 = 1
      · rw [if_pos h0, h0]
      · rw [if_neg h0]
        rcases h v (List.mem_cons_self ..) with h1 | ⟨h1, h2⟩
        · exact absurd h1 h0
        · rw [dif_pos h1, h2],
     pick_ok l fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

theorem mon1_plain (n : ℕ) (h : 1 ≤ n) :
    ((pfCube E n).var (pdPlain E n)).mon ⟨1, Nat.lt_succ_of_le h⟩ = 1 := by
  show ∑ b : Bool, (1 : E) * (if b then (1 : E) else 0) ^ 1 = 1
  rw [Fintype.sum_bool]
  simp

theorem plain_vars : ∀ (k : ℕ) (dg : Fin k → ℕ), (∀ i, 1 ≤ dg i) →
    ∀ v ∈ pVars (ldPartFmt E k dg) (ldPartDat E k dg fun _ => none),
      v.mon 0 = 1 ∨ ∃ h : 1 ≤ v.n, v.mon ⟨1, Nat.lt_succ_of_le h⟩ = 1
  | 0, _, _ => fun _ hv => absurd hv (List.not_mem_nil)
  | k + 1, dg, hd => fun v hv => by
    rcases List.mem_cons.1 hv with h1 | h1
    · rw [h1]
      exact Or.inr ⟨hd 0, mon1_plain (dg 0) (hd 0)⟩
    · exact plain_vars k (fun i => dg i.succ) (fun i => hd i.succ) v h1

namespace MergeL
variable (L : MergeL E)

/-- the programs' choice -/
def F1 : ∀ st, HFixs (L.T.par.vars st) := fun st => pick (L.T.par.vars st)

theorem pick_ok (st : L.St) : HFixs.OK (L.T.par.vars st) (L.F1 st) :=
  Cb.Pv.Lay.pick_ok _ fun v hv => by
    rcases mem_snoc L.T.fmt (L.T.dat st) (pDummy E L.T.DY) (pDummyD E L.T.DY) v hv with h1 | h1
    · exact plain_vars L.k (fun _ => 2) (fun _ => by norm_num) v h1
    · rw [h1]
      exact Or.inl (mon0_dummy L.T.DY)

/-- the short sumcheck with that choice -/
def V1 (Ex : ExtSpec) : ShortK L.T.par Ex := shortK L.T.par L.F1 Ex

end MergeL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.MergeL.conds
#print axioms Cb.Pv.Lay.MergeL.sum_iff
#print axioms Cb.Pv.Lay.MergeL.out_iff
#print axioms Cb.Pv.Lay.MergeL.knowAt
#print axioms Cb.Pv.Lay.MergeL.errs
#print axioms Cb.Pv.Lay.MergeL.pick_ok
