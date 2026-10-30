-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Rows.lean: the products of the norms' rows: hidden sums are sent, batched, and proved by
one sumcheck over the token positions. One interactive oracle reduction with its knowledge
soundness.

What is to be shown: a claim (`led`) on np sums. Sum n is the sum over the token positions, under
equality weights at a point, of the product of two shown vectors. The claim may tie several sums
in one line (in the programs' ledger one line has two of a norm's seven products, and two lines
have none), and it may read the entries of the committed messages. The prover sends, for each n,
the sum under a mask of its own. That splits the claim in two under new names: (A) each sum plus
its mask is the sent scalar; (B) `led` holds of the sent scalars minus their masks. The claim (B)
rides on. The claims (A) are combined under the powers of one drawn element, from the power 0 on,
and the combination is proved by the sumcheck of Cb/Pv/Lay/Tok.lean, whose own claimed sum is
hidden and sent too; a linear row (`tie`) ties it to the sent scalars. The rounds, as the programs
have them: np scalars, then the element; then the sumcheck's.

Main names:
  `RowsL`: the parameters.
  `RowsL.Idn`: `led` of the np sums. `RowsL.slots`: the claim (B). `RowsL.tie`: the linear row.
    `RowsL.Psi`: the claim (B) and the linear row.
  `RowsL.tok`: the sumcheck's parameters: states ((old state, sent scalars), element); one term
    for each n, with the power of the element as its coefficient; no kept vector; degree 2.
  `RowsL.few`: if `led` fails of the np sums then, whatever is sent, at most np - 1 elements leave
    (B) and the combination of (A) true. `RowsL.th_iff`: these are Psi at the sumcheck's true
    masked sum.
  `RowsL.blk`, `RowsL.knowAt`, `RowsL.know`: the reduction and its knowledge soundness for each
    fixed tuple of messages: from "what rides, and `led` of the np sums" to "what rides, the claim
    (B), the linear row at the sent sum, and the sumcheck's output claims".
  `RowsL.errs`: its errors: np - 1, 1, then 2 for each bit, then 2, 0.

Limits: nothing is said on what the vectors, the point and the claim `led` are in the model; that
the programs' rows are `slots` and `tie` is not shown here. The errors are numbers of bad draws,
round by round. Every draw is from the whole field, but the further variable's, which is from the
elements other than 0. "For each fixed tuple of messages" asks of a user that every entry that the
maps, forms and claims of the record read is fixed before the block's first draw. Nothing is said
on the honest prover, on completeness or on zero knowledge. The sentences on what the programs do
are by reading: nothing is compared with the programs here. This reduction is not joined to the
one before it or behind it in the sub-proof: that the two joints agree is not shown in this
folder.

-/
import Cb.Pv.Lay.Tok
import Cb.Pv.Lay.Draws
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Johnson.L5.Door

noncomputable section

/-- The parameters. -/
structure RowsL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the number of bits of a position; the number of products -/
  k : ℕ
  np : ℕ
  St : Type
  /-- the shown vectors; the two factors of each product -/
  A : Type
  [finA : Fintype A]
  vA : St → (J → E) → A → ℕ → E
  pr : Fin np → A × A
  pnt : St → Fin k → E
  /-- what is to be shown of the np sums -/
  led : St → (J → E) → (Fin np → E) → Prop
  /-- own masks: the sent sums'; the sumcheck's -/
  mkAt : Fin np → J
  rJ : J
  wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : A → J
  /-- what else is claimed of state and entries -/
  Rd : St → (J → E) → Prop

attribute [instance] RowsL.finJ RowsL.finA

variable {E : Type} [Field E] [Fintype E]

namespace RowsL
variable (L : RowsL E)

/-- the states behind the first round -/
abbrev X2 : Type := (L.St × (Fin L.np → E)) × E

/-- the n-th sum -/
def pA (st : L.St) (m : L.J → E) (n : Fin L.np) : E :=
  Blocks.ext L.k (fun X => L.vA st m (L.pr n).1 X * L.vA st m (L.pr n).2 X) (Blocks.nat (L.pnt st))

/-- what is to be shown: `led` of the np sums -/
def Idn (st : L.St) (m : L.J → E) : Prop := L.led st m (L.pA st m)

/-- the claim (B) -/
def slots (x : L.X2) (m : L.J → E) : Prop := L.led x.1.1 m fun n => x.1.2 n - m (L.mkAt n)

/-- the combined claims (A) -/
def bsum (x : L.X2) (m : L.J → E) : Prop :=
  ∑ n : Fin L.np, x.2 ^ (n : ℕ) * L.pA x.1.1 m n + ∑ n : Fin L.np, x.2 ^ (n : ℕ) * m (L.mkAt n) =
    ∑ n : Fin L.np, x.2 ^ (n : ℕ) * x.1.2 n

/-- the linear row that ties the sumcheck's sent sum z to the sent scalars -/
def tie (x : L.X2) (z : E) (m : L.J → E) : Prop :=
  (z - m L.rJ) - ∑ n : Fin L.np, x.2 ^ (n : ℕ) * (x.1.2 n - m (L.mkAt n)) = 0

def Psi (x : L.X2) (z : E) (m : L.J → E) : Prop := L.slots x m ∧ L.tie x z m

theorem few (st : L.St) (m : L.J → E) (h : ¬ L.Idn st m) (s : Fin L.np → E) :
    cnt (fun σ => L.slots ((st, s), σ) m ∧ L.bsum ((st, s), σ) m) ≤ L.np - 1 := by
  refine le_trans (cnt_mono fun σ hσ => ?_)
    (cnt_badPow fun n => L.pA st m n - (s n - m (L.mkAt n)))
  obtain ⟨h1, h2⟩ := hσ
  refine ⟨fun h0 => h ?_, ?_⟩
  · have e : L.pA st m = fun n => s n - m (L.mkAt n) :=
      funext fun n => sub_eq_zero.1 (congrFun h0 n)
    show L.led st m (L.pA st m)
    rw [e]
    exact h1
  have h3 : ∑ n : Fin L.np, σ ^ (n : ℕ) * L.pA st m n + ∑ n : Fin L.np, σ ^ (n : ℕ) * m (L.mkAt n) =
      ∑ n : Fin L.np, σ ^ (n : ℕ) * s n := h2
  simp only [mul_sub, sum_sub_distrib]
  rw [← h3]
  ring

/-- The sumcheck's parameters. -/
@[reducible] def tok : TokL E where
  J := L.J
  k := L.k
  St := L.X2
  A := L.A
  B := Empty
  vA := fun x m a => L.vA x.1.1 m a
  vB := fun _ _ b => b.elim
  pnt := fun x => L.pnt x.1.1
  t0 := (List.finRange L.np).map fun (n : Fin L.np) =>
    (fun x : L.X2 => x.2 ^ (n : ℕ), [(L.pr n).1, (L.pr n).2])
  tb := fun b => b.elim
  C := Empty
  vC := fun _ c => c.elim
  tc := fun b => b.elim
  dy := 2
  h0 := fun t ht => by
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ht
    exact ⟨le_refl _, le_refl _⟩
  hb := fun b => b.elim
  rJ := L.rJ
  wAt := L.wAt
  cAt := L.cAt
  Rd := fun x m => L.Rd x.1.1 m

omit [Fintype E] in
theorem ext_sum (g : ℕ) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → ℕ → E) (pt : ℕ → E) :
    Blocks.ext g (fun X => ∑ n ∈ s, c n * v n X) pt = ∑ n ∈ s, c n * Blocks.ext g (v n) pt := by
  unfold Blocks.ext
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun X _ => by ring

/-- the sumcheck's true sum is the combination of the np sums -/
theorem smd_ext (x : L.X2) (m : L.J → E) :
    Blocks.ext L.k (L.tok.smd x m) (Blocks.nat (L.pnt x.1.1)) =
      ∑ n : Fin L.np, x.2 ^ (n : ℕ) * L.pA x.1.1 m n := by
  have e : L.tok.smd x m = fun X => ∑ n : Fin L.np,
      x.2 ^ (n : ℕ) * (L.vA x.1.1 m (L.pr n).1 X * L.vA x.1.1 m (L.pr n).2 X) := by
    funext X
    unfold TokL.smd
    rw [Fintype.sum_empty, add_zero, Fin.sum_univ_def, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun n _ => ?_)
    simp
  rw [e, ext_sum]
  rfl

/-- the claims behind the first round are Psi at the sumcheck's true masked sum -/
theorem th_iff (x : L.X2) (m : L.J → E) :
    (L.slots x m ∧ L.bsum x m) ↔ L.Psi x (tsum L.tok.toSum.T.par x m) m := by
  unfold Psi
  refine and_congr_right fun _ => ?_
  unfold bsum tie
  rw [L.tok.tsum_eq, L.smd_ext, add_sub_cancel_right]
  simp only [mul_sub, sum_sub_distrib]
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    have h' := sub_eq_zero.1 h
    rw [h']
    ring

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc L.St Ex (M × Wp)) (msg : M → L.J → E)

/-- what rides -/
@[reducible] def A0 : Rels Kc L.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ L.Rd st (msg w.1),
    fun a w => R0.relR a w ∧ L.Rd a.1 (msg w.1), R0.on, R0.core⟩

/-- the base, read at the old state -/
@[reducible] def R2 : Rels Kc L.X2 Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1.1 y w, fun a w => R0.relR (a.1.1.1, a.2) w,
    fun a => R0.on (a.1.1.1, a.2), R0.core⟩

/-- the joint before: what rides, and `led` of the np sums -/
@[reducible] def relIn : Rels Kc L.St Ex (M × Wp) := sendIn (L.A0 R0 msg) msg L.Idn

/-- the joint behind -/
@[reducible] def relOut : Rels Kc ((L.X2 × E) × L.tok.toSum.T.par.Out) Ex (M × Wp) :=
  L.tok.toSum.rrelOut (L.R2 R0) msg L.Psi

/-- The reduction. -/
def blk : IOR L.St Ex ((L.X2 × E) × L.tok.toSum.T.par.Out) Ex :=
  (send E (Fin L.np) E L.St Ex).seq (L.tok.blk (Ex := Ex))

/-- its errors -/
def eps : Err (L.blk (Ex := Ex)).shape :=
  Err.app (s := [sendRound E (Fin L.np) E]) ((L.np - 1, ()) : ℕ × Unit)
    (L.tok.toSum.reps (Ex := Ex) (F₀ L.tok.toSum.T.par))

theorem knowAt :
    KnowAt (L.blk (Ex := Ex)) (L.relIn R0 msg) (L.relOut R0 msg) (fun _ _ _ wp => wp)
      (L.eps (Ex := Ex)) := by
  have h1 : KnowAt (send E (Fin L.np) E L.St Ex) (L.relIn R0 msg)
      (sendOut (L.A0 R0 msg) msg fun x m => L.slots x m ∧ L.bsum x m) (fun _ _ _ wp => wp)
      ((L.np - 1, ()) : ℕ × Unit) :=
    send_knowAt (L.A0 R0 msg) msg L.Idn _ (L.np - 1) fun st m h s => L.few st m h s
  have h2 := L.tok.knowAt (Ex := Ex) (L.R2 R0) msg L.Psi
  have h3 : KnowAt (L.tok.blk (Ex := Ex))
      (sendOut (L.A0 R0 msg) msg fun x m => L.slots x m ∧ L.bsum x m) (L.relOut R0 msg)
      (fun _ _ _ wp => wp) (L.tok.toSum.reps (Ex := Ex) (F₀ L.tok.toSum.T.par)) :=
    knowAt_mono h2 (fun _ h => h)
      (fun a w _ h => ⟨h.1, (L.th_iff a.1 _).2 h.2⟩) (fun _ _ _ h => h) (fun _ h => h)
  exact knowAt_seq h1 h3

/-- Knowledge soundness, for each fixed tuple of messages. -/
theorem know (m : M) :
    (L.blk (Ex := Ex)).red.Know (L.relIn R0 msg).on (fun a wp => (L.relIn R0 msg).relR a (m, wp))
      (fun b wp => (L.relOut R0 msg).relR b (m, wp)) (fun _ _ wp => wp)
      (L.eps (Ex := Ex)) :=
  (L.knowAt R0 msg).know m

/-- The errors, round by round. -/
theorem errs : TWhole.errList (L.eps (Ex := Ex)) =
    (L.np - 1) :: 1 :: (List.replicate L.k 2 ++ [2, 0]) := by
  refine (errList_app _ _).trans ?_
  exact congrArg (fun l => (L.np - 1) :: l) (L.tok.errs (Ex := Ex))

end Block

end RowsL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.RowsL.th_iff
#print axioms Cb.Pv.Lay.RowsL.knowAt
#print axioms Cb.Pv.Lay.RowsL.errs
