-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidersT.lean: THE PREMISES ON THE LETTERS OF A `Thread` T
(Honest/Thread/Thr.lean), AS ONE STRUCTURE, for the riders' debt (`RidesPast`,
Honest/Thread/Pays.lean) at the member at an attention segment's own rounds (kind K5), WITH T A
VARIABLE; and that the first chain's `Thread` at the library's own letters meets it where its letter
`keeps` at the border gives `K5Keeps`. It stands beside `K5AtT` (Honest/K5/Law/AtT.lean) and takes
the same letters.

  `StrsKept`          two values of the oracles' strings agree at the stored table's symbols and at
                      every tree below a number
  `strsKept_add`      no premise: the frame's strings behind rounds that were played agree so with
                      those in front, below the number of trees sent
  `K5RidersT`         THE STRUCTURE: four fields:
      riders   T.opened and T.row at the border: whatever is open there and is neither shut nor owed
               by the member's row is one of the table's items of the riding sorts ("no mark"; the
               five sorts of `riderB`, Johnson/Desc/First/Att/K05Riders.lean), and is not the
               digits' part of a segment's relation
      means    T.means at the riding sorts: the table's own sentence, as in `K5AtT`
      keeps    T.keeps at the border gives `K5Keeps`: with the converse, which the debt `Behind`
               takes (Kp), the two pin T.keeps at the border to `K5Keeps`
      strs     T.strs: behind rounds that were played the strings agree with those in front at the
               stored table and below the number of trees sent
  `k5RidersT_thrAt`   CONDITIONAL: the first chain's `Thread` at the library's own letters meets it,
                      where its letter `keeps` at the border gives `K5Keeps`

The field riders speaks of the list T.opened, which is made of T.start and of all of T's rows in
front of the border: it is one sentence on these letters, not an equation on each.

Limits. A definition: a premise's form; nothing is claimed of it. NO LAW ON THE RIDERS' DEBT STANDS
IN THIS FILE. The hypothesis `P5J.AtMgA` stands in the field means and is not shown here. At the
library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtT
import Johnson.Desc.ProofFile.Honest.K5.Law.RidersFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Strs Chain)
open ProofFile.Honest (Env Played srcAt)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Att.P (riderB)
open VerifiableInference.Desc.Sound (mgBase mgAll)
open H2K5.Honest (K5Keeps)
open ProofFile.Honest.FirstThread (Script WtF honest)
open P5J (AtMgA TS CellsM)

/-- **Two values of the oracles' strings agree at the stored table's symbols and at every tree below
the number n.** It is a definition. -/
def StrsKept (n : Nat) (y y' : Strs) : Prop := y'.cell = y.cell ∧ ∀ j, j < n → y'.col j = y.col j

/-- **The first chain's strings behind rounds that were played agree with those in front**, at the
stored table and below the number of trees sent. No premise: by the texts of `Env.add`
(Honest/Side.lean) and `Env.strs` (Honest/Thread/Thr.lean). -/
theorem strsKept_add (item n₁ n₂ : Nat) (E : Env) (ps : List Played) :
    StrsKept E.sent (Env.strs item (srcAt 0 n₁ n₂) E)
      (Env.strs item (srcAt 0 n₁ n₂) (E.add ps)) := by
  refine ⟨rfl, fun j hj => ?_⟩
  funext x
  show (match (srcAt 0 n₁ n₂ j).bind (E.add ps).tree with
    | some u => if x < 2 ^ u.2.logLength then u.2.col x else []
    | none => []) =
    (match (srcAt 0 n₁ n₂ j).bind E.tree with
    | some u => if x < 2 ^ u.2.logLength then u.2.col x else []
    | none => [])
  have e : (srcAt 0 n₁ n₂ j).bind (E.add ps).tree = (srcAt 0 n₁ n₂ j).bind E.tree := by
    unfold srcAt
    by_cases h1 : j < n₁
    · simp only [beq_self_eq_true, if_true, if_pos h1, Option.bind_some]
      show (if j < E.sent then E.tree (.own j) else _) = _
      rw [if_pos hj]
    · simp only [beq_self_eq_true, if_true, if_neg h1, Option.bind_none]
  rw [e]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **THE STRUCTURE FOR THE RIDERS: WHAT IS SPENT OF T's LETTERS AT THE KIND's MEMBER OF GROUP g.**
T: the `Thread`, a variable. The other letters: as in `K5AtT`. It is a definition: a premise's form.
Nothing is claimed of it. -/
structure K5RidersT
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (g : Nat) (it : Item → T.ι) (pb : T.P → ProofFile.InstPub) (wt : T.Wt → WtF)
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull) : Prop where
  /-- T.opened and T.row at the border: which items ride -/
  riders : ∀ j ∈ T.opened (borderOf g), j ∉ (T.row (borderOf g)).shuts →
    j ∉ (T.row (borderOf g)).owes →
    ∃ i, j = it i ∧ (i = .unmarked ∨ riderB (2 * g + 1) i = true) ∧
      ∀ n, i ≠ .constr n .lookDigits
  /-- T.means at the riding sorts: the table's own sentence, at the honest letters over the
  library's filling with the two fields laid -/
  means : ∀ i, (i = .unmarked ∨ riderB (2 * g + 1) i = true) → ∀ w a y v,
    T.means w (it i) a y v ↔
      Item.holds (P5J.At.N Zp cF)
        (honest (mgAll { h.𝔇 with decT := fun _ _ => some (cq w), cr1 := carryX } mgBase) ans test)
        i (pb a.1, a.2) y (wt v)
  /-- T.keeps at the border -/
  keeps : ∀ s s', T.keeps (borderOf g) s s' → K5Keeps s s'
  /-- T.strs: what rounds that were played leave of the strings -/
  strs : ∀ E ps, StrsKept E.sent (T.strs E) (T.strs (E.add ps))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE FIRST CHAIN's `Thread` AT THE LIBRARY's OWN LETTERS MEETS THE STRUCTURE**, at the three
maps the identity. CONDITIONAL: g is below 12; Kq: the letter `keeps` at the border gives
`K5Keeps`. -/
theorem k5RidersT_thrAt {g : Nat} (hg : g < 12)
    (Kq : ∀ s s', keeps (borderOf g) s s' → K5Keeps s s') :
    K5RidersT h (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) g
      (fun i => i) (fun p => p) (fun v => v) ans test carryX Q.cells :=
  { riders := fun j ho h1 h2 =>
      ⟨j, rfl,
        riders_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg j ho h1 h2,
        no_digits_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg j ho⟩
    means := fun _ _ _ _ _ _ => Iff.rfl
    keeps := Kq
    strs := fun E ps => strsKept_add item n₁ n₂ E ps }

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.strsKept_add
#print axioms ProofFile.Honest.K5.k5RidersT_thrAt
