-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TreesLaws.lean: laws of the typed rounds in which one message may send the roots of
several trees (OnBytes/Maker/Trees.lean): what a proof that a verifier over such rounds is local
(`IOR.IsLocal`, Ior/Ior.lean) takes from them. After Run/PlanQSLaws.lean's `rhoS_eq`, `rvS_congr`
and `colAtS_congr`: the first three are OnBytes/TypedOracleCompiler/Run/PlanQSLaws.lean's `rhoS_eq`, `rvS_congr`,
`colAtS_congr` at `toRDs ds`, proved again here.

  `rhoT_eq`         the verifier's messages that `rhoT` reads off a transcript are the transcript's
  `rvT_congr`       the rounds of a view are the same at two transcripts with the same verifier's
                    messages and the same plain parts
  `colAtST_read`    the column at (tree, leaf) is the transcript's answer at the position there
  `colAtST_congr`   so it is the same at two transcripts that answer alike at that one position
  `colAtST_none`    there is a column exactly where there is a position
  `finPosT`, `pointT`, `pointsT`, `pointsOfT`
                    the positions of a round are finitely many, and every round's oracle is a string
                    (`Shape.IsPoint`, Iop/Shape.lean)

Not claimed. Nothing on soundness, and nothing on an honest prover.


-/
import OnBytes.Maker.Trees
import OnBytes.Maker.TerminalLaws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

theorem rhoT_eq (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)), rhoT C ds τ = τ.rho
  | [], _ => rfl
  | _ :: ds, (_, c, τ) => congrArg (Prod.mk c) (rhoT_eq C ds τ)

theorem rvT_congr (C : CK) :
    ∀ (ds : List RDT) (τ τ' : Iop.Tr (uLT C ds)),
      τ.rho = τ'.rho → τ.plains = τ'.plains → rvT C ds τ = rvT C ds τ'
  | [], _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), hρ, hp => by
      have e1 : c = c' := congrArg Prod.fst hρ
      have e2 : τ.rho = τ'.rho := congrArg Prod.snd hρ
      have e3 : m.2 = m'.2 := congrArg Prod.fst hp
      have e4 : τ.plains = τ'.plains := congrArg Prod.snd hp
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: rvT C ds τ =
        ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m'.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c')⟩ :: rvT C ds τ'
      rw [e1, e3, rvT_congr C ds τ τ' e2 e4]

/-- A column hangs on the transcript only at its one position. -/
theorem colAtST_congr (C : CK) :
    ∀ (ds : List RDT) (τ τ' : Iop.Tr (uLT C ds)) (n x : ℕ),
      (∀ p, posAtST C ds n x = some p → τ.read p = τ'.read p) →
      colAtST C ds τ n x = colAtST C ds τ' n x
  | [], _, _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), n, x, h => by
      rw [colAtST_cons, colAtST_cons]
      simp only [posAtST_cons] at h
      by_cases hn : n < d.trees.length
      · rw [if_pos hn, if_pos hn]
        rw [if_pos hn] at h
        cases hq : posAtT d.trees n x with
        | none => rfl
        | some p =>
          have e : m.1 p = m'.1 p := h (.inl p) (by rw [hq]; rfl)
          show some (colT d.trees p (m.1 p)) = some (colT d.trees p (m'.1 p))
          rw [e]
      · rw [if_neg hn, if_neg hn]
        rw [if_neg hn] at h
        refine colAtST_congr C ds τ τ' (n - d.trees.length) x fun p hp => ?_
        exact h (.inr p) (by rw [hp]; rfl)

/-- The symbol at a position of the rounds behind the round in front, as a list of words. -/
def colOfSym (C : CK) : (ds : List RDT) → (p : OPos (uLT C ds)) → OSym (uLT C ds) p → List UInt64
  | d :: _, .inl p, c => colT d.trees p c
  | _ :: ds, .inr q, c => colOfSym C ds q c

/-- **The column at (tree, leaf) is the transcript's answer at the position there.** -/
theorem colAtST_read (C : CK) :
    ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)) (n x : ℕ),
      colAtST C ds τ n x = (posAtST C ds n x).map fun p => colOfSym C ds p (τ.read p)
  | [], _, _, _ => rfl
  | d :: ds, (m, c, τ), n, x => by
      rw [colAtST_cons, posAtST_cons]
      by_cases hn : n < d.trees.length
      · rw [if_pos hn, if_pos hn, Option.map_map]
        rfl
      · rw [if_neg hn, if_neg hn, Option.map_map, colAtST_read C ds τ (n - d.trees.length) x]
        rfl

/-- There is a column exactly where there is a position. -/
theorem colAtST_none (C : CK) (ds : List RDT) (τ : Iop.Tr (uLT C ds)) (n x : ℕ) :
    colAtST C ds τ n x = none ↔ posAtST C ds n x = none := by
  rw [colAtST_read, Option.map_eq_none_iff]

/-- The positions of a round with several trees are finitely many. -/
abbrev finPosT : (ts : List Fmt.Shape) → Fintype (PosT ts) := TypedOracleCompiler.Run.PQ.finPosT

/-- The oracle of a round with several trees is a string. -/
def pointT (C : CK) (d : RDT) : (roundT C d).up.IsPoint :=
  ⟨finPosT d.trees, decPosT d.trees, fun f => f, fun _ _ => rfl, fun _ => rfl, zeroT d.trees⟩

def pointsT (C : CK) : (ds : List RDT) → (uLT C ds).IsPoint
  | [] => ()
  | d :: ds => (pointT C d, pointsT C ds)

/-- Every round's oracle is a string, the round in front among them. -/
def pointsOfT (C : CK) (ds : List RDT) : (Twin.up (SOfT C ds)).IsPoint :=
  (pointFront C, pointsT C ds)

end OnBytes.Maker
