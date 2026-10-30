-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BearsOwn.lean: THE PREMISE `bears` OF `AtPlace` | `AtPlaceOwn` HAS A MEMBER:
THE CHAIN's OWN COUNTS. Definitions, statements and proofs, on lists of numbers.

The errors εt of the piece's rounds behind "BAT" are a free letter of the law; `bears` asks that
they bear the chain's own counts, round by round. So one may take just these:

  `errOfList`: a list of numbers as a list of errors over a shape; `errList_errOfList`: and back,
    where the two are as long.
  `errList_length`: a list of errors is as long as its shape.
  `bears_own`: where the place's stages, written rounds and letters give the chain c₀, and c₀ has as
    many rounds as the stretch behind "BAT": εt := the chain's own counts meets `bears`.
What it buys: the law then stands AT THE CHAIN's OWN COUNTS; whether these are small is a question
on numbers alone.
Limits: nothing on soundness. That the counts are small is not shown. "As many rounds" is a premise.
A tool.
-/
import Johnson.Desc.K12.Coin.Sheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice OnBytes.Maker
open Iop _root_.Run
open H2K.Pub (sgOf writtenOf WR chainFrom)

/-- A list of numbers as a list of errors over a shape; 0 where the list ends. -/
def errOfList : (s : Shape) → List ℕ → Err s
  | [], _ => ()
  | _ :: s, l => (l.headD 0, errOfList s l.tail)

theorem errList_errOfList : ∀ (s : Shape) (l : List ℕ), l.length = s.length →
    errList s (errOfList s l) = l
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: s, n :: l, h => by
    show n :: errList s (errOfList s l) = n :: l
    rw [errList_errOfList s l (Nat.succ.inj h)]

theorem errList_length : ∀ (s : Shape) (ε : Err s), (errList s ε).length = s.length
  | [], _ => rfl
  | _ :: s, (_, ε) => by
    show (errList s ε).length + 1 = s.length + 1
    rw [errList_length s ε]

theorem forall₂_le_refl : ∀ l : List ℕ, List.Forall₂ (· ≤ ·) l l
  | [] => .nil
  | n :: l => .cons (Nat.le_refl n) (forall₂_le_refl l)

/-- **The chain's own counts meet `bears`.** -/
theorem bears_own (π : P12) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (dt : List RDT)
    (a₀ : Fmt.M1.Stage) (rest₀ : List Fmt.M1.Stage) (w₀ : WR) (l₀ : List WR)
    (c₀ : OnBytes.Slice.Chain (sgOf a₀)) (hs : π.nums.stages = a₀ :: rest₀)
    (hw : writtenOf π.nums = some (w₀ :: l₀))
    (hc : chainFrom (.at L mC mS mW rad) rest₀ a₀ l₀ = some c₀)
    (hlen : (PQ.uL (ckP .two) c₀.rds).length = (uLT (ckP .two) dt).length) :
    ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL (errOfList (uLT (ckP .two) dt) (errList _ c₀.errL)) := by
  intro a rest w0 l c hs' hw' hc'
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (hw.symm.trans hw'))
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  unfold Bears
  rw [errList_errOfList _ _ ((errList_length _ _).trans hlen)]
  exact forall₂_le_refl _

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.errList_errOfList
#print axioms VerifiableInference.Desc.K12.Coin.bears_own
