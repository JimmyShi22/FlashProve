-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/First.lean: THE TWO PREMISES OF `follows_of_yes` (Follows.lean), PAID AT THE
SHEET's LETTERS. Statements and proofs.

  `first_cols`: the first switch's openings: by `FirstOpens`' two clauses and the clauses opens.a
    and opens.W of the kind's test on the record, the column of the tree that opening number i names
    is the written column of `W0` at the book's place D.ts[i]. After `first_fits`
    (Johnson/Desc/K12/Law/ViewWide.lean).
  `own_cols`: the later openings: by `numOwn`, `own0`, `batNone` and `Chain.Trees`, the tree of own
    number free + k is the stretch's k-th, and that is the chain's k-th switch's.
A tool.
-/
import Johnson.Desc.K12.Coin.Follows
import Johnson.Desc.K12.Coin.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK H2K.Sw
open H2K.First (gpOf gpL Plain logAt widthAt made_of opensOf_cut opens_a_of_ok opens_W_of_ok ownN)

theorem first_cols (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ)
    (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)) (t : T12) (a : Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hD : gpOf π t a L = some D)
    (hok : H2K.First.ok (gpL π a row D) = true)
    (h1 : D.opens.map (fun o => num o.2) = D.ts.map no) (h2 : ∀ z ∈ D.ts, no z < base) (i : ℕ)
    (o : ToldO) (x : ℕ) (col : List UInt64)
    (ho : ((cutS (laidS π) a.k).flatMap (·.opens))[i]? = some o)
    (hP : PCol (ckP .two) ⟨F.a, base, F.all, ds, F.key, F.all⟩ y τ num o x col) :
    col = colW (W0 F no D.book y (D.ts.getD i 0)).1 (W0 F no D.book y (D.ts.getD i 0)).2 x := by
  have ho' : D.opens[i]? = some o := by
    rw [(made_of π t a L D hD).opens, ← opensOf_cut]
    exact ho
  have ha := congrArg (·[i]?) (opens_a_of_ok π a row D hok)
  have hWd := congrArg (·[i]?) (opens_W_of_ok π a row D hok)
  have hn := congrArg (·[i]?) h1
  simp only [List.getElem?_map, ho', Option.map_some] at ha hWd hn
  cases hz : D.ts[i]? with
  | none =>
    rw [hz] at ha
    cases ha
  | some z =>
    rw [hz] at ha hWd hn
    have e1 : o.1.a = logAt D.book z := Option.some.inj ha
    have e2 : o.1.W = widthAt D.book z := Option.some.inj hWd
    have e3 : num o.2 = no z := Option.some.inj hn
    have hget : D.ts.getD i 0 = z := by rw [List.getD_eq_getElem?_getD, hz]; rfl
    obtain ⟨p1, p2, p3⟩ := hP
    rw [hget]
    refine (colW_woIn F y (no z) _ _ x col (by rw [← e1]; exact p3) ?_
      (by rw [← e2]; exact p2)).symm
    rw [e3] at p1
    have p1' : (if no z < base then (posL F.all (no z) x).map y.2
        else colAtST (ckP .two) ds τ (no z - base) x) = some col := p1
    rw [if_pos (h2 z (List.mem_of_getElem? hz))] at p1'
    unfold colIn
    rw [p1']
    rfl

theorem own_cols (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT)
    (lo : List (PQ.RD × List ℕ)) (y : F.E.Str) (m : (roundT (ckP .two) dB).up.Msg)
    (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) {s : Sg}
    (ch : OnBytes.Slice.Chain s) (hR : ch.rds = lo.map (·.1)) (hT : ch.Trees)
    (hown : ownN π = 0) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hbn : dB.trees = []) :
    OwnCols (PCol (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ y (m, c, τ) num)
      (π.nums.free + (ownN π + 0)) ch (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) := by
  refine ownCols_of _ ch hT _ _ fun k o ho x col hP => ?_
  obtain ⟨p1, _, _⟩ := hP
  rw [ho, hown, Nat.add_zero, hnum k] at p1
  have p1' : (if base + k < base then (posL F.all (base + k) x).map y.2
      else colAtST (ckP .two) (dB :: lo.map mk) (m, c, τ) (base + k - base) x) = some col := p1
  have hl : dB.trees.length = 0 := by rw [hbn]; rfl
  rw [if_neg (by omega), Nat.add_sub_cancel_left, colAtST_cons,
    if_neg (by rw [hl]; exact Nat.not_lt_zero k), hl, Nat.sub_zero] at p1'
  have p2 : colAtST (ckP .two) (lo.map mk) τ k x = some col := p1'
  rw [trL_blOf, colAtS_cast, ← colAtST_trW]
  exact p2

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.first_cols
#print axioms VerifiableInference.Desc.K12.Coin.own_cols
