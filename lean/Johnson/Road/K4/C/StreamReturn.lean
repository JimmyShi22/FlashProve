-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StreamReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4): three more of the verifier's readers
(OnBytes/Model/LayerForms.lean) return where the entries that they name are there: the residual
stream after a write (SxsA), the loop of the segment DD, and a sum of forms. One definition of a
hypothesis; statements and proofs. General in the sizes.

  `Strm v sg`     the table of the stream after write number sg is found, and its blocks are there.
  `SxsA_some`     the stream's sum returns.
  `foldDD_some`   the loop of the segment DD returns.
  `sumForms_some`      a sum of forms returns where each member does.

Not shown here. That the hypotheses hold at any plan: no example is shown here. Public data alone:
whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.ReadersReturn
import Johnson.Road.FormsKeysA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env sumForms aff0)
open OnBytes.Desc.First.K4.Total (sumForms_all)

variable {v : Env}

/-- **The table of the residual stream after write number sg is found, and its blocks are there.**
This defines a hypothesis; the definition claims nothing. -/
def Strm (v : Env) (sg : ℕ) : Prop :=
  ∃ tb txs,
    v.tabAt ((if sg == 0 then "xbI" else if sg == v.y.NW * v.y.Lam then "xbO" else "af") ++ "@" ++
      "Z") = some tb ∧ v.y.T_ "xs" = some txs ∧
    ∀ xh, xh < v.y.h.d / v.y.S2 →
      (if (sg == 0 || sg == v.y.NW * v.y.Lam) = true then v.xbA tb xh
        else v.longA tb txs (sg - 1) xh).isSome = true

/-- The stream's sum returns. -/
theorem SxsA_some {sg : ℕ} (S : Strm v sg) (wh : Array E) : (v.SxsA wh "Z" sg).isSome = true := by
  obtain ⟨tb, txs, e1, e2, H⟩ := S
  unfold Env.SxsA
  dsimp only
  rw [e1, e2]
  show (sumForms (v.y.h.d / v.y.S2) fun xh =>
    (if (sg == 0 || sg == v.y.NW * v.y.Lam) = true then v.xbA tb xh
      else v.longA tb txs (sg - 1) xh).map fun a => (a, wh.getD xh zeroE)).isSome = true
  rw [sumForms_all, List.all_eq_true]
  intro xh hx
  rw [Option.isSome_map]
  exact H xh (List.mem_range.mp hx)

/-- A sum of forms returns where each member does. -/
theorem sumForms_some {n : ℕ} {f : ℕ → Option (Aff × E)} (h : ∀ x, x < n → (f x).isSome = true) :
    (sumForms n f).isSome = true := by
  rw [sumForms_all, List.all_eq_true]
  exact fun x hx => h x (List.mem_range.mp hx)

/-- The loop of the segment DD returns. -/
theorem foldDD_some {lamM n : ℕ} (ew : Array E) (h1 : Short v "lr" "zt" lamM n)
    (h2 : Short v "sel" "zt" lamM n) : ∀ (l : List ℕ), (∀ x ∈ l, x < n) → ∀ s : Aff × Aff,
    (l.foldlM (stepDD v lamM ew) s).isSome = true
  | [], _, _ => rfl
  | x :: l, hl, s => by
    obtain ⟨a, ha⟩ := some_of (shA_some h1 (hl x List.mem_cons_self))
    obtain ⟨b, hb⟩ := some_of (shA_some h2 (hl x List.mem_cons_self))
    have e : stepDD v lamM ew s x =
        some (s.1.addMul (a + s.2) (negE (ew.getD x zeroE)), s.2 + b) := by
      unfold stepDD
      rw [ha, hb]
      rfl
    rw [List.foldlM_cons, e]
    exact foldDD_some ew h1 h2 l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.SxsA_some
#print axioms OnBytes.Road.K4.C.sumForms_some
#print axioms OnBytes.Road.K4.C.foldDD_some
