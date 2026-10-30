-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/OrderAgrees.lean: A YARDSTICK BESIDE Johnson/Desc/First/K8/Order.lean: each
text there agrees, at every argument, with the test of the verifier on bytes after which it asks:
namedNow with ReqFrame.whereIs · fixed with HTailF2.arrayFixed · orderOk with
Johnson/Top/H0/L3/Frame.lean's orderGuard (that verifier's fixedBeforeTheMatrixF's condition) ·
close with HTailF2.closeFuns · front with L3.drawFront, but for the refusals' names.
NO RUNNING TEXT IMPORTS THIS FILE. Nothing on soundness is said.

-/
import Johnson.Desc.First.K8.Order
import Johnson.Top.H0.L3.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Order
open OnBytes OnBytes.Model

theorem namedNow_eq (f : ReqFrame) (w : Lies) : namedNow f w = f.whereIs w.born w.message := by
  unfold namedNow ReqFrame.whereIs
  cases hn : f.next <;> simp
  by_cases hb : w.born = f.link
  · simp [hb]
  · simp only [hb, if_false]
    split <;> rename_i h <;> simp [h]

theorem fixed_eq (L : LinkCtx) (S : Statement) (t : Nat) :
    fixed L S t = HTailF2.arrayFixed L S t := by
  unfold fixed liesAt HTailF2.arrayFixed sentInFront answered
  simp only [namedNow_eq]
  cases h1 : L.arrayOf[t]? with
  | none => simp
  | some bn =>
    obtain ⟨born, name⟩ := bn
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    cases h2 : (L.check.rows.layout.link.getD born []).find? fun A => A.name == name with
    | none => simp
    | some a =>
      simp only [Option.bind_some]
      cases h3 : L.check.frame.shape.link[born]? with
      | none => simp
      | some l =>
        simp only [Option.bind_some]
        cases h4 : l.messages[a.message]? with
        | none => simp
        | some m =>
          simp only [Option.bind_some]
          cases h5 : L.check.frame.whereIs born a.message with
          | none => simp
          | some o =>
            cases h6 : S.oracles[o]? with
            | none => simp [h6]
            | some x =>
              by_cases hb : born = L.link
              · subst hb; simp [h6]
              · by_cases hl : born < L.link
                · have : born ≤ L.link := Nat.le_of_lt hl
                  simp [hb, hl, this, h6]
                · have : ¬ born ≤ L.link := fun h => hl (Nat.lt_of_le_of_ne h hb)
                  simp [hb, hl, this, h6]

theorem orderOk_eq (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    orderOk tl L S = L3.orderGuard tl L S := by
  have hf : fixed L S = HTailF2.arrayFixed L S := funext (fixed_eq L S)
  unfold orderOk L3.orderGuard
  rw [hf]
  congr 1
  congr 1
  funext n
  cases tl.ix.U.getD n none <;> simp

theorem close_eq (tl : HTailF2) (funs : Array HFun) :
    (close tl funs).toOption = tl.closeFuns funs := by
  unfold close HTailF2.closeFuns
  by_cases h : tl.funClosed <;> simp [h, Except.toOption]

theorem front_ok_iff (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    (front tl L S).isOk = (L3.drawFront tl L S).isOk := by
  unfold front L3.drawFront
  rw [orderOk_eq]
  by_cases h1 : tl.funClosed <;> by_cases h2 : tl.shp.size = tl.NM <;>
    by_cases h3 : L3.orderGuard tl L S <;> simp [h1, h2, h3, Except.isOk, Except.toBool]

end VerifiableInference.Desc.First.K8.Order
