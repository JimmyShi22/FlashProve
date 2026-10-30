-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpRest.lean: at the plan of this protocol's technical report (lean/CREDITS.md; one
splitting; three tests):
under the hypotheses named below, "restG is rest" and the three clauses on "the rest" fall to
conditions on places.

A definition (`LdLinPp.restOf`), statements and proofs. Generic.
The plan: `LdLinPp` (Cb/Ld/LdLinClosePlanP.lean). "restG is rest" is the equation
`p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)`, for all sa and m, which
`Spec.ldLinPp_says` there assumes. "The rest" is what closes the rows that the preamble left, after
the three tests (here `LdRowsQ`, Cb/Ld/LdLinClosePlanRows.lean). A place is an entry of an oracle
message (`Sig.Ent`, Cb/Ld/LdBatSig.lean).
At this plan the mask part "rest" of the evaluation's row is read on the instance's group `p.Gc`, a
group of what is left after the two shared tests; the rows that the preamble left go to what is
left after the third test.

Main names:
  `Spec.ldRestP_val`: if slA is non-zero only in oracle messages that are kept at both shared
    bridges (`p.kp₁`, `p.kp₂`) and lie in `p.Gc`, `p.restOf slA` has slA's value on `p.Gc`'s
    message.
  `Spec.ldRestP_is`: under the same condition, for a plan whose `restG` is `p.restOf slA` and a test
    whose "rest" is slA's value, restG is rest.
  `Spec.ldOWfRestP_is`: the same at `W.O.toC` (the test over what weights-formedness leaves), for
    `p.restG = p.restOf (W.restF nAt)`, from `W.P.EntAt nAt` (Cb/Ld/LdWfMasksBatt.lean) and two
    conditions on places: the oracle messages of the places that `Spec.ldOWfRest_read`
    (Cb/Obj/LdObjectWfRest.lean) names are kept at both shared bridges and lie in `p.Gc`.
  `Spec.ldOWfRowsP_three`: the three clauses of "the rest" (`Spec.ldRowsOneP_three`,
    Cb/Ld/LdLinClosePlanOneP.lean; says Ab, `p.SaysA`; in order, `LdTc.OK`; its demand, `LdTc.q`)
    for one test X on all that is left after the third test, from `Nonempty (Fin W.Cf.C₀.n)`,
    `EntAt`, "X takes all rows, keeps nothing", a condition on places (the filed rows' entries
    (`W.RB`, Cb/Obj/LdObjectWfRows.lean) lie in messages kept at all three bridges, `p.kp₃` too),
    `X.run.OK`.

Limits: `X.run.OK` is asked. No instance here.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectWfRestProofs
import Cb.Ld.LdLinClosePlanOnePProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- a form on the entries of what the preamble left, read on the message of the instance's group -/
def LdLinPp.restOf {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y}
    (p : LdLinPp C) (slA : Slf E C.Sta C.Sa.Ent) : Slf E C.Sta p.Gc.C.J :=
  (((C.upA slA).onSub p.kp₁).onSub p.kp₂).onG p.Gc

namespace Spec

def ldRestP_val : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y)
      (p : LdLinPp C) (slA : Slf E C.Sta C.Sa.Ent),
    (∀ st (a : C.Sa.O) j, slA st ⟨a, j⟩ ≠ 0 →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl a)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩) →
    ∀ sa (m : C.S.Msg),
      (p.restOf slA).val sa (p.Gc.msg (p.left₂ m)) = slA.val sa (C.Sa.ents (C.aM m))

def ldRestP_is : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y)
      (p : LdLinPp C) (slA : Slf E C.Sta C.Sa.Ent),
    p.restG = p.restOf slA → (∀ sa ma, C.rest sa ma = slA.val sa (C.Sa.ents ma)) →
    (∀ st (a : C.Sa.O) j, slA st ⟨a, j⟩ ≠ 0 →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl a)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩) →
    ∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOWfRestP_is : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (p : LdLinPp W.O.toC), W.P.EntAt nAt →
    p.restG = p.restOf (W.restF nAt) →
    (∀ i, ∃ (h₁ : p.kp₁
            (.inl
              (.inl (.inl (nAt (W.P.wAt (pIx W.P.bt.fmt (pdPlains E W.P.bt.n W.P.bt.k) i))).1))))
          (h₂ : p.kp₂ ⟨_, h₁⟩),
        p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩) →
    (∀ (q : Fin (W.P.n + 1)) n, W.P.gC q n →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl (nAt n).1)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩) →
    ∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = W.O.toC.rest sa (W.O.toC.aM m)

def ldOWfRowsP_three : Prop :=
  ∀ (W : LdOWf F E) [Nonempty (Fin W.Cf.C₀.n)] (nAt : W.P.N → W.P.S.Ent) (p : LdLinPp W.O.toC)
      (X : LdRowsD p.S₃ W.O.toC.E₀ W.O.toC.Wpa (p.rowsL (W.rowsA nAt)))
      (w₀ : (p.S₃.sub X.kp).Wit × W.O.toC.Wpa),
    W.P.EntAt nAt → (∀ b, X.now b) → (∀ o, ¬ X.kp o) →
    (∀ (r : W.RB) n, W.P.gR r.1.1 r.2 n →
      ∃ (h₁ : p.kp₁ (.inl (.inl (.inl (nAt n).1)))) (h₂ : p.kp₂ ⟨_, h₁⟩), p.kp₃ ⟨⟨_, h₁⟩, h₂⟩) →
    X.run.OK →
    p.SaysA (X.one W.tgA w₀).Q.base (X.one W.tgA w₀).fx ∧
    (X.one W.tgA w₀).Q.OK ∧
    ∀ V,
      (X.one W.tgA w₀).Q.q V → p.S₃.qFam (fun U : Finset W.O.toC.E₀.Pos => U = ∅) (fun _ => X.t) V

end
end Spec

theorem ldRestP_val : Spec.ldRestP_val := by
  intro E ι κ J Y _ C p slA hs sa m
  have s1 : ∀ (n : C.S.Ent), ¬ p.kp₁ n.1 → C.upA slA sa n = 0 := by
    rintro ⟨((a | a) | a) | a, j⟩ hn
    · by_contra hne
      exact hn (hs sa a j hne).1
    · rfl
    · rfl
    · rfl
  have s2 : ∀ (n : p.S₁.Ent), ¬ p.kp₂ n.1 → ((C.upA slA).onSub p.kp₁) sa n = 0 := by
    rintro ⟨⟨((a | a) | a) | a, h⟩, j⟩ hn
    · by_contra hne
      exact hn (hs sa a j hne).2.1
    · rfl
    · rfl
    · rfl
  have s3 : ∀ (n : p.S₂.Ent),
      ¬ p.Gc.mem n.1 → (((C.upA slA).onSub p.kp₁).onSub p.kp₂) sa n = 0 := by
    rintro ⟨⟨⟨((a | a) | a) | a, h⟩, h'⟩, j⟩ hn
    · by_contra hne
      exact hn (hs sa a j hne).2.2
    · rfl
    · rfl
    · rfl
  exact (ldPeel_onG E p.S₂ p.Gc C.Sta (((C.upA slA).onSub p.kp₁).onSub p.kp₂)
      sa (p.left₂ m) s3).trans
    ((ldPeel_onSub E p.S₁ p.kp₂ C.Sta ((C.upA slA).onSub p.kp₁) sa
        (C.S.res (T := OMsg.Msg) p.kp₁ m) s2).trans
      ((ldPeel_onSub E C.S p.kp₁ C.Sta (C.upA slA) sa m s1).trans (C.upA_val slA sa m)))

theorem ldRestP_is : Spec.ldRestP_is := by
  intro E ι κ J Y _ C p slA hG hr hs sa m
  rw [hG, hr]
  exact ldRestP_val E ι κ J Y C p slA hs sa m

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOWfRestP_is : Spec.ldOWfRestP_is F E := by
  intro W nAt p hE hG hp1 hp2
  refine ldRestP_is E _ _ _ _ W.O.toC p (W.restF nAt) hG
    (fun sa ma => (ldOWfRest_val F E W nAt hE sa ma).symm) fun st a j hne => ?_
  rcases ldOWfRest_read F E W nAt st ⟨a, j⟩ hne with ⟨i, hi⟩ | ⟨q, n, hg, hn⟩
  · have ha := congrArg Sigma.fst hi
    have h := hp1 i
    rw [ha] at h
    exact h
  · have ha : (nAt n).1 = a := congrArg Sigma.fst hn
    subst ha
    exact hp2 q n hg

theorem ldOWfRowsP_three : Spec.ldOWfRowsP_three F E := by
  intro W _ nAt p X w₀ hE hn hk hpl hX
  obtain ⟨h1, h2⟩ := ldOWfRows_ab F E W nAt hE
  refine ldRowsOneP_three E _ _ _ _ W.O.toC p W.RB (W.rowsA nAt) W.tgA X w₀ (fun U => U = ∅)
    hn hk h1 h2 (fun r st a j hne => ?_) hX rfl
  obtain ⟨n, hg, hat⟩ := ldOWfRows_read F E W nAt r st ⟨a, j⟩ hne
  have ha : (nAt n).1 = a := congrArg Sigma.fst hat
  subst ha
  exact hpl r n hg

end
end Cb
