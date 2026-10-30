-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegWholeZk.lean: what zero knowledge asks of a segment with one group, with two groups
(Cb/Req1/LdSegWhole.lean: `segOne`, `segTwo`), beside its hypotheses, reduced to its body and one
fact.

Statements (Cb.Spec.ldSegWholeZk_*) and proofs.
Cb/Req1/LdReq.lean follows "which masks are fresh" through the lists of a segment (`s.Zk base`).
Behind the body, the only masked block of a closing is the split.

Main names:
  `Spec.ldSegWholeZk_one`: one group: s.Zk base follows from body.Zk base. The closing asks nothing,
    beside its hypotheses.
  `Spec.ldSegWholeZk_two`: for `Nonempty D.Pf`, `Nonempty F.Pf` (as `segTwo` needs): two groups:
    s.Zk base follows from body.Zk base and: the split's mask entry is fresh after the body
    (`D.spl.mask.fact` is among the facts body.After base). The batching and the step before the
    split do not look at it.

Limits: this file does not say which facts a segment hands on to the next one (`s.After base`: rules
in Cb/Req1/LdSegCarry.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegWhole
import Cb.Req1.LdSegCarry
import Cb.Req1.LdReqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

namespace Spec

def ldSegWholeZk_one : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl1 E Kc)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold) (base : MaskFact a.J.W → Prop),
    body.Zk base → (segOne D body hT l Q).Zk base

def ldSegWholeZk_two : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a : LdStage E Kc) (D : LdCl2 E Kc) (F : LdCl2b D)
      (body : LdProg a D.bat.src) (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l₁ : Link Kc D.fold₁.src.J D.fold₁.mid) (l₂ : Link Kc F.fold₂.src.J F.fold₂.mid)
      [Nonempty D.Pf] [Nonempty F.Pf] (t₁ t₂ : ℕ) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
      (cut₂ : N.Msg → F.Cf.N.Wit) (cut₁ : N.Msg → D.Cf.N.Wit) (bk₀ : N.Msg → Wp' → D.Wp)
      (L tN : N.O → ℕ)
      (Sn : N.Sender (F.fold₂.tgt.S.Wit × F.fold₂.tgt.Wp) (F.fold₂.tgt.S.Wit × Wp'))
      (base : MaskFact a.J.W → Prop),
    body.Zk base → body.After base D.spl.mask.fact →
    (segTwo D F body hT l₁ l₂ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn).Zk base

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- kinds that ask nothing, beside their hypotheses -/
theorem LdProg.zk_of_kinds {a b : LdStage E Kc} (p : LdProg a b) (q : LdTag → Prop)
    (hq : ∀ t, q t → t ≠ .sub ∧ t ≠ .split) (h : p.All q) (base : MaskFact a.J.W → Prop) :
    p.Zk base :=
  ldReq_zk_free E Kc a b p base (LdProg.all_mono q _ hq p h)

end

theorem ldSegWholeZk_one : Spec.ldSegWholeZk_one := by
  intro E Kc _ _ a D body hT l Q base hb
  refine ⟨hb, ?_, ?_, ?_⟩
  · refine (LdProg.zk_snoc _ _ _).2
      ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, trivial⟩, trivial⟩
  · exact LdProg.zk_of_kinds _ _
      (by
        rintro t (rfl | rfl) <;> exact ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩)
      (segOne D body hT l Q).foldT _
  · exact LdProg.zk_of_kinds _ _
      (by
        rintro t (rfl | rfl) <;> exact ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩)
      (segOne D body hT l Q).locT _

theorem ldSegWholeZk_two : Spec.ldSegWholeZk_two := by
  intro E Kc _ _ a D F body hT l₁ l₂ _ _ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn base hb hκ
  refine ⟨hb, ?_, ?_, ?_⟩
  · -- bat ; stepA ; split ; stepB
    have h1 : (LdMv.bat D.bat).After (body.After base) D.spl.mask.fact :=
      segCarry_bat D.bat _ D.spl.mask.fact hκ
    have h2 : D.stepA.After ((LdMv.bat D.bat).After (body.After base)) D.spl.mask.fact := by
      unfold LdCl2.stepA ldStepF
      exact segCarry_step D.bat.tgt D.spl.src _ _ _ _ _ D.spl.mask.fact _ D.spl.mask.fact.kc
        D.spl.mask.fact.put h1 (fun _ _ _ _ h => ⟨rfl, h⟩)
    refine (LdProg.zk_snoc _ _ _).2
      ⟨(LdProg.zk_snoc _ _ _).2
          ⟨(LdProg.zk_snoc _ _ _).2
              ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, trivial⟩, trivial⟩,
            ?_⟩,
        trivial⟩
    show (LdProg.After _ (body.After base)) D.spl.mask.fact
    rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
    exact h2
  · exact LdProg.zk_of_kinds _ _
      (by
        rintro t (rfl | rfl) <;> exact ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩)
      (segTwo D F body hT l₁ l₂ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn).foldT _
  · exact LdProg.zk_of_kinds _ _
      (by
        rintro t (rfl | rfl) <;> exact ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩)
      (segTwo D F body hT l₁ l₂ t₁ t₂ N Sd Wp' cut₂ cut₁ bk₀ L tN Sn).locT _

end Cb
