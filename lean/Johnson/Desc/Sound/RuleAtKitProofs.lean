-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleAtKitProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleAtKit.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleAtKit
import Johnson.Desc.Sound.RuleOwnOkProofs
import Johnson.Desc.Sound.RuleKitMoreProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)

theorem kitView : KitView := by
  intro f ds
  induction ds with
  | nil =>
    intro _ r hr
    have hr' : r ∈ ([] : List Fmt.RoundView) := hr
    exact absurd hr' List.not_mem_nil
  | cons d ds ih =>
    rintro ⟨m, c, τ⟩ r hr
    have hr' : r ∈ (⟨_root_.Run.PQ.PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work) m.2),
        (_root_.Run.ckP f).dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)⟩ : Fmt.RoundView) ::
        rvSL (_root_.Run.ckP f) ds τ := hr
    rcases List.mem_cons.1 hr' with e | h
    · intro x hx
      rw [e] at hx
      exact kitBelow f d c x hx
    · exact ih τ r h

theorem okF_of_lt (a : UInt64) (h : a.toNat < Fmt.Fld.two.p) : OnBytes.okF a = true := by
  have e : OnBytes.pW.toNat = Fmt.Fld.two.p := by decide
  unfold OnBytes.okF
  exact decide_eq_true (UInt64.lt_iff_toNat_lt.2 (by rw [e]; exact h))

theorem kitViewOkE : KitViewOkE := by
  intro ds τ r hr x hx
  obtain ⟨h0, h1, h2⟩ := kitView .two ds τ r hr x hx
  show (OnBytes.okF x.1 && OnBytes.okF x.2.1 && OnBytes.okF x.2.2) = true
  rw [okF_of_lt _ h0, okF_of_lt _ h1, okF_of_lt _ h2]
  rfl

theorem ownOfRuleAtKit : OwnOfRuleAtKit := by
  intro S Cl W ι D fld F p on on' means In Out comp dec rule ceil hc hlog hb hpin hprom hlaw
  refine ownOfRuleOk S Cl W ι D (_root_.Run.ckP fld) F p on on' means In Out comp dec rule ceil
    (kitK (toRDs p.ds)) (kitFs fld (toRDs p.ds)) (DrawnBelow fld) hc ?_ hb hpin
    (fun a τ b _ _ => kitView fld _ τ) hprom hlaw
  intro j d hj
  have e1 : kitK (toRDs p.ds) j = nElems (Fmt.dsOf d.entry d.kind) := by
    unfold kitK
    rw [hj]
  have e2 : kitFs fld (toRDs p.ds) j = kitF fld d := by
    unfold kitFs
    rw [hj]
  rw [e1, e2]
  exact kitMeasure fld d (hlog d (List.mem_of_getElem? hj))

end VerifiableInference.Desc.Sound
