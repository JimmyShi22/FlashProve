-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/AsmKV0.lean.
The assembled lookup at the named short sumcheck.

States: asmK_know0: knowledge soundness of the lookup over TWhole.V₀, TWhole.V₀C (Cb/G6/Pick.lean:
in each round the constant coefficient is left out), under the premises of asmK_know
(Cb/Pv/Lookup/Know/AsmKV.lean);
  asmK_eq0: at each of the lookup's own sumchecks every variable's weights sum to 1 (TWhole.Eq0):
    the condition under which that short sumcheck's verifier rejects nothing and its value is
    computed by TWhole.shortV, shortVC (F₀_ok, Cb/G6/Pick.lean; short_red_out, short_red_outC,
    Cb/G6/Value.lean).
  eqs_mon0, mix_mon0, tieF_eq0, treeP_eq0: the same for lists of equality variables, for the tie's
    steps and for a tree's levels.
Limits: that the whole lookup's verifier rejects nothing is not stated here.

-/
import Cb.Pv.Lookup.Know.AsmKV
import Cb.G6.Pick

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Finset

section
variable (E : Type) [Field E] [Fintype E]

theorem eqs_mon0 (n : ℕ) : ∀ (k : ℕ) (z : Fin k → E),
    ∀ v ∈ pVars (List.replicate k (pfCube E n)) (pdEqs E n k z), v.mon 0 = 1
  | 0, _ => fun _ hv => absurd hv List.not_mem_nil
  | k + 1, z => eq0_cons (pfCube E n) (pdEq E n (z 0)) _ _ (mon0_eq n (z 0))
      (eqs_mon0 n k fun i => z i.succ)

theorem mix_mon0 : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    ∀ v ∈ pVars (pfMix E k dg) (pdMix E k dg z), v.mon 0 = 1
  | 0, _, _ => fun _ hv => absurd hv List.not_mem_nil
  | k + 1, dg, z => eq0_cons (pfCube E (dg 0)) (pdEq E (dg 0) (z 0)) _ _ (mon0_eq (dg 0) (z 0))
      (mix_mon0 k (fun i => dg i.succ) fun i => z i.succ)

theorem tieF_eq0 (D : TieF E) (l : ℕ) : Eq0 (D.lv l).T.par := by
  cases l <;> exact our_eq0 _ fun _ _ hv => absurd hv List.not_mem_nil

theorem treeP_eq0 (D : TreeP E) (l : ℕ) : Eq0 (D.lv l).T.par := by
  cases l with
  | zero => exact our_eq0 _ fun _ => eqs_mon0 E 2 (D.g + 0) _
  | succ l => exact our_eq0 _ fun _ => eqs_mon0 E 2 (D.g + l + 1) _

/-- Eq0 at each of the lookup's own sumchecks. -/
theorem asmK_eq0 (A : LkAsmH E) :
    (∀ l, Eq0 (A.H.tie.lv l).T.par) ∧ (∀ l, Eq0 ((A.IK.setV (A.v' + 1)).DK.lv l).T.par) ∧
    (∀ l, Eq0 (A.D.lv l).T.par) ∧ Eq0 A.En.par ∧ Eq0 A.Bt.zc.next.par :=
  ⟨tieF_eq0 E A.H.tie, treeP_eq0 E _, treeP_eq0 E A.D,
    fun _ => mix_mon0 E _ _ _, our_eq0 _ fun _ => eqs_mon0 E 2 _ _⟩

/-- `asmK_know` at V₀, V₀C. -/
theorem asmK_know0 (p : ℕ) [CharP E p] (A : LkAsmH E) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w)
    (m : M) :
    (A.baseK V₀ V₀C).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ A.lk.inR a.1 (msg m))
      (fun b wp => R0.relR (b.1.1, b.2) (m, wp) ∧ A.lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (A.baseK V₀ V₀C).e :=
  asmK_know E p A V₀ V₀C Ex Kc M Wp R0 msg hA hP hF m

end
end Cb
