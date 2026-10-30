-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseShort.lean: the join point, the closing, the zero point and the test of the
bits at the short sumcheck `SK₀` (Cb/Pv/KeyLookup/Short0.lean), in which the coefficient of power 0
of each round's polynomial is not sent.

It imports CloseLam.lean, CloseForm.lean, CloseSupp.lean and Short0.lean; no file of the port.
Each statement is that of its twin at the library's verifier, with `SK₀` for `PscLtK.lib`.

  `close_short`, `bits_short`   `SK₀` meets the condition on the letter.
  `four_know_short`   all four blocks are `Know` between their joints, if pl ≤ 2^mu.
  `close_form_short`, `bits_form_short`   state handed on, oracles only copied.
  `close_supp_short`, `bits_supp_short`   under `P.In G`: forms stay 0 outside G.
  `clo_lam_short`, `bits_lam_short`   errors and numbers of values are the list's columns c and n.

-/
import Cb.Pv.KeyLookup.CloseLam
import Cb.Pv.KeyLookup.CloseForm
import Cb.Pv.KeyLookup.CloseSupp
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (Ex : ExtSpec)

theorem close_short (Kc M Wp : Type) (msg : M → Option A.J → E) :
    (SK₀ E Ex).CoreK M Wp Kc (A.En P).par msg :=
  SK₀_coreK M Wp Kc (A.En P).par msg (endM_vars E (A.En P)).1 (endM_deg E (A.En P) (A.en_ok P))
    (endM_vars E (A.En P)).2

theorem bits_short (Kc M Wp : Type) (msg : M → Option A.J → E) :
    (SK₀ E Ex).FullK M Wp Kc (A.BT P).par msg :=
  SK₀_ourK M Wp Kc (A.BT P) msg (ldZeroP_vars E (A.Bt P).zc).1 (ldLkpBitP_degX E (A.Bt P))
    (ldLkpBitP_degY E (A.Bt P)) (ldZeroP_vars E (A.Bt P).zc).2

/-- All four at the short sumcheck. -/
theorem four_know_short (hr : A.pl ≤ 2 ^ A.mu) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    (A.joinK Ex).Know (A.jt R0 msg Mu A.Roots) (A.jt R0 msg Mu A.Joined) ∧
    (A.closeK P (SK₀ E Ex)).Know (A.jt R0 msg Mu fun x μ => A.Table x μ A.d)
      (A.jt R0 msg Mu A.Closed) ∧
    (A.zeroK Ex).Know (A.jt R0 msg Mu A.Closed) (A.jt R0 msg Mu A.Zero) ∧
    (A.bitsK P (SK₀ E Ex)).Know (A.jt R0 msg Mu A.Zero) (A.jt R0 msg Mu A.Bitten) :=
  ⟨A.join_know hr Ex Kc M Wp R0 msg Mu,
    A.close_know P Kc M Wp _ R0 msg Mu (A.close_short P Ex Kc M Wp _),
    A.zero_know Ex Kc M Wp R0 msg Mu,
    A.bits_know P Kc M Wp _ R0 msg Mu (A.bits_short P Ex Kc M Wp _)⟩

theorem close_form_short : Bks.FormX (A.closeK P (SK₀ E Ex)) :=
  A.close_form P _ (SK₀_passesC Ex (A.En P).par) (SK₀_copiesC Ex (A.En P).par)

theorem bits_form_short : Bks.FormX (A.bitsK P (SK₀ E Ex)) :=
  A.bits_form P _ (SK₀_passes Ex (A.BT P).par) (SK₀_copies Ex (A.BT P).par)

theorem close_supp_short {G : A.J → Prop} (hP : P.In G) :
    Inv (A.closeK P (SK₀ E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.close_supp P hP _ (SK₀_passesC Ex (A.En P).par)

theorem bits_supp_short {G : A.J → Prop} (hP : P.In G) :
    Inv (A.bitsK P (SK₀ E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.bits_supp P hP _ (SK₀_passes Ex (A.BT P).par)

theorem clo_lam_short :
    (A.closeK P (SK₀ E Ex)).e.toList = (lamClo (Fintype.card E) A.toPub).map (·.c) ∧
    (A.closeK P (SK₀ E Ex)).R.shape.chalList = (lamClo (Fintype.card E) A.toPub).map (·.n) :=
  ⟨(SK₀_errsC Ex (A.En P).par).trans (A.clo_lam P Ex).1,
    (SK₀_valsC Ex (A.En P).par).trans (A.clo_lam P Ex).2⟩

theorem bits_lam_short :
    (A.bitsK P (SK₀ E Ex)).e.toList = (lamBits (Fintype.card E) A.toPub).map (·.c) ∧
    (A.bitsK P (SK₀ E Ex)).R.shape.chalList = (lamBits (Fintype.card E) A.toPub).map (·.n) :=
  ⟨(SK₀_errs Ex (A.BT P).par).trans (A.bits_lam P Ex).1,
    (SK₀_vals Ex (A.BT P).par).trans (A.bits_lam P Ex).2⟩

end Dat
end Lk6

#print axioms Lk6.Dat.four_know_short
#print axioms Lk6.Dat.close_form_short
#print axioms Lk6.Dat.bits_form_short
#print axioms Lk6.Dat.close_supp_short
#print axioms Lk6.Dat.bits_supp_short
#print axioms Lk6.Dat.clo_lam_short
#print axioms Lk6.Dat.bits_lam_short
