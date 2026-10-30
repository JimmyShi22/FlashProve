-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseForm.lean: the join point, the closing, the zero point and the test of the bits
hand the caller's state on unchanged and only copy their oracles (`Bks.FormX`, AsmForm.lean).

It imports Join.lean, Bits.lean, Cb/Pv/KeyLookup/AsmForm.lean and the library; no file of the port.

  `join_form`, `zero_form`    no condition: a draw.
  `close_form`, `bits_form`   two conditions on the letter at this sumcheck: it hands its state on,
                              and it only copies its oracles.
  `close_form_lib`, `bits_form_lib`   the library's verifier meets both
                              (Cb/Ld/LdLkpFormat.lean).
Nothing on an honest side.

-/
import Cb.Pv.KeyLookup.Join
import Cb.Pv.KeyLookup.Bits
import Cb.Pv.KeyLookup.AsmForm
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (Ex : ExtSpec)

theorem join_form : Bks.FormX (A.joinK Ex) :=
  ⟨Passes.draw _ _ Ex _ _ fun _ _ => rfl, OnlyCopies.draw _ _ Ex⟩

theorem zero_form : Bks.FormX (A.zeroK Ex) :=
  ⟨Passes.draw _ _ Ex _ _ fun _ _ => rfl, OnlyCopies.draw _ _ Ex⟩

variable {Ex}

theorem close_form (SK : PscLtK E Ex)
    (h1 : (SK.core (A.En P).par).R.Passes Prod.snd PscPar.Mid.st)
    (h2 : (SK.core (A.En P).par).R.OnlyCopies) : Bks.FormX (A.closeK P SK) :=
  ⟨((passes_map h1 fun x : A.XS => x.st).pre _ _ fun x x' e => by
      obtain rfl := Option.some.inj e
      rfl).post _ _ fun zz x' e => by
      obtain rfl := Option.some.inj e
      rfl,
    onlyCopies_post (onlyCopies_pre h2 _) _⟩

theorem bits_form (SK : PscLtK E Ex)
    (h1 : (SK.full (A.BT P).par).R.Passes Prod.snd PscPar.Out.st)
    (h2 : (SK.full (A.BT P).par).R.OnlyCopies) : Bks.FormX (A.bitsK P SK) :=
  ⟨((passes_map h1 fun s : (A.BT P).St => s.1.st).pre _ _ fun x x' e => by
      obtain rfl := Option.some.inj e
      rfl).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl,
    onlyCopies_post (onlyCopies_pre h2 _) _⟩

theorem close_form_lib : Bks.FormX (A.closeK P (PscLtK.lib E Ex)) :=
  A.close_form P _ (core_passes (A.En P).par Ex) (core_onlyCopies (A.En P).par Ex)

theorem bits_form_lib : Bks.FormX (A.bitsK P (PscLtK.lib E Ex)) :=
  A.bits_form P _ (psc_passes (A.BT P).par Ex) (psc_onlyCopies (A.BT P).par Ex)

end Dat
end Lk6

#print axioms Lk6.Dat.join_form
#print axioms Lk6.Dat.zero_form
#print axioms Lk6.Dat.close_form
#print axioms Lk6.Dat.bits_form
#print axioms Lk6.Dat.close_form_lib
#print axioms Lk6.Dat.bits_form_lib
