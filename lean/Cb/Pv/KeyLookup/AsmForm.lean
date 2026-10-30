-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/AsmForm.lean: two properties of form of the assembled lookup that a link above it
wants, from the like of each
stretch: the caller's state is handed on unchanged; the oracles are only copied.

It imports Cb/Pv/KeyLookup/Asm.lean and the library (`Iop.IOR.Passes`,
`Iop.IOR.OnlyCopies`: Cb/Ld/LdWfPre.lean; `Cb.onlyCopies_post`: Cb/Ld/LdLkpFormat.lean); no file of
    the port.

  `B.Form`        what is asked of the letters: each block hands the field st on, and only copies
                  its oracles.
  `lam1_passes`   B.Form ⇒ whenever the lookup's verifier outputs o from the state st: o.1 = st.
  `lam1_copies`   B.Form ⇒ the lookup only copies its oracles (so R.imp y τ = y).
Nothing on an honest side.

-/
import Cb.Pv.KeyLookup.Asm
import Cb.Ld.LdWfPre
import Cb.Ld.LdLkpFormat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

namespace Bks
variable {E : Type} [Field E] [Fintype E] {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- A block over the one state type hands the caller's state on and only copies its oracles. -/
def FormX (b : BkK A.XS A.XS Ex) : Prop :=
  b.R.Passes (fun x => x.st) (fun x => x.st) ∧ b.R.OnlyCopies

/-- What is asked of the letters. -/
structure Form : Prop where
  head  : B.head.R.Passes id (fun x => x.st) ∧ B.head.R.OnlyCopies
  parts : FormX B.parts
  join  : FormX B.join
  keys  : FormX B.keys
  table : FormX B.table
  clo   : FormX B.clo
  zero  : FormX B.zero
  bits  : FormX B.bits

theorem chn_passes (h : B.Form) : B.chn.R.Passes id (fun x => x.st) :=
  (((((((h.head.1.seq h.parts.1).seq h.join.1).seq h.keys.1).seq h.table.1).seq h.clo.1).seq
    h.zero.1).seq h.bits.1)

theorem chn_copies (h : B.Form) : B.chn.R.OnlyCopies :=
  (((((((h.head.2.seq h.parts.2).seq h.join.2).seq h.keys.2).seq h.table.2).seq h.clo.2).seq
    h.zero.2).seq h.bits.2)

/-- The caller's state is handed on unchanged. -/
theorem lam1_passes (h : B.Form) : B.lam1.R.Passes id (fun o => o.1) :=
  (B.chn_passes h).post _ _ fun x o e => by
    obtain rfl := Option.some.inj e
    rfl

/-- The lookup only copies its oracles. -/
theorem lam1_copies (h : B.Form) : B.lam1.R.OnlyCopies := onlyCopies_post (B.chn_copies h) _

end Bks
end Lk6

#print axioms Lk6.Bks.lam1_passes
#print axioms Lk6.Bks.lam1_copies
