-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Asm.lean: the lookup with parts as ONE chain, put together from its stretches as
letters; and that it is
knowledge sound between the first joint and the last if each stretch is between its own two.

It imports the library, Cb/Pv/KeyLookup/Seams.lean and the kit for blocks without an
honest side (Cb/Pv/Lookup/Know/KnowAt.lean: BkK, Know, know_seq, know_postM); no file of the port.

  `Bks A Ex`      eight blocks without an honest side (a verifier and its errors each), over the one
                  state type of
                  Cb/Pv/KeyLookup/Letters.lean: head (draw and fused tie) · parts · join · keys ·
                  table · clo · zero · bits.
  `B.lam1`        these in a row, then the read-out (a step without rounds).
  `B.Knows …`     what is asked of the letters: each block is `Know` from its joint to the next.
  `lam1_know`     B.Knows ⇒ B.lam1 is `Know` from «every key of every part is a row of the table» to
                  «a claim a part,
                  and the rows», beside any riding joint R0, for every Mu (which `Know` does not
                  read).
No premise's type names an honest prover. Nothing here says that blocks with `Knows` exist: they are
files of their own.

-/
import Cb.Pv.KeyLookup.Seams
import Cb.Pv.Lookup.Know.KnowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

noncomputable section
variable {E : Type} [Field E] [Fintype E]

/-- The stretches that have rounds, as letters. -/
structure Bks (A : Dat E) (Ex : ExtSpec) where
  head  : BkK A.St A.XS Ex
  parts : BkK A.XS A.XS Ex
  join  : BkK A.XS A.XS Ex
  keys  : BkK A.XS A.XS Ex
  table : BkK A.XS A.XS Ex
  clo   : BkK A.XS A.XS Ex
  zero  : BkK A.XS A.XS Ex
  bits  : BkK A.XS A.XS Ex

namespace Bks
variable {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- the chain before the read-out -/
def chn : BkK A.St A.XS Ex :=
  ((((((B.head.seq B.parts).seq B.join).seq B.keys).seq B.table).seq B.clo).seq B.zero).seq B.bits

/-- The lookup at the base: the verifier's side and its errors. -/
def lam1 : BkK A.St A.Out Ex := B.chn.postM A.rd

/-- What is asked of the letters. -/
structure Knows {Kc M Wp : Type} (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) : Prop where
  head  : B.head.Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Tied)
  parts : B.parts.Know (A.jt R0 msg Mu A.Tied) (A.jt R0 msg Mu A.Roots)
  join  : B.join.Know (A.jt R0 msg Mu A.Roots) (A.jt R0 msg Mu A.Joined)
  keys  : B.keys.Know (A.jt R0 msg Mu A.Joined) (A.jt R0 msg Mu fun x μ => A.Table x μ 0)
  table : B.table.Know (A.jt R0 msg Mu fun x μ => A.Table x μ 0) (A.jt R0 msg Mu fun x μ => A.Table
      x μ A.d)
  clo   : B.clo.Know (A.jt R0 msg Mu fun x μ => A.Table x μ A.d) (A.jt R0 msg Mu A.Closed)
  zero  : B.zero.Know (A.jt R0 msg Mu A.Closed) (A.jt R0 msg Mu A.Zero)
  bits  : B.bits.Know (A.jt R0 msg Mu A.Zero) (A.jt R0 msg Mu A.Bitten)

theorem chn_know {Kc M Wp : Type} (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (h : B.Knows R0 msg Mu) :
    B.chn.Know (A.jtIn R0 msg Mu) (A.jt R0 msg Mu A.Bitten) :=
  know_seq (know_seq (know_seq (know_seq (know_seq (know_seq (know_seq h.head h.parts) h.join)
      h.keys)
    h.table) h.clo) h.zero) h.bits

/-- The lookup is knowledge sound between its first joint and its last. -/
theorem lam1_know {Kc M Wp : Type} (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (h : B.Knows R0 msg Mu) :
    B.lam1.Know (A.jtIn R0 msg Mu) (A.jtOut R0 msg) :=
  know_postM A.rd (B.chn_know R0 msg Mu h) (fun _ _ ho => ho)
    fun x _ w _ hw => ⟨hw.1, (A.done_rd x (msg w.1)).1 hw.2⟩

end Bks
end
end Lk6

#print axioms Lk6.Bks.lam1_know
