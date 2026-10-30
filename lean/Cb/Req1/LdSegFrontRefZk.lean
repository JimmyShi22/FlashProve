-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontRefZk.lean: what zero knowledge asks of the whole front of the reference segment
(`V.prog.Zk base`), beside its hypotheses (`V.prog.Hyp`): no hypothesis on a link is left.

Statements (in `Cb.Spec`) and proofs.
Cb/Req1/LdSegFrontRef.lean still asks of the lookup: "its link is a masked block" and "it reads the
entries in RdL only". Cb/Req1/LdSegRefLkpPreZk.lean, for E of characteristic p and `z.E₀.Str`
nonempty, shows both from the lookup's own conditions on places and on its claim
(`Fp.ZkOK p Dt Rd C`). Here they are put in.
A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of
type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.

Main names (both for E of characteristic p and `z.E₀.Str` nonempty):
  `Spec.ldSegFrontRefZk`: `V.prog.Zk base` from: `V.OK p`; `Fp.ZkOK p Dt RdK C` (the lookup's
    places; the claim with which its item starts); the places of each sumcheck's own masks
    (`OwnOur`); the facts of the lookup and of each sumcheck are in "base" (fresh at the segment's
    entry), and overwriting the masks of a sumcheck changes no entry that the lookup or an earlier
    sumcheck reads.
  `Spec.ldSegFrontRefZk_carry`: under `V.OK p`, `Fp.ZkOK p Dt RdK C` and each sumcheck's `OwnOur`:
    any fact of "base" whose overwriting changes no entry that the lookup or a sumcheck of the front
    reads is fresh after the front.

Limits: no hypothesis on a link or on an honest prover ("is a masked block", "does not look") is
left. What is left: `V.OK p`; conditions on places and on the lookup's claim (`ZkOK`, `OwnOur`); on
the facts: overwriting the masks of one block changes no entry that an earlier block reads
("quiet"; exactly: `ldQuiet`, Cb/Req1/LdSegFrontTabZk.lean); and that the facts are in "base": fresh
at the segment's entry, which is the matter of the sendings before it.
This file does not say that the conditions can be met together.
On "quiet": pairwise different places for the masks of different blocks are not enough: the clause
speaks of all pairs of witnesses whose readings by the later block's fact differ by the overwriting;
so every entry that an earlier block reads must also be shown by the later block's reading, and be
none of its own places: readings that grow along the front (Cb/Req1/LdSegFrontToyKit.lean:
`psc_quiet`; met at the toy of Cb/GlVal/GlJ3SegFrontToy.lean; there, with one further sumcheck
(m = 0), "quiet for the further sumchecks before it" holds for want of cases).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFrontRef
import Cb.Req1.LdSegRefLkpPreZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldSegFrontRefZk_carry : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (z : LdStage E Kc) [Nonempty z.E₀.Str] (V : LdFrontRef E Kc z)
      (Dt RdK : V.Fp.A0.J → Prop) (C : V.Fp.St × E → (V.Fp.A0.J → E) → Prop)
      (Rd0 : V.Fp.Z.T.J → Prop) (Rd : ∀ i, (V.T i).J → Prop) (base : MaskFact V.Fp.s0.J.W → Prop)
      (f : MaskFact (z.S.Wit × z.Wp)),
    V.OK p → V.Fp.ZkOK p Dt RdK C → V.Fp.Z.T.OwnOur Rd0 → (∀ j ≤ V.m, (V.T j).OwnOur (Rd j)) →
    base f → ldQuiet z.S f V.Fp.msg (V.Fp.A.srAll Dt) → ldQuiet z.S f V.Fp.msg0 Rd0 →
    (∀ j ≤ V.m, ldQuiet z.S f (V.msg j) (Rd j)) → V.prog.After base f

/-- What zero knowledge asks of the whole front, beside its hypotheses. -/
def ldSegFrontRefZk : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (z : LdStage E Kc) [Nonempty z.E₀.Str] (V : LdFrontRef E Kc z)
      (Dt RdK : V.Fp.A0.J → Prop) (C : V.Fp.St × E → (V.Fp.A0.J → E) → Prop)
      (Rd0 : V.Fp.Z.T.J → Prop) (Rd : ∀ i, (V.T i).J → Prop) (base : MaskFact V.Fp.s0.J.W → Prop),
    V.OK p → V.Fp.ZkOK p Dt RdK C → V.Fp.Z.T.OwnOur Rd0 → (∀ j ≤ V.m, (V.T j).OwnOur (Rd j)) →
    base (V.Fp.dm RdK C).fact → base (V.tab.f0 Rd0) →
    ldQuiet z.S (V.tab.f0 Rd0) V.Fp.msg (V.Fp.A.srAll Dt) → (∀ i ≤ V.m, base (V.tab.f i (Rd i))) →
    (∀ i ≤ V.m, ldQuiet z.S (V.tab.f i (Rd i)) V.Fp.msg (V.Fp.A.srAll Dt)) →
    (∀ i ≤ V.m, ldQuiet z.S (V.tab.f i (Rd i)) V.Fp.msg0 Rd0) →
    (∀ i ≤ V.m, ∀ j < i, ldQuiet z.S (V.tab.f i (Rd i)) (V.msg j) (Rd j)) → V.prog.Zk base

end
end Spec

theorem ldSegFrontRefZk_carry (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRefZk_carry
      E := fun p _ Kc z _ V Dt RdK C Rd0 Rd base f h hK hO0 hO hb hqL hq0 hq =>
  ldSegTabZk_carry E Kc z V.tab Rd0 Rd base f (V.tab_ok p h) hO0 hO
    (ldSegRef_preZk_carry E p Kc _ _ _ V.Fp Dt RdK C base f hK hqL hb) hq0 hq

theorem ldSegFrontRefZk (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRefZk
      E := fun p _ Kc z _ V Dt RdK C Rd0 Rd base h hK hO0 hO hD hf0 hq0L hf hqL hq0 hq =>
  ldSegTabZk E Kc z V.tab Rd0 Rd base (V.tab_ok p h)
    (ldSegRef_preZk_zk E p Kc _ _ _ V.Fp Dt RdK C base hK hD) hO0 hO
    (ldSegRef_preZk_carry E p Kc _ _ _ V.Fp Dt RdK C base _ hK hq0L hf0)
    (fun i hi => ldSegRef_preZk_carry E p Kc _ _ _ V.Fp Dt RdK C base _ hK (hqL i hi) (hf i hi))
    hq0 hq

end Cb
