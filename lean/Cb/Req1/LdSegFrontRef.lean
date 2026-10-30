-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontRef.lean: the whole front of the reference segment as one closed term: shift; the
assembled lookup; claims joined, a sumcheck; a sumcheck again for each map that is given by an inner
sum; a last step.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Req1/LdSegFrontTab.lean has the front in the table's order with "pre" (what comes first) as a
parameter; Cb/Req1/LdSegRefLkpPre.lean has "pre" as a term (the shift; the assembled lookup with its
rows filed as a family of fixed size; two steps). Here the two are one term, and what a segment and
a request require of it is reduced to the blocks' conditions and to conditions on places.
A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of
type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.

Main names (p: the characteristic of E):
  `LdFrontRef E Kc z`: the stage z at which the front ends is a parameter (its oracle messages,
    further oracles, further witness are the front's): so a caller's stage is met by definition. The
    data: Fp (`LdPreD` over z.S, z.E₀, z.Wp, Cb/Req1/LdSegRefLkpPre.lean; it has the first block's
    Z, R0z, msg0); m, T, A0, msg, g0, g: the further sumchecks and the steps; gz: the last step.
  `V.tab`: the data of Cb/Req1/LdSegFrontTab.lean. `V.prog : LdProg V.Fp.s0 z`: no list of moves is
    left as a parameter.
  `V.OK p`: `Fp.OK p` (tags, numbers, places, the multiplicities' clause, the step after the
    lookup); `Link`, `Back`, the evader's law of Z; `VarsOK`, `DegX`, `DegY`, `ValInj` of each
    sumcheck; four clauses for each step.
  `Spec.ldSegFrontRef_hyp`: `V.OK p` → `V.prog.Hyp`.
  `Spec.ldSegFrontRef_kinds`: sendings, sub-protocols and steps only (no sending occurs: by reading
    of the definitions; the statement admits one).
  `Spec.ldSegFrontRef_nums`: the number of rounds `V.prog.nAll` is 1 + the lookup's + 1 +
    (`V.Fp.Z.T.fmt.length` + 3) + the sum over i ≤ m of (`(V.T i).fmt.length` + 3).
  `Spec.ldSegFrontRef_zk`: `V.prog.Zk base` from: `V.OK p`; the lookup's link is a masked block
    (`Link.GoodM`, Ior/KnowCollRulesChain.lean) with letters D (`MaskData`, Ior/Masked.lean), and
    D's fact is in "base"; the lookup reads the entries in RdL only; the places of
    each sumcheck's own masks (`OwnOur`); each sumcheck's fact is in "base", and overwriting its
    masks changes no entry that the lookup or an earlier sumcheck reads (exactly: `ldQuiet`,
    Cb/Req1/LdSegFrontTabZk.lean).
  `Spec.ldSegFrontRef_carry`: under `V.OK p`, `V.Fp.lkBk.SameOn V.Fp.msg RdL` and each sumcheck's
    `OwnOur`: any fact of "base" whose overwriting changes no entry that the lookup or a sumcheck of
    the front reads (`ldQuiet`) is fresh after the front.

Limits: this file does not say that the lookup's link is a masked block and reads RdL only
(Cb/Req1/LdSegRefLkpPreZk.lean: `Spec.ldSegRef_preZk_goodM`, `baseF_sameOn`: each under its
hypotheses, for the letters `F.dm Rd C` and the entries in `A.srAll Dt`; the item "masked messages":
Cb/Ld/LdLkpMask*.lean). It does not say which claims a model's segment has. It says nothing on the
format (Cb/Req1/LdSegFormat*.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFrontTabZk
import Cb.Req1.LdSegRefLkpPreProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp
open scoped ENNReal

/-- The whole front: the data. -/
structure LdFrontRef (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) : Type 1 where
  Fp  : LdPreD E Kc z.S z.E₀ z.Wp
  m   : ℕ
  T   : ℕ → PscOur E
  A0  : ∀ i, Rels Kc (T i).St z.E₀ (z.S.Msg × z.Wp)
  msg : ∀ i, z.S.Msg → (T i).J → E
  g0  : Fp.Z.T.par.Out → E × (T 0).St
  g   : ∀ i, (T i).par.Out → E × (T (i + 1)).St
  gz  : (T m).par.Out → z.St

namespace LdFrontRef
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (V : LdFrontRef E Kc z)

/-- the data of the front in the table's order -/
@[reducible] def tab : LdFrontTab E Kc z :=
  { Z := V.Fp.Z, R0 := V.Fp.R0z, msg0 := V.Fp.msg0, m := V.m, T := V.T, A0 := V.A0, msg := V.msg,
    g0 := V.g0, g := V.g, a := V.Fp.s0, pre := V.Fp.prog, gz := V.gz }

/-- The front. -/
def prog : LdProg V.Fp.s0 z := V.tab.prog

/-- What is asked. -/
structure OK (p : ℕ) : Prop where
  pre   : V.Fp.OK p
  link  : V.Fp.Z.Link
  back  : V.Fp.Z.Back
  ev    : V.Fp.Z.ev.OK
  psc0  : LdFrontTab.PscOK V.Fp.Z.T
  psc   : ∀ i ≤ V.m, LdFrontTab.PscOK (V.T i)
  step0 : LdStepOK z.S V.tab.t0.A (V.tab.s 0).A V.g0
  step  : ∀ i < V.m, LdStepOK z.S (V.tab.t i).A (V.tab.s (i + 1)).A (V.g i)
  post  : LdStepOK z.S (V.tab.t V.m).A z.A V.gz

end LdFrontRef

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldSegFrontRef_hyp : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (z : LdStage E Kc) (V : LdFrontRef E Kc z), V.OK p → V.prog.Hyp

def ldSegFrontRef_kinds : Prop :=
  ∀ (Kc : Type) (z : LdStage E Kc) (V : LdFrontRef E Kc z),
    V.prog.All fun t => t = .send ∨ t = .sub ∨ t = .step

def ldSegFrontRef_nums : Prop :=
  ∀ (Kc : Type) (z : LdStage E Kc) (V : LdFrontRef E Kc z), V.prog.nAll =
    (1 + V.Fp.lkBk.R.shape.nAll) + (1 + (V.Fp.Z.T.fmt.length + 3)) +
      ∑ i ∈ Finset.range (V.m + 1), ((V.T i).fmt.length + 3)

/-- Under the hypotheses below, masks of later blocks pass the front. -/
def ldSegFrontRef_carry : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (z : LdStage E Kc) (V : LdFrontRef E Kc z)
      (RdL : V.Fp.A0.J → Prop) (Rd0 : V.Fp.Z.T.J → Prop) (Rd : ∀ i, (V.T i).J → Prop)
      (base : MaskFact V.Fp.s0.J.W → Prop) (f : MaskFact (z.S.Wit × z.Wp)),
    V.OK p → V.Fp.lkBk.SameOn V.Fp.msg RdL → V.Fp.Z.T.OwnOur Rd0 →
    (∀ j ≤ V.m, (V.T j).OwnOur (Rd j)) → base f → ldQuiet z.S f V.Fp.msg RdL →
    ldQuiet z.S f V.Fp.msg0 Rd0 → (∀ j ≤ V.m, ldQuiet z.S f (V.msg j) (Rd j)) → V.prog.After base f

/-- What zero knowledge asks of the whole front, beside its hypotheses. -/
def ldSegFrontRef_zk : Prop :=
  ∀ (p : ℕ) [CharP E p] (Kc : Type) (z : LdStage E Kc) (V : LdFrontRef E Kc z)
      (D : MaskData (V.Fp.s2.linkA V.Fp.jT V.Fp.lkBk).R V.Fp.s2.J.W) (RdL : V.Fp.A0.J → Prop)
      (Rd0 : V.Fp.Z.T.J → Prop) (Rd : ∀ i, (V.T i).J → Prop) (base : MaskFact V.Fp.s0.J.W → Prop),
    V.OK p → (V.Fp.s2.linkA V.Fp.jT V.Fp.lkBk).GoodM D → base D.fact →
    V.Fp.lkBk.SameOn V.Fp.msg RdL → V.Fp.Z.T.OwnOur Rd0 → (∀ j ≤ V.m, (V.T j).OwnOur (Rd j)) →
    base (V.tab.f0 Rd0) → ldQuiet z.S (V.tab.f0 Rd0) V.Fp.msg RdL →
    (∀ i ≤ V.m, base (V.tab.f i (Rd i))) →
    (∀ i ≤ V.m, ldQuiet z.S (V.tab.f i (Rd i)) V.Fp.msg RdL) →
    (∀ i ≤ V.m, ldQuiet z.S (V.tab.f i (Rd i)) V.Fp.msg0 Rd0) →
    (∀ i ≤ V.m, ∀ j < i, ldQuiet z.S (V.tab.f i (Rd i)) (V.msg j) (Rd j)) → V.prog.Zk base

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem LdFrontRef.tab_ok {Kc : Type} {z : LdStage E Kc} (V : LdFrontRef E Kc z) (p : ℕ)
    [CharP E p] (h : V.OK p) : V.tab.OK :=
  ⟨ldSegRef_pre_hyp E p Kc _ _ _ V.Fp h.pre, h.link, h.back, h.ev, h.psc0, h.psc,
    h.step0, h.step, h.post⟩

end

theorem ldSegFrontRef_hyp (E : Type) [Field E] [Fintype E] : Spec.ldSegFrontRef_hyp E :=
  fun p _ Kc z V h => ldSegTab_hyp E Kc z V.tab (V.tab_ok p h)

theorem ldSegFrontRef_kinds (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRef_kinds E := fun Kc z V =>
  ldSegTab_kinds E Kc z V.tab _ (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl)) (ldSegRef_pre_kinds E Kc _ _ _ V.Fp)

theorem ldSegFrontRef_nums (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRef_nums E := fun Kc z V => by
  have h := (ldSegTab_nums E Kc z V.tab).1
  rw [show V.tab.pre.nAll = 1 + V.Fp.lkBk.R.shape.nAll
      from ldSegRef_pre_rounds E Kc _ _ _ V.Fp] at h
  exact h

theorem ldSegFrontRef_carry (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRef_carry E := fun p _ Kc z V RdL Rd0 Rd base f h hL hO0 hO hb hqL hq0 hq =>
  ldSegTabZk_carry E Kc z V.tab Rd0 Rd base f (V.tab_ok p h) hO0 hO
    (ldSegRef_pre_carry E Kc _ _ _ V.Fp RdL hL base f hqL hb) hq0 hq

theorem ldSegFrontRef_zk (E : Type) [Field E] [Fintype E] :
    Spec.ldSegFrontRef_zk
      E := fun p _ Kc z V D RdL Rd0 Rd base h hM hD hL hO0 hO hf0 hq0L hf hqL hq0 hq =>
  ldSegTabZk E Kc z V.tab Rd0 Rd base (V.tab_ok p h)
    (ldSegRef_pre_zk E p Kc _ _ _ V.Fp base D h.pre hM hD) hO0 hO
    (ldSegRef_pre_carry E Kc _ _ _ V.Fp RdL hL base _ hq0L hf0)
    (fun i hi => ldSegRef_pre_carry E Kc _ _ _ V.Fp RdL hL base _ (hqL i hi) (hf i hi)) hq0 hq

end Cb
