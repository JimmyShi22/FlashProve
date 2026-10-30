-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseAlt.lean: sequential composition of interactive oracle reductions: the last part of
such a reduction (a closing), in which proximity tests on groups of oracles (whole tests) alternate
with sub-reductions that send, drop and test no oracle (fronts): "front ; tests ; front ; tests".

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseAltProofs.lean. Generic: no protocol.
It uses Cb/Ld/LdLinCloseChain.lean (a closing as a chain: `LdTc`; one whole test in front of a
closing: `LdTc.cons`), Cb/Ld/LdFront.lean (a front: steps without rounds, batchings, splittings over
one signature), Ior/KnowCollPiece.lean (a chain that comes after another: `OkFrom`) and
Cb/Ld/LdTowerKitChain.lean (the budgets' halves).
No new data: a closing is still an `LdTc` (explicit part, base joint, chain, demand on positions).

Why: Cb/Ld/LdLinCloseChain.lean calls a closing in order (`Q.OK`) if every link has the whole bundle
(`Link.GoodT`, Ior/KnowCollRulesChain.lean) by itself (and `Q.c.SidesCT Q.q` holds). A splitting has
not: it is a masked block, honest-verifier zero knowledge only behind the rounds that sent its mask.
Cb/Ld/LdLinCloseSplit.lean therefore puts all splittings in one front, before all tests.

Main names:
  `Q.OkBehind c₀`: the closing is in order after the chain c₀: each of its links has the whole
    bundle, or is a masked block whose masks are fresh after c₀ and the closing's earlier links
    (`OkFrom`); and the budgets' halves fit (`SidesCT`, Cb/Ld/LdTowerKitChain.lean). It is a premise
    of `Spec.ldLinAlt_tail` (Cb/Ld/LdLinCloseDemandT.lean), which concludes that the test for linear
    constraints with the closing `C.cZ Q fq` is a tail (`TailTr`, Cb/Ld/LdTowerKit.lean).
  `LdTc.front x Q p`: the front p, from the stage x down to Q's first joint, in front of Q. (Its
    chain begins with the link that does nothing: a front has to come after something.)
  `Spec.ldAlt_cons`, a whole test in front: `D.OK`, and Q in order after (c₀, then the test) ⇒ "the
    test D, then Q" is in order after c₀.
  `Spec.ldAlt_front`, a front in front: c₀ is a chain of the two kinds (`c₀.Ok`); the moves' own
    hypotheses; every step has the budgets' half at Q's demand; what is asked for the splittings
    (`p.ZkOK Rd Rr ..`, Cb/Ld/LdFront.lean; Rd is a set of entries, Rr a set of oracle messages) at
    "fresh after c₀" (and the link that does nothing); Q in order after (c₀, then the front) ⇒ "the
    front, then Q" is in order after c₀.
  `Spec.ldAlt_demand`: a front needs of the oracles what follows it needs: the demand of
    `LdTc.front x Q p` is Q's, by definition.
  So "front ; tests ; front ; tests" is
  front x₁ (cons D₁ (cons D₂ (front x₂ (cons D₃ (cons D₄ Q')) p₂))) p₁, in order after c₀ by five
  applications (`ldAlt_front` twice, `ldAlt_cons` twice, `ldAlt_of_ok` once), under their hypotheses
  (`LdLinPtT.Q`, `Spec.ldLinPtT_behind`, Cb/Ld/LdLinCloseDemandT.lean).

What of this file a write-up of ours (lean/CREDITS.md) uses, and what it does not (by a
reading).
  The write-up's test for linear constraints has one splitting, in what the instances share,
  before all tests, and no scalar of an instance's own (Cb/Ld/LdLinClosePlanP.lean). So in it no
  front stands behind a whole test.
  Used by its plan: `LdTc.front` (the closing as one term with its front inside: the closings for a
  batch are built on that term), `Q.OkBehind`, `ldAlt_front`, `ldAlt_of_ok`
  (Cb/Ld/LdLinCloseDemandPA.lean).
  Not used by it: a front behind tests (`ldAlt_cons` under a front; "front ; tests ; front ;
  tests"): that serves the wider plan with a second splitting, of the instance's own
  (Cb/Ld/LdLinClosePlanT.lean), which is this library's own. For that plan: first what the instances
  share (splitting, tests); then each instance's own (splitting, tests). So a splitting stands
  behind whole tests.
  Why: the compiler takes an instance's rounds, one block of shared rounds, an instance's rounds; an
  instance's scalar between shared rounds would break that. Two things are kept (the second as a
  premise: `noU`, `noO` of `LdLinPt.Plain`, Cb/Ld/LdLinClosePlanT.lean): the mask entry is sent and
  sampled before the scalar; no test on a group that holds an instance's mask-only message
  comes before that instance's splitting (what the write-up asks of every message that
  holds a mask for a later block: while it is pending, the verifier does not query its mask rows).

Limits: this file does not say that a mask is still fresh behind a whole test: `ldAlt_front` asks
freshness after all that stands before the front, tests included; that a test does not look at a
mask which it only carries is another file's. Nothing on batches: one instance's chain.
The bookkeeping is this library's own.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdFrontProofs
import Cb.Ld.LdLinkCloseProofs
import Cb.Req1.LdSegProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdTc
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- The closing is in order after c₀. -/
def OkBehind (Q : LdTc S E₀ Wp) {Z : Joint Unit} (c₀ : Chain Unit Z (S.jointCf Q.base)) : Prop :=
  Q.c.OkFrom c₀ ∧ Q.c.SidesCT Q.q

variable [Fintype E]

/-- the links of a front, as a chain from its first stage -/
def frontC {x y : FSt S E₀ Wp Unit} (p : Front x y) :
    Chain Unit x.stage.J y.stage.J :=
  p.prog.onto (.one x.stage.idLink)

/-- A front in front of a closing. -/
def front (x : FSt S E₀ Wp Unit) (Q : LdTc S E₀ Wp) (p : Front x ⟨Q.St, Q.base⟩) :
    LdTc S E₀ Wp where
  St := x.St
  base := x.A
  c := (frontC p).append Q.c
  q := Q.q

end LdTc

namespace Spec

def ldAlt_of_ok : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (Q : LdTc S E₀ Wp)
      (Z : Joint Unit) (c₀ : Chain Unit Z (S.jointCf Q.base)),
    Q.OK → Q.OkBehind c₀

/-- A whole test in front. -/
def ldAlt_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (Z : Joint Unit)
      (c₀ : Chain Unit Z (S.jointCf (D.pre Q.base))),
    D.OK → Q.OkBehind (c₀.snoc (D.link Q.base d d')) → (LdTc.cons D Q d d').OkBehind c₀

/-- A front in front. -/
def ldAlt_front : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x : FSt S E₀ Wp Unit)
      (Q : LdTc S E₀ Wp) (p : Front x ⟨Q.St, Q.base⟩) (Z : Joint Unit) (c₀ : Chain Unit Z x.stage.J)
      (Rd : S.Ent → Prop) (Rr : S.O → Prop),
    c₀.Ok → p.prog.Hyp → p.Sd Q.q →
    p.ZkOK Rd Rr (fun g => (c₀.append (.one x.stage.idLink)).FreshFor g.kc g.Mk g.put) →
    Q.OkBehind (c₀.append (LdTc.frontC p)) → (LdTc.front x Q p).OkBehind c₀

def ldAlt_demand : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x : FSt S E₀ Wp Unit)
      (Q : LdTc S E₀ Wp) (p : Front x ⟨Q.St, Q.base⟩),
    (LdTc.front x Q p).q = Q.q

end Spec
end Cb
