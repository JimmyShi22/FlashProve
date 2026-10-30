-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontV.lean: a front with one splitting for a batch: the honest side.

In the words of lean/GLOSSARY.md: honest side: the honest prover of a protocol or reduction, as
data: its coins, its strategy, and the sets of verifier randomness that its analysis names.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdFrontVProofs.lean. Generic: no
protocol.
It builds on Cb/Ld/LdFrontB.lean (`p.cA sh`: a front's links for a batch, with annotations),
Cb/Ld/LdSplitV.lean (the splitting as a masked link of a batch, in every slot or by the shared
part), Cb/Ld/LdLinCloseVPlan.lean (a link in every slot: `l.loV`; when it is a piece) and
Cb/Ld/LdAltB.lean (`LdTcV.front` takes any chain with honest sides over the front's annotated links;
`ldAltV_front` asks that it stands behind what comes before).

The shape: the link that does nothing ; one splitting ; a link L without masks in every slot (meant:
the step without rounds in which each row goes to its test). The fronts of a closing step of the
test for linear constraints have this shape (Cb/Ld/LdLinClosePlanT.lean).
Along the front the shared witness (W0) stays; the demand on families of positions is q up to L and
q₃ after it; the ties (`JV.tie`, Cb/Ld/LdLinChainV.lean: how a slot's statement and witness are tied
to the shared witness) t₁ (at the start), t₂ (after the splitting), t₃ (at the end) are parameters,
t₂ and t₃ each with "it is carried".

Main names:
  `ldFrLo D N W0 t₁ q t₂ L t₃ q₃`: the chain with honest sides, the splitting in every slot (an
    instance's own closing step).
  `ldFrSh D N W0 t₁ q rd t₂ L t₃ q₃`: the same, the splitting by the shared part (the shared closing
    step); rd reads off the shared witness the messages, cut to what the splitting reads, and its
    public part.
  `Spec.frontV_forgetLo`, `Spec.frontV_forgetSh`: at the front p = nil ; split ; step: their
    annotated links are `p.cA false`, `p.cA true`: the hypothesis hV of `LdTcV.front`
    (Cb/Ld/LdAltB.lean).
  `Spec.frontV_lo`: `ldFrLo` stands behind c₀ (`OkFromV`), if: the splitting's hypotheses (`D.Hyp`);
    L has the whole bundle (`L.GoodT`) and withholds nothing in secret (`∀ w x, L.H.Hid w x = ∅`);
    the two ties are carried; L bears what follows (`BearsV`); the demands are kept by subsets of
    slots (`q.Her`, `q₃.Her`); the mask entry of each slot is fresh, for sets of slots, after c₀
    (`FreshForV`).
  `Spec.frontV_sh`: the same for `ldFrSh`, under the hypotheses of `Spec.frontV_lo` but the last,
    and: on tied statements rd reads what the slots hold; the shared mask entry is fresh after c₀
    (`FreshForV` at `(D.mask.tagPub xp₀).sharedV rd N`, for some xp₀; `MaskData.tagPub`,
    Cb/Ld/LdSplitV.lean).
  `Spec.idleV_fresh`: M0, Mj nonempty: the link that does nothing, in every slot, carries every fact
    for sets of slots.

`L.GoodT` is a hypothesis of `Spec.frontV_lo` and `Spec.frontV_sh`. `IOR.GoodT` (likewise
`IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between
two joints, at given numbers; among its clauses: completeness between the honest relations, outside
sets of verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.

Limits: this file says nothing on fronts with several splittings or with a batching. It does not say
that the entry is fresh after c₀. It says nothing on soundness (Cb/Ld/LdFrontB.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFrontB
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E] (D : LdSplD E Unit) (N : ℕ) (W0 : Type)
  (t₁ : W0 → D.src.J.X → D.src.J.E.Str → D.src.J.W → Prop) (q : QFam D.src.J.E N)

/-- The splitting in every slot. -/
def ldFrLo (t₂ : W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop) {B : Joint Unit}
    (L : Link Unit D.tgt.J B) (t₃ : W0 → B.X → B.E.Str → B.W → Prop) (q₃ : QFam B.E N) :
    ChainV Unit N (⟨W0, t₁, q⟩ : JV N D.src.J) (⟨W0, t₃, q₃⟩ : JV N B) :=
  ((ChainV.one (D.src.idLink.loV N ⟨W0, t₁, q⟩ t₁ q)).snoc (D.link.loV N ⟨W0, t₁, q⟩ t₂ q)).snoc
    (L.loV N ⟨W0, t₂, q⟩ t₃ q₃)

/-- The splitting by the shared part. -/
def ldFrSh (rd : W0 → D.S.Msg × (E × (D.St₁ × D.St₂)))
    (t₂ : W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop) {B : Joint Unit}
    (L : Link Unit D.tgt.J B) (t₃ : W0 → B.X → B.E.Str → B.W → Prop) (q₃ : QFam B.E N) :
    ChainV Unit N (⟨W0, t₁, q⟩ : JV N D.src.J) (⟨W0, t₃, q₃⟩ : JV N B) :=
  ((ChainV.one (D.src.idLink.loV N ⟨W0, t₁, q⟩ t₁ q)).snoc
      (D.link.shV N (⟨W0, t₁, q⟩ : JV N D.src.J)
        (ldSplS0 D fun w0 => ((rd w0).1, (rd w0).2.2.1)) t₂ q)).snoc
    (L.loV N ⟨W0, t₂, q⟩ t₃ q₃)

end

namespace Spec

/-- M0, Mj nonempty: the link that does nothing carries every fact for sets of slots. -/
def idleV_fresh : Prop :=
  ∀ (E : Type) [Field E] (a : LdStage E Unit) (N : ℕ) (VA : JV N a.J) (Z : Joint Unit)
      (VZ : JV N Z) (c₀ : ChainV Unit N VZ VA) (K0 Kj : Type) (k0 : VA.W0 → K0) (kj : a.J.W → Kj)
      (M0 : Type) [Fintype M0] [Nonempty M0] (put0 : M0 → K0 → K0) (Mj : Type) [Fintype Mj]
      [Nonempty Mj] (putj : Mj → Kj → Kj),
    c₀.FreshForV k0 kj M0 put0 Mj putj →
    (c₀.snoc (a.idLink.loV N VA VA.tie VA.q)).FreshForV
      (VB := ⟨VA.W0, VA.tie, VA.q⟩) k0 kj M0 put0 Mj putj

section
variable (E : Type) [Field E] [Fintype E]

/-- Its annotated links are the front's. -/
def frontV_forgetLo : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
      (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
      (z : FSt S E₀ Wp Unit) f g m back (N : ℕ) (W0 : Type) t₁ q t₂ t₃ q₃,
    (ldFrLo (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N W0 t₁ q t₂
        (Front.stepL _ z f g m back) t₃ q₃).forget =
      (Front.step (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs (Front.nil _))
        z f g m back).cA false

def frontV_forgetSh : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
      (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
      (z : FSt S E₀ Wp Unit) f g m back (N : ℕ) (W0 : Type) t₁ q rd t₂ t₃ q₃,
    (ldFrSh (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N W0 t₁ q rd t₂
        (Front.stepL _ z f g m back) t₃ q₃).forget =
      (Front.step (Front.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs (Front.nil _))
        z f g m back).cA true

/-- States: under the hypotheses below, the instance's own front stands behind c₀. -/
def frontV_lo : Prop :=
  ∀ (D : LdSplD E Unit) (N : ℕ) (W0 : Type) (t₁ : W0 → D.src.J.X → D.src.J.E.Str → D.src.J.W → Prop)
      (q : QFam D.src.J.E N) (t₂ : W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop)
      (B : Joint Unit) (L : Link Unit D.tgt.J B) (t₃ : W0 → B.X → B.E.Str → B.W → Prop)
      (q₃ : QFam B.E N) (Z : Joint Unit) (VZ : JV N Z)
      (c₀ : ChainV Unit N VZ (⟨W0, t₁, q⟩ : JV N D.src.J)),
    D.Hyp → L.GoodT → (∀ w x, L.H.Hid w x = ∅) → q.Her → q₃.Her →
    (∀ x y w, (⟨W0, t₁, q⟩ : JV N D.src.J).rel x y w →
      t₂ w.1 (splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1))
        y w.2) →
    (∀ x y w c ρ, (⟨W0, t₂, q⟩ : JV N D.tgt.J).rel x y w → ρ ∉ L.H.Bad →
      t₃ w.1 ((L.H.strat w.2 x c).run ρ).2.1
        (L.R.imp y ((L.H.strat w.2 x c).run ρ).1) ((L.H.strat w.2 x c).run ρ).2.2) →
    L.R.BearsV (RoundSplits.allLocal _) (budEach L.R N L.P.bud) q q₃ →
    c₀.FreshForV (D.mask.localV W0 N).k0 (D.mask.localV W0 N).kj (D.mask.localV W0 N).M0
      (D.mask.localV W0 N).put0 (D.mask.localV W0 N).Mj (D.mask.localV W0 N).putj →
    (ldFrLo D N W0 t₁ q t₂ L t₃ q₃).OkFromV c₀

/-- States: under the hypotheses below, the shared front stands behind c₀. -/
def frontV_sh : Prop :=
  ∀ (D : LdSplD E Unit) (N : ℕ) (W0 : Type) (t₁ : W0 → D.src.J.X → D.src.J.E.Str → D.src.J.W → Prop)
      (q : QFam D.src.J.E N) (rd : W0 → D.S.Msg × (E × (D.St₁ × D.St₂))) (xp₀ : E × (D.St₁ × D.St₂))
      (t₂ : W0 → D.tgt.J.X → D.tgt.J.E.Str → D.tgt.J.W → Prop) (B : Joint Unit)
      (L : Link Unit D.tgt.J B) (t₃ : W0 → B.X → B.E.Str → B.W → Prop) (q₃ : QFam B.E N)
      (Z : Joint Unit) (VZ : JV N Z) (c₀ : ChainV Unit N VZ (⟨W0, t₁, q⟩ : JV N D.src.J)),
    D.Hyp → L.GoodT → (∀ w x, L.H.Hid w x = ∅) → q.Her → q₃.Her →
    (∀ x y w, (⟨W0, t₁, q⟩ : JV N D.src.J).rel x y w →
      (rd w.1).1 = D.S.cut D.Rd (D.S.msgs w.2.1) ∧ (rd w.1).2 = x.1.1) →
    (∀ x y w, (⟨W0, t₁, q⟩ : JV N D.src.J).rel x y w →
      t₂ w.1 (splitNx D.S D.St₁ D.St₂ D.St₀ x (splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1))
        y w.2) →
    (∀ x y w c ρ, (⟨W0, t₂, q⟩ : JV N D.tgt.J).rel x y w → ρ ∉ L.H.Bad →
      t₃ w.1 ((L.H.strat w.2 x c).run ρ).2.1
        (L.R.imp y ((L.H.strat w.2 x c).run ρ).1) ((L.H.strat w.2 x c).run ρ).2.2) →
    L.R.BearsV (RoundSplits.allLocal _) (budEach L.R N L.P.bud) q q₃ →
    c₀.FreshForV ((D.mask.tagPub xp₀).sharedV rd N).k0 ((D.mask.tagPub xp₀).sharedV rd N).kj
      ((D.mask.tagPub xp₀).sharedV rd N).M0 ((D.mask.tagPub xp₀).sharedV rd N).put0
      ((D.mask.tagPub xp₀).sharedV rd N).Mj ((D.mask.tagPub xp₀).sharedV rd N).putj →
    (ldFrSh D N W0 t₁ q rd t₂ L t₃ q₃).OkFromV c₀

end
end Spec
end Cb
