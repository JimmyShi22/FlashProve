-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontOn.lean: for the front "one splitting, then each row goes to its test", run by the
shared part of a batch, the keys and the honest side are got from conditions at the front's two
ends. (not all hypotheses are named here: see `Spec.frontOn_sh`)

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdFrontOnProofs.lean. Generic: no
protocol.
It builds on Cb/Ld/LdFrontB.lean (`p.cA true`: a front's links for a batch, with annotations, and
with batchings and splittings once by the shared part; `p.Keys`; `frontB_kb`), Cb/Ld/LdFrontV.lean
(`ldFrSh`; `frontV_sh`) and Cb/Ld/LdBatPeel.lean (a step that, as used in this file, only maps the
explicit part: `sideF`, `sideG`, `sideM`, `sideB`).

The front. `Front.on1 .. z f` := nil (in its links for a batch, `p.cA`: the link that does nothing)
; the splitting (G₁, G₂, k, rows sl₁, sl₂, beside A₀) ; the step without rounds that maps the
explicit part by f and leaves samples, oracles, witness. (The front of the closing of the test for
linear constraints has this form by definition: Cb/Ld/LdLinClosePlanP.lean.)

Why: Cb/Ld/LdFrontB.lean and Cb/Ld/LdFrontV.lean ask for a key and a tie at every stage of a front.
Here the ones between are chosen, so that only the two ends are left. A key (`JKey`,
Cb/Ld/LdLinChainB.lean): what the statements of one batch have in common at a stage. A tie
(`JV.tie`, Cb/Ld/LdLinChainV.lean): how a slot's statement and witness are tied to the shared
witness.

Main names:
  `Front.spTie ..`: the tie after the splitting: "comes from a tied statement by the honest scalar".
  `Front.onV ..`: the chain with honest sides: `ldFrSh` with that tie.
  `Spec.frontOn_keys`: kx at the start, kz at the end, F: if for every statement a and every scalar
    u the key of (f of the split explicit part, samples, oracles) is F (key of a) u, then
    `p.Keys true N kx kz`. With `frontB_kb`, under the moves' own hypotheses (`p.prog.Hyp`): the
    front by the shared part is knowledge sound for the vectors with one key (limits: the head of
    Cb/Ld/LdFrontB.lean).
  `Spec.frontOn_forget`: the annotated links of `Front.onV` are `p.cA true`.
  `Spec.frontOn_sh`: `Front.onV` stands behind c₀ (`OkFromV`) if: the moves' hypotheses
    (`prog.Hyp`); the demand is kept by subsets of slots (`q.Her`); on tied statements rd reads, off
    the shared witness, the messages cut to what the splitting reads, and its public part; the tie
    t₃ at the end holds of what the honest front makes of a tied statement; the shared mask entry is
    fresh, for sets of slots, after c₀ (`FreshForV` at
    `((Front.splD ..).mask.tagPub xp₀).sharedV rd N`, for some xp₀; `MaskData.tagPub`,
    Cb/Ld/LdSplitV.lean).

In the words of lean/GLOSSARY.md: annotation: of the shape of a batch protocol: for each round
whether it is local or shared, and how a prover message of a local transcript splits into the shared
part, which is one for all slots of the batch, and the part of one slot.

Limits: this file does not say that the entry is fresh (at the standard senders of the test for
linear constraints: Cb/Ld/LdLinStdSpV.lean: `ldSpV_fresh`). It says nothing on the same front in
every slot.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFrontV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Front
section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (G₁ G₂ : Grp S)
  (k : SplitAt G₁ G₂) (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J)
  (St₀ : Type) (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
  (z : FSt S E₀ Wp Unit) (f : ((E × St₁) × (E × St₂)) × St₀ → z.St)

/-- One splitting; then each row goes to its test. -/
def on1 : Front (⟨_, claimRels (splitIn sl₁ sl₂) A₀⟩ : FSt S E₀ Wp Unit) z :=
  .step (.split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs (.nil _))
    z (sideF S f) (sideG S (ExtMap.id E₀)) (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2)

variable (N : ℕ) (W0 : Type)
  (t₁ : W0 → (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.X →
    (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.E.Str →
    (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.W → Prop)
  (q : QFam (E₀.prod S.ext) N)

/-- the tie after the splitting -/
def spTie :
    W0 → (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt.J.X →
    (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt.J.E.Str →
    (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt.J.W → Prop :=
  fun w0 x' y w =>
    ∃ x,
      (⟨W0, t₁, q⟩ : JV N (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J).rel x y (w0, w) ∧
      x' = splitNx S St₁ St₂ St₀ x (splitVal k sl₁ (S.msgs w.1) x.1.1.2.1)

/-- The chain with honest sides: the splitting by the shared part. -/
def onV (rd : W0 → S.Msg × (E × (St₁ × St₂)))
    (t₃ : W0 → z.stage.J.X → z.stage.J.E.Str → z.stage.J.W → Prop) :
    ChainV Unit N (⟨W0, t₁, q⟩ : JV N (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J)
      (⟨W0, t₃, q⟩ : JV N z.stage.J) :=
  ldFrSh (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N W0 t₁ q rd
    (spTie G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs N W0 t₁ q)
    (stepL (⟨_, (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt.A⟩ : FSt S E₀ Wp Unit) z
      (sideF S f) (sideG S (ExtMap.id E₀)) (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2))
    t₃ q

end
end Front

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- Keys: from the two ends. -/
def frontOn_keys : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
      (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
      (z : FSt S E₀ Wp Unit) (f : ((E × St₁) × (E × St₂)) × St₀ → z.St) (N : ℕ)
      (kx : JKey (⟨_, claimRels (splitIn sl₁ sl₂) A₀⟩ : FSt S E₀ Wp Unit).stage.J)
      (kz : JKey z.stage.J) (F : kx.κ → E → kz.κ),
    (∀ a u, kz.key
        ((f (splitNx S St₁ St₂ St₀ a.1 u).1, (splitNx S St₁ St₂ St₀ a.1 u).2),
          (sideG S (ExtMap.id E₀)).map a.2) =
      F (kx.key a) u) →
    (Front.on1 G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f).Keys true N kx kz

def frontOn_forget : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂)
      (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop)
      (dRs : DecidablePred Rs) (z : FSt S E₀ Wp Unit)
      (f : ((E × St₁) × (E × St₂)) × St₀ → z.St) (N : ℕ) (W0 : Type) t₁ q rd t₃,
    (Front.onV G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f N W0 t₁ q rd t₃).forget =
      (Front.on1 G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f).cA true

/-- The honest side: from the two ends. -/
def frontOn_sh : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
      (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Unit St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
      (z : FSt S E₀ Wp Unit) (f : ((E × St₁) × (E × St₂)) × St₀ → z.St) (N : ℕ) (W0 : Type)
      (t₁ : W0 → (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.X →
        (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.E.Str →
        (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J.W → Prop)
      (q : QFam (E₀.prod S.ext) N) (rd : W0 → S.Msg × (E × (St₁ × St₂))) (xp₀ : E × (St₁ × St₂))
      (t₃ : W0 → z.stage.J.X → z.stage.J.E.Str → z.stage.J.W → Prop) (Z : Joint Unit) (VZ : JV N Z)
      (c₀ : ChainV Unit N VZ
        (⟨W0, t₁, q⟩ : JV N (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J)),
    (Front.on1 G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f).prog.Hyp → q.Her →
    (∀ x y w, (⟨W0, t₁, q⟩ : JV N (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J).rel
        x y w →
      (rd w.1).1 = S.cut Rs (S.msgs w.2.1) ∧ (rd w.1).2 = x.1.1) →
    (∀ x y w, (⟨W0, t₁, q⟩ : JV N (Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).src.J).rel
        x y w →
      t₃ w.1 (f (splitNx S St₁ St₂ St₀ x (splitVal k sl₁ (S.msgs w.2.1) x.1.1.2.1)).1, x.2)
        ((sideG S (ExtMap.id E₀)).map y) w.2) →
    c₀.FreshForV
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).k0
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).kj
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).M0
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).put0
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).Mj
      (((Front.splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).mask.tagPub xp₀).sharedV rd N).putj →
    (Front.onV G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f N W0 t₁ q rd t₃).OkFromV c₀

end
end Spec
end Cb
