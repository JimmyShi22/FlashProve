-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinBHonTop.lean: the test for linear constraints on the encoded index for at most N
instances, whole: under the hypotheses of `Spec.ldLinT_all`, one term with knowledge soundness for
the instances of a batch, the honest side of a batch, and the format items.

Definitions, statements (in `Iop.Spec` and `Cb.Spec`) and proofs. The closing is a parameter: a
chain of links with annotations, batch errors and the honest side of a batch (`ChainV`,
Cb/Ld/LdLinChainV.lean) from the joint after ζ to the trivial statement.

Main names:
Generic:
  `c.OkFromV c₀`: c stands behind c₀ (the analogue for batches of `OkFrom`, Ior/KnowCollPiece.lean):
    every link of c is a piece (`LinkV.PV`, Cb/Ld/LdLinChainV.lean), or it is a masked link
    (Cb/Ld/LdLinChainVMask.lean: `PM`) whose masks are fresh, for sets of slots, after all that
    comes before it, c₀ included.
  `c.pWh`: the sum over the links of the probabilities of their (public) withheld sets.
    `Spec.chainV_wh`: the withheld set of the chain as one link has at most this probability.
    `Spec.chainV_wh_append`: they add.
The test (in all statements ι, the set of positions of the encoded index, is nonempty):
  `P.linCV`: the test, whole. `Spec.ldLinT_same`: one term: `P.linCA` (at `cZ.forget`) and `P.linC`
    (at `cZ.forget.forget`) are its link with annotation and its link, so that what is proved of
    these two holds of one term.
  `Spec.ldLinT_wh`: the core withholds nothing: the withheld set of the whole has at most the
    closing's probability.
  `Spec.ldLinT_all`: under `P.FoldErr on0 εf`, an injective `P.D.py`, `S.OK`, `S.Apart` and a value
    of `P.Ea.Str`: all items, of the one term, for a closing chain cZ such that
    (one instance) `cZ.forget.forget` stands behind the core and has the budgets' half (`OkFrom`,
      Ior/KnowCollPiece.lean; `SidesCT`, Cb/Ld/LdTowerKitChain.lean: as in `Spec.ldLinC_tail`,
      Cb/Ld/LdLinChain.lean);
    (batch, sound) `cZ.forget` has `KB` from the key after ζ (Cb/Ld/LdLinChainB.lean);
    (batch, honest) cZ stands behind the core (`OkFromV`: each link a piece, or a masked link whose
      masks are fresh after all before it, the core included), its annotations are coherent, its
      last demand (`JV.q`) holds of the empty family.
  The items:
    strings (`IsPoint`);
    local;
    the annotation is coherent;
    the verifier reads all that is tied to its positions;
    the positions read in the encoded index are a function of the shared verifier messages, and at
      most t;
    `KnowB` for the vectors that share the encoded index and its record, on the statements with the
      condition `(P.j0 on0).on`;
    complete for each slot;
    exactly honest-verifier zero knowledge for sets of slots at no further reads
      (`HonestV.ExactV`, Ior/LinkV.lean);
    the probability of the withheld set.
  So closings with splittings whose masks ride in the core are reached, for one instance and for
    sets of slots. That these masks are fresh after the core is part of the two hypotheses "behind"
    (`OkFrom`, `OkFromV`).

By type, not among the clauses: the shared part's messages are functions of what it holds (at the
start: the encoded index as sent, its full messages and its record: `Sh0`), the shared verifier
messages and coins of its own (Ior/LinkV.lean: `HonestV.strat0`; for the core:
Cb/Ld/LdLinBHon.lean's `sU0`, `sO0`).

Limits: No closing is given (none in this file; closing chains with the honest side of a batch:
`LdLinC.cZV`, Cb/Ld/LdLinCloseVPlan.lean, over plans (`LdTcA`, `LdTcV`) that are parameters).
Running times of verifier, prover and extractor, and the prover's randomness by kind, are not
modelled.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinBHonProofs
import Cb.Ld.LdLinChainVMask
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR

/-- c stands behind c₀, for sets of slots. -/
def ChainV.OkFromV {K : Type} {N : ℕ} :
    {Z A B : Joint K} → {VZ : JV N Z} → {VA : JV N A} → {VB : JV N B} →
    ChainV K N VA VB → ChainV K N VZ VA → Prop
  | _, _, _, _, _, _, .one v, c₀ =>
    v.PV ∨ ∃ D : MaskDataV v.a.l.R _ _ N, v.PM D ∧ c₀.FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj
  | _, _, _, _, _, _, .snoc c v, c₀ =>
    OkFromV c c₀ ∧
    (v.PV ∨ ∃ D : MaskDataV v.a.l.R _ _ N,
        v.PM D ∧ (c₀.append c).FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj)

theorem ChainV.okFromV_one {K : Type} {N : ℕ} {Z A B : Joint K} {VZ : JV N Z} {VA : JV N A}
    {VB : JV N B} (c₀ : ChainV K N VZ VA) (v : LinkV K N VA VB) :
    (ChainV.one v).OkFromV c₀ ↔
    (v.PV ∨ ∃ D : MaskDataV v.a.l.R _ _ N,
        v.PM D ∧ c₀.FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj) := by
  rw [ChainV.OkFromV]
theorem ChainV.okFromV_snoc {K : Type} {N : ℕ} {Z A B C : Joint K} {VZ : JV N Z}
    {VA : JV N A} {VB : JV N B} {VC : JV N C} (c₀ : ChainV K N VZ VA)
    (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).OkFromV c₀ ↔
    c.OkFromV c₀ ∧
    (v.PV ∨ ∃ D : MaskDataV v.a.l.R _ _ N,
        v.PM D ∧ (c₀.append c).FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj) := by
  rw [ChainV.OkFromV]

/-- the sum of the probabilities of the links' withheld sets -/
def ChainV.pWh {K : Type} {N : ℕ} :
    {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → ℝ≥0∞
  | _, _, _, _, .one v => prRho v.hv.withheld
  | _, _, _, _, .snoc c v => c.pWh + prRho v.hv.withheld

theorem ChainV.pWh_one {K : Type} {N : ℕ} {A B : Joint K} {VA : JV N A}
    {VB : JV N B} (v : LinkV K N VA VB) :
    (ChainV.one v).pWh = prRho v.hv.withheld := by rw [ChainV.pWh]
theorem ChainV.pWh_snoc {K : Type} {N : ℕ} {A B C : Joint K} {VA : JV N A} {VB : JV N B}
    {VC : JV N C} (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).pWh = c.pWh + prRho v.hv.withheld := by rw [ChainV.pWh]

end IOR

namespace Spec
open IOR

/-- Two chains in a row are of the two kinds (`OkV`, Cb/Ld/LdLinChainVMask.lean) if and only if the
first is, and the second is behind the first. -/
def chainV_ok_append : Prop :=
  ∀ (K : Type) (N : ℕ) (Z A B : Joint K) (VZ : JV N Z) (VA : JV N A) (VB : JV N B)
      (c₀ : ChainV K N VZ VA) (c : ChainV K N VA VB),
    (c₀.append c).OkV ↔ c₀.OkV ∧ c.OkFromV c₀

def chainV_okFrom_of_all : Prop :=
  ∀ (K : Type) (N : ℕ) (Z A B : Joint K) (VZ : JV N Z) (VA : JV N A) (VB : JV N B)
      (c₀ : ChainV K N VZ VA) (c : ChainV K N VA VB),
    c.AllPV → c.OkFromV c₀

def chainV_wh : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    prRho (c.linkV d).hv.withheld ≤ c.pWh

def chainV_wh_append : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (c : ChainV K N VA VB) (c' : ChainV K N VB VC),
    (c.append c').pWh = c.pWh + c'.pWh

end Spec

open IOR

theorem chainV_ok_append : Spec.chainV_ok_append := by
  intro K N Z A B VZ VA VB c₀ c
  induction c with
  | one v => rw [ChainV.append_one, ChainV.okV_snoc, ChainV.okFromV_one]
  | snoc c v ih => rw [ChainV.append_snoc, ChainV.okV_snoc, ChainV.okFromV_snoc, ih, and_assoc]

theorem chainV_okFrom_of_all : Spec.chainV_okFrom_of_all := by
  intro K N Z A B VZ VA VB c₀ c
  induction c with
  | one v => exact fun h => (ChainV.okFromV_one c₀ v).2 (Or.inl ((ChainV.allPV_one v).1 h))
  | snoc c v ih =>
    exact fun h =>
      (ChainV.okFromV_snoc c₀ c v).2
        ⟨ih c₀ ((ChainV.allPV_snoc c v).1 h).1, Or.inl ((ChainV.allPV_snoc c v).1 h).2⟩

theorem chainV_wh : Spec.chainV_wh := by
  intro K N A B VA VB c d
  induction c with
  | one v => rw [ChainV.linkV_one, ChainV.pWh_one]
  | snoc c v ih =>
      rw [ChainV.linkV_snoc, ChainV.pWh_snoc]
      have e : ((c.linkV d).seq v d).hv.withheld =
          Rho.cylFst v.a.l.R.shape (c.linkV d).hv.withheld ∪
            Rho.cylSnd (c.linkV d).a.l.R.shape v.hv.withheld :=
        Set.ext fun ρ => LinkVSeq.mem_withheld (c.linkV d).hv v.hv ρ
      rw [e]
      refine (pr_union_le _ _ _).trans (add_le_add ?_ (le_of_eq (prRho_cylSnd _ _)))
      exact (le_of_eq (prRho_cylFst _ _)).trans ih

theorem chainV_wh_append : Spec.chainV_wh_append := by
  intro K N A B C VA VB VC c c'
  induction c' with
  | one v => rw [ChainV.append_one, ChainV.pWh_snoc, ChainV.pWh_one]
  | snoc c' v ih => rw [ChainV.append_snoc, ChainV.pWh_snoc, ChainV.pWh_snoc, ih, add_assoc]

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- The test for at most N instances, whole. -/
def LdLinP.linCV {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
    [Fintype κ] [Fintype J] [Fintype Y] (P : LdLinP E ι κ J Y) (S : P.Snd)
    (qa : Finset P.Ea.Pos → Prop) (N : ℕ) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ)
    {VT : JV N LdLinP.JT} (cZ : ChainV Unit N (P.V6 S qa N) VT) (d : P.W0) :
    LinkV Unit N (P.V0 qa N on0) VT :=
  ((P.chainV S qa N on0 εf).append cZ).linkV d

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- One term: its link with annotation is `P.linCA` at `cZ.forget`, and its link `P.linC` at
`cZ.forget.forget`. -/
def ldLinT_same : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ)
      (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (P.V6 S qa N) VT) (d : P.W0),
    (P.linCV S qa N on0 εf cZ d).a = P.linCA on0 S εf N cZ.forget d ∧
    (P.linCV S qa N on0 εf cZ d).a.l = P.linC on0 S εf cZ.forget.forget d

/-- The core withholds nothing: the withheld set of the whole has at most the closing's
probability. -/
def ldLinT_wh : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ)
      (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (P.V6 S qa N) VT) (d : P.W0),
    prRho (P.linCV S qa N on0 εf cZ d).hv.withheld ≤ cZ.pWh

open Classical in
/-- All items, of the one term: ten clauses on `P.linCV S qa N on0 εf cZ d`, for a nonempty ι, under
four hypotheses on the test, a value of `P.Ea.Str`, and six hypotheses on the closing chain cZ; the
head's row of `Spec.ldLinT_all` tells them in the statement's order. (not all hypotheses are named
here: see the statement below) -/
def ldLinT_all : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (_ : P.Ea.Str) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (P.V6 S qa N) VT) (kT : JKey LdLinP.JT) (d : P.W0),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK → S.Apart →
    cZ.forget.forget.OkFrom (P.chain on0 S εf) →
    cZ.forget.forget.SidesCT (P.q5 S qa) → cZ.forget.KB N P.key6 kT →
    cZ.OkFromV (P.chainV S qa N on0 εf) → cZ.forget.Coh → (∀ Jn, VT.q Jn fun _ => ∅) →
    Nonempty (P.linCV S qa N on0 εf cZ d).a.l.R.shape.IsPoint ∧
    (P.linCV S qa N on0 εf cZ d).a.l.R.IsLocal ∧
    (P.linCV S qa N on0 εf cZ d).a.ann.Coherent ∧
    (P.linCV S qa N on0 εf cZ d).a.l.R.Tied ∧
    (∀ ρ ρ', Rho.sh (P.linCV S qa N on0 εf cZ d).a.ann ρ =
        Rho.sh (P.linCV S qa N on0 εf cZ d).a.ann ρ' →
      (((P.linCV S qa N on0 εf cZ d).a.l.R.extReads ρ : Finset P.E0.Pos)).filter
          (fun p => p.isLeft) =
        (((P.linCV S qa N on0 εf cZ d).a.l.R.extReads ρ' : Finset P.E0.Pos)).filter
          (fun p => p.isLeft)) ∧
    (∀ ρ, ((((P.linCV S qa N on0 εf cZ d).a.l.R.extReads ρ : Finset P.E0.Pos)).filter
        (fun p => p.isLeft)).card ≤ P.t) ∧
    (P.linCV S qa N on0 εf cZ d).a.l.R.KnowB (P.linCV S qa N on0 εf cZ d).a.ann N (SameKey P.k0)
      (P.j0 on0).on (P.j0 on0).relR (fun _ (_ : Unit) => True)
      (P.linCV S qa N on0 εf cZ d).a.l.ext (P.linCV S qa N on0 εf cZ d).a.err ∧
    (P.linCV S qa N on0 εf cZ d).hv.AccV (P.V0 qa N on0).rel VT.rel ∧
    (P.linCV S qa N on0 εf cZ d).hv.ExactV N (P.V0 qa N on0).rel (fun _ _ Ts => ∀ j, Ts j = ∅) ∧
    prRho (P.linCV S qa N on0 εf cZ d).hv.withheld ≤ cZ.pWh

end
end Spec

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinT_same : Spec.ldLinT_same E ι κ J Y := by
  intro P on0 εf N S qa VT cZ d
  have h1 : (P.linCV S qa N on0 εf cZ d).a = P.linCA on0 S εf N cZ.forget d := by
    unfold LdLinP.linCV LdLinP.linCA
    rw [chainV_link, chainV_forget_append, ldLinV_forget]
  exact ⟨h1, by rw [h1, ldLinCB_same]⟩

theorem ldLinT_wh : Spec.ldLinT_wh E ι κ J Y := by
  intro P on0 εf N S qa VT cZ d
  refine (chainV_wh Unit N (P.J0 on0) LdLinP.JT (P.V0 qa N on0) VT
    ((P.chainV S qa N on0 εf).append cZ) d).trans ?_
  rw [chainV_wh_append]
  have hl : ∀ {X X' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo} {Wi Wo : Type}
          (H : R.Honest Wi Wo) (W0 : Type),
        H.Bad = ∅ → prRho (H.localV W0).withheld = 0 := fun H W0 hB =>
    le_antisymm (prRho_empty _ fun ρ hρ => by
      have := (LinkV.local_withheld H W0 ρ).1 hρ
      rw [hB] at this
      exact this) (zero_le _)
  have hs : ∀ {X X' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo} {Wi Wo W0 W0' : Type}
          (H : R.Honest Wi Wo) (s0 : W0 → H.Coin → Strat R.shape W0'),
        H.Bad = ∅ → prRho (H.sharedV s0).withheld = 0 := fun H s0 hB =>
    le_antisymm (prRho_empty _ fun ρ hρ => by
      have := (LinkV.shared_withheld H s0 ρ).1 hρ
      rw [hB] at this
      exact this) (zero_le _)
  have h0 : (P.chainV S qa N on0 εf).pWh = 0 := by
    unfold LdLinP.chainV
    simp only [ChainV.pWh_snoc, ChainV.pWh_one]
    have e0 : prRho (P.lv0 qa N on0).hv.withheld = 0 := hl P.hStep0 P.Sh0 rfl
    have eW : prRho (P.lvW S qa N on0).hv.withheld = 0 :=
      hl (ldSendFamHon P.SdW P.X0 P.E0 S.dW) P.Sh0 rfl
    have eP : prRho (P.lvPt S qa N on0 εf).hv.withheld = 0 := hs P.hPt P.sPt0 rfl
    have eU : prRho (P.lvU S qa N on0).hv.withheld = 0 :=
      hs (ldSendFamHon P.SdU P.X2 P.E1 S.dU) (P.sU0 S) rfl
    have eL : prRho (P.lvLoc S qa N on0).hv.withheld = 0 := hs P.hLoc P.sLoc0 rfl
    have eO : prRho (P.lvO S qa N).hv.withheld = 0 :=
      hs (ldSendFamHon P.SdO P.X4 P.E4 S.dO) (P.sO0 S) rfl
    have eZ : prRho (P.lvZeta S qa N).hv.withheld = 0 := hs P.hZeta P.sZeta0 rfl
    rw [e0, eW, eP, eU, eL, eO, eZ]
    simp
  rw [h0, zero_add]

theorem ldLinT_all : Spec.ldLinT_all E ι κ J Y := by
  classical
  intro P on0 εf N S qa ya VT cZ kT d hF hpy hS hA hOk hSd hKB hPV hCoh hq
  obtain ⟨e1, e2⟩ := ldLinT_same P on0 εf N S qa VT cZ d
  have hT := ldLinC_tail P on0 εf S qa d cZ.forget.forget hF hpy hS hOk hSd
  rw [← e2] at hT
  have hE := chainV_ok_end Unit N _ _ _ VT ((P.chainV S qa N on0 εf).append cZ) d
    ((chainV_ok_append _ _ _ _ _ _ _ _ _ cZ).2
      ⟨okV_of_allPV _ _ _ _ _ _ _ (ldLinV_core P on0 εf N S qa ya hF hpy hS hA), hPV⟩) hq
  have hK := ldLinCB_know P on0 εf N S cZ.forget kT d hF hpy hS hKB
  have hc := ldLinD_coherent P on0 εf N S cZ.forget d hCoh
  have hsh := ldLinD_idxShared P on0 εf N S cZ.forget d hCoh
  have hrd := ldLinD_idxReads P on0 εf N S cZ.forget d hCoh
  rw [← e1] at hK hc hsh hrd
  exact ⟨hT.good.point, hT.good.isLocal, hc, hT.tied, hsh, hrd, hK, hE.2.1,
    hE.2.2.1, ldLinT_wh P on0 εf N S qa VT cZ d⟩

end
end Cb
