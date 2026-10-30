-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStart.lean: the preamble of a request as one reduction from a statement without oracle
messages.

Definitions, statements (Cb.Spec.ldReqStart_*) and proofs.
In standard terms: the interactive oracle reductions of a request's preamble, composed into one
reduction whose input statement has no oracle message yet.
The preamble of Cb/Req1/LdReq.lean (`LdReq`) leads from a stage to a stage. At the start of a
request no oracle message has been sent: the statement is (explicit part, the encoded index), of any
joint A. Here that joint is read as a stage with the empty signature, and the chain becomes one
reduction from A's own types.

Main names:
  `LdStage.start E Kc A`: the stage (no oracle message; A claimed of the further witness).
  `r.F w₀`, `r.FH w₀`, `r.Fext w₀`, `r.FP w₀`: reduction, honest side, extractor, numbers: the chain
    as one link after a step without rounds that adds the empty families. (w₀: the extractor's value
    where an earlier verifier rejects.)
  `Spec.ldReqStart_goodT`: from r.Hyp and r.Zk: the whole bundle `IOR.GoodT` from A (on A's own
    statements) to the last stage's joint (collision-free may fail there).
  `Spec.ldReqStart_goodB`: the bundle without its clause on zero knowledge, from r.Hyp.
  `Spec.ldReqStart_fmt`: under `r.Hyp` and the premise on `qa` of its statement: the formats
    (`JFmt`), if every link has its format (Cb/Req1/LdReqFormat.lean: `r.chain.Fmt φ ψ`) and the
    index is the left part at both ends: the index is not read, nothing is tied to it, it is copied
    (`IdxPrefix` of Cb/Ld/LdWfPre.lean); the record is handed on; the honest prover hands its prover
    encoded index on (`Honest.Hands`, Cb/Ld/LdWfPre.lean: on inputs in the relation, at verifier
    messages that are not withheld); the reduction bears what follows (`IOR.Bears`, Ior/Bears.lean).
  `Spec.ldReqStart_nums`: shape and the two numbers `pBad`, `pHid` (of `IOR.Nums`, Ior/Chain.lean)
    are those of the chain.

Limits: this file says nothing on the step to the parameter list of a preamble of the holographic
protocol. It does not say that every link has a format.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqProofs
import Cb.Req1.LdReqFormat
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc Xi Wi : Type} {E0 : ExtSpec}

/-- the one family over no oracle message -/
def Sig.nilFam (E : Type) {T : OMsg E → Type} : ∀ a, T ((Sig.nil E).om a) := fun a => a.elim

/-- A joint without oracle messages, as a stage. -/
@[reducible] def LdStage.start (E Kc : Type) (A : Rels Kc Xi E0 Wi) : LdStage E Kc :=
  ⟨Sig.nil E, Xi, E0, Wi,
    ⟨fun x y w => A.rel x y w.2, fun a w => A.relR a w.2, A.on, fun w => A.core w.2⟩⟩

/-- the step without rounds: the empty families are added -/
def ldStartX (E : Type) (x : Xi) : Xi × (Sig.nil E).Smp := (x, Sig.nilFam E)
def ldStartE (E : Type) (E0 : ExtSpec) : ExtMap E0 (E0.prod (Sig.nil E).ext) :=
  (ExtMap.id E0).pair ⟨fun _ => Sig.nilFam E, fun q => q.1.elim⟩
def ldStartW (E : Type) (w : Wi) : (Sig.nil E).Wit × Wi := (Sig.nilFam E, w)

variable [Field E] [Fintype E] {A : Rels Kc Xi E0 Wi} {z : LdStage E Kc}

namespace LdReq
variable (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi)

def F : IOR Xi E0 z.X z.Ex :=
  (r.chain.link (ldStartW E w₀)).R.pre (fun x => some (ldStartX E x)) (ldStartE E E0)
def FH : (r.F w₀).Honest Wi z.W :=
  (r.chain.link (ldStartW E w₀)).H.pre (fun x => some (ldStartX E x)) (ldStartE E E0)
    fun p => (ldStartX E p.1, ldStartW E p.2)
def Fext : Xi × E0.Str → Tr (r.F w₀).shape → z.W → Wi := fun a τ w =>
  ((r.chain.link (ldStartW E w₀)).ext (ldStartX E a.1, (ldStartE E E0).map a.2) τ w).2
def FP : Nums Kc (r.F w₀) :=
  (r.chain.link (ldStartW E w₀)).P.pre (fun x => some (ldStartX E x)) (ldStartE E E0)

end LdReq
end

namespace Spec

def ldReqStart_goodB : Prop :=
  ∀ (E Kc Xi Wi : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi),
    r.Hyp → GoodB (r.F w₀) (r.FH w₀) A z.J.rels (r.Fext w₀) (r.FP w₀)

/-- Under `r.Hyp` and `r.Zk`: the preamble of a request, as one reduction, has the whole bundle. -/
def ldReqStart_goodT : Prop :=
  ∀ (E Kc Xi Wi : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi),
    r.Hyp → r.Zk → GoodT (r.F w₀) (r.FH w₀) A z.J.rels (r.Fext w₀) (r.FP w₀)

open Classical in
/-- The formats. -/
def ldReqStart_fmt : Prop :=
  ∀ (E Kc Xi Wi Rc Pw : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (S : Sig E) (St Wp : Type) (B : Rels Kc St E0 (S.Msg × Wp))
      (r : LdReq (LdStage.start E Kc A) ⟨S, St, E0, Wp, B⟩) (w₀ : Wi)
      (φ : JFmt Kc E0 Rc Pw (LdStage.start E Kc A).J)
      (ψ : JFmt Kc E0 Rc Pw (⟨S, St, E0, Wp, B⟩ : LdStage E Kc).J) (qa : Finset E0.Pos → Prop),
    r.Hyp → r.chain.Fmt φ ψ → φ.ix = IxAt.left E0 (Sig.nil E).ext → ψ.ix = IxAt.left E0 S.ext →
    (∀ U, φ.q U → qa (U.biUnion (ldStartE E E0).src)) →
    (r.F w₀).IdxPrefix ∧
    (r.F w₀).Passes (fun x => φ.rc (ldStartX E x)) ψ.rc ∧
    (r.FH w₀).Hands A.rel (fun w => φ.px (ldStartW E w)) ψ.px ∧
    (r.F w₀).Bears (r.FP w₀).bud qa ψ.q

def ldReqStart_nums : Prop :=
  ∀ (E Kc Xi Wi : Type) (E0 : ExtSpec) [Field E] [Fintype E] (A : Rels Kc Xi E0 Wi)
      (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi),
    (r.F w₀).shape = (r.chain.link (ldStartW E w₀)).R.shape ∧
    (r.FP w₀).pBad = (r.chain.link (ldStartW E w₀)).P.pBad ∧
    (r.FP w₀).pHid = (r.chain.link (ldStartW E w₀)).P.pHid

end Spec

section
variable {E Kc Xi Wi : Type} {E0 : ExtSpec}

theorem ldStartE_isLocal : (ldStartE E E0).IsLocal := by
  obtain ⟨hid, -, -, -, hpair⟩ := extMap_isLocal
  exact hpair _ _ _ _ _ (hid _) (fun _ _ q _ => q.1.elim)

variable [Field E] (A : Rels Kc Xi E0 Wi)

theorem ldStartStep :
    StepT (fun x : Xi => some (ldStartX E x)) (ldStartE E E0)
      (fun p : Xi × Wi => (ldStartX E p.1, ldStartW E p.2)) (fun _ w => w.2)
      A (LdStage.start E Kc A).J.rels where
  isLocal := ldStartE_isLocal
  acc := fun _ _ _ h => ⟨rfl, fun a => a.elim, fun a => a.elim, h⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' ha hx hw
    cases hx
    rcases hw with hw | hn
    · exact hw.2
    · exact absurd ⟨fun a => a.elim, ha⟩ hn

end

/-- after the step that adds the empty families, a reduction that leaves the left part alone is a
prefix -/
theorem idxPrefix_start {E Xi X₁ X₂ : Type} {E0 Ea : ExtSpec}
    (R : IOR X₁ (E0.prod (Sig.nil E).ext) X₂ (E0.prod Ea)) (f : Xi → Option X₁)
    (h : R.IdxLink (IxAt.left E0 (Sig.nil E).ext) (IxAt.left E0 Ea)) :
    (R.pre f (ldStartE E E0)).IdxPrefix := by
  classical
  refine ⟨fun ρ => Finset.eq_empty_of_forall_notMem fun p hp => ?_,
    fun ρ p => Finset.eq_empty_of_forall_notMem fun u hu => ?_,
    fun y τ => h.copy _ τ,
    fun ρ p => ⟨?_, (h.srcIdx ρ p).2⟩,
    fun ρ q => Finset.eq_empty_of_forall_notMem fun u hu => ?_⟩
  · obtain ⟨q, hq, _⟩ := Finset.mem_biUnion.1 hp
    cases q with
    | inl q => exact h.noIdx ρ q hq
    | inr q => exact q.1.elim
  · obtain ⟨q, hq, _⟩ := Finset.mem_biUnion.1 hu
    cases q with
    | inl q => exact h.noTie ρ p q hq
    | inr q => exact q.1.elim
  · show (R.srcE ρ (Sum.inl p)).biUnion (ldStartE E E0).src = {p}
    have := (h.srcIdx ρ p).1
    rw [show R.srcE ρ (Sum.inl p) = {Sum.inl p} from this, Finset.singleton_biUnion]
    rfl
  · obtain ⟨q', hq', _⟩ := Finset.mem_biUnion.1 hu
    cases q' with
    | inl q' => exact h.srcAux ρ (Sum.inr q) (fun p' hp' => by cases hp') q' hq'
    | inr q' => exact q'.1.elim

theorem ldReqStart_goodB : Spec.ldReqStart_goodB := fun E Kc Xi Wi E0 _ _ A z r w₀ h =>
  goodB_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ldStartStep A)
    (ldReq_goodB E Kc _ z r (ldStartW E w₀) h) (fun _ _ _ _ hx => by cases hx; rfl)

theorem ldReqStart_goodT : Spec.ldReqStart_goodT := fun E Kc Xi Wi E0 _ _ A z r w₀ h hz =>
  (goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2
    ⟨ldReqStart_goodB E Kc Xi Wi E0 A z r w₀ h,
      exact_pre _ _ _ _ _ _ _ _ _ _ _ _ A.rel _ _ _
        (fun p : Xi × Wi => (ldStartX E p.1, ldStartW E p.2)) ldStartE_isLocal (ldStartStep A).acc
        (ldReq_goodT E Kc _ z r (ldStartW E w₀) h hz).exact⟩

theorem ldReqStart_fmt : Spec.ldReqStart_fmt := by
  classical
  intro E Kc Xi Wi Rc Pw E0 _ _ A S St Wp B r w₀ φ ψ qa h hF hφ hψ hq
  have hB : r.chain.AllB :=
    r.last.onto_allB _
      (r.segs.onto_allB _
        (r.more.onto_allB _ ((allB_one _).2 (goodB_of_goodT' (r.first.goodT h.first))) h.more)
        h.segs) h.last
  have g := chain_fmt Kc E0 Rc Pw _ _ r.chain (ldStartW E w₀) φ ψ hB hF
  have gi := g.idx
  rw [hφ, hψ] at gi
  exact ⟨idxPrefix_start _ _ gi,
    g.pass.pre _ _ (fun _ _ hx => by cases hx; rfl),
    g.hands.pre _ _ _ (fun x y w hw => ((ldStartStep A).acc x y w hw).2) (fun _ => rfl),
    bears_pre _ _ _ _ _ _ _ _ _ _ _ _ _ g.bears hq⟩

theorem ldReqStart_nums : Spec.ldReqStart_nums := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

end Cb
