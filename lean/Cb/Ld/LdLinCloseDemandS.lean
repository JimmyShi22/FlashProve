-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandS.lean: one closing of the test for linear constraints (a proximity test with
claims on the encoded index), that of the plan with two splittings (Cb/Ld/LdLinClosePlanS.lean):
four whole tests on groups of oracle messages, one after the other; how many positions of each
oracle message they need in all; and a statement, with a long list of hypotheses, that test and
closing together are a reduction to the trivial statement (a tail).

Definitions, statements (in `Cb.Spec`) and proofs. It uses Cb/Ld/LdLinClosePlanS.lean (the plan:
stage, front, base joint), Cb/Ld/LdLinCloseDemand.lean (positions of tests in a row add up),
Cb/Ld/LdLinCloseSplit.lean (the closing with a front behind the test's core).
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. `Spec.ldLinPsT_tail` concludes `TailTr`.
"Fresh": `FreshFor`, Ior/KnowCollRulesChain.lean.

Main names:
  `LdLinPsT p`: for each of the four groups the zero-evader, the whole test, the bound on the list,
    the number of positions; the closing Q' of what is left. `T.D₁` .. `T.D₄`; `T.Q`; `T.front`.
  `Spec.ldLinPsT_ok`: `T.Q.OK` from the four tests' own hypotheses and `Q'.OK`.
  `Spec.ldLinPsT_demand`: under the hypotheses of its statement, the demand of `T.Q` is within what
    the three sendings bear (`q5`), if T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) is at most
    ba on what the preamble left, and at most the senders' numbers.
  `Spec.ldLinPsT_plain`: in plain numbers: that bound, at an oracle message o, is at most t₁ + t₂ +
    t₃ + t₄ + c, if b' is at most c at o, where o is still kept after the four tests (each tᵢ counts
    only if the oracle message is a member of the i-th group: the bound itself says so).
  `Spec.ldLinPsT_tail`: the test with this closing is a tail, from the claim on the encoded index to
    the trivial statement. Hypotheses:
    ι, the set of positions of the encoded index, is nonempty;
    the core's (`C.P.FoldErr on0 εf`, `Function.Injective C.P.D.py`, `Sn.OK`);
    "restG is rest" (`p.restG` on the message of `p.GcW` equals `C.rest`);
    `p.Plain`, `p.Kept`, κ° ≠ κ_c;
    Q' says Ab (`p.SaysA T.Q'.base T.fa`);
    the tests' own (`T.D₁.OK` to `T.D₄.OK`) and `Q'.OK`;
    the two premises on `Q'.q` and qa and the inequalities of `Spec.ldLinPsT_demand`;
    Rs₀, Rs₁ within Rd;
    and the two facts "κ° is fresh", "κ_c is fresh" after the core and the step
      (Cb/Ld/LdLinCloseSplit.lean gives them, for entries of members of the families sent with Ω,
      G_u or W, from conditions on the senders, on Rd and on Rr).

Notation: κ°: `p.k₀`; κ_c: `p.k₁` (Cb/Ld/LdLinClosePlanS.lean); `hc₁` to `hc₄`: every oracle message
is a member of the i-th group or kept (`p.kp₁` to `p.kp₄`); `fa`: a map from `C.Sta` to the states
of Q'; `d₁` to `d₄`: for the i-th test a witness over its signature with a further witness; `d₁'` to
`d₄'`: a value of `LdBrW` (Cb/Ld/LdBatSig.lean).

Limits: this file says nothing on the batch. It does not say that senders with fresh κ°, κ_c exist.
The plan with two splittings is not the technical report's (head of Cb/Ld/LdLinClosePlanS.lean);
the report's: Cb/Ld/LdLinClosePlanP.lean, Cb/Ld/LdLinCloseDemandP.lean.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
/- Limits: no instance that meets the hypotheses of `ldLinPsT_tail` is part of this library; as far
   as the library shows, this theorem may hold of nothing. -/
import Cb.Ld.LdLinClosePlanSProofs
import Cb.Ld.LdLinCloseSplitProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The four tests: the data. -/
structure LdLinPsT {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
    {C : LdLinC E ι κ J Y} (p : LdLinPs C) where
  [ne₁ : Nonempty p.GU.P]
  hc₁ : ∀ o, p.GU.mem o ∨ p.kp₁ o
  Z₁  : Evader E (p.GU.Row (C.Brc ⊕ Unit))
  T₁  : LdEnd (p.GU.joint (fun _ => C.Sh6) p.r₁ Z₁)
  L₁  : ℕ
  t₁  : ℕ
  [ne₂ : Nonempty p.G₂.P]
  hc₂ : ∀ o, p.G₂.mem o ∨ p.kp₂ o
  Z₂  : Evader E (p.G₂.Row Unit)
  T₂  : LdEnd (p.G₂.joint (fun _ => C.Sh6) p.r₂ Z₂)
  L₂  : ℕ
  t₂  : ℕ
  [ne₃ : Nonempty p.G₃.P]
  hc₃ : ∀ o, p.G₃.mem o ∨ p.kp₃ o
  Z₃  : Evader E (p.G₃.Row Unit)
  T₃  : LdEnd (p.G₃.joint (fun _ => C.St6) p.r₃ Z₃)
  L₃  : ℕ
  t₃  : ℕ
  [ne₄ : Nonempty p.G₄.P]
  hc₄ : ∀ o, p.G₄.mem o ∨ p.kp₄ o
  Z₄  : Evader E (p.G₄.Row LinB₂)
  T₄  : LdEnd (p.G₄.joint (fun _ => C.St6) p.r₄ Z₄)
  L₄  : ℕ
  t₄  : ℕ
  Q'  : LdTc p.S₄ C.E₀ C.Wpa
  fa  : C.Sta → Q'.St
  d₁  : C.S.Wit × C.Wpa
  d₁' : LdBrW p.GU p.kp₁ C.Wpa
  d₂  : p.S₁.Wit × C.Wpa
  d₂' : LdBrW p.G₂ p.kp₂ C.Wpa
  d₃  : p.S₂.Wit × C.Wpa
  d₃' : LdBrW p.G₃ p.kp₃ C.Wpa
  d₄  : p.S₃.Wit × C.Wpa
  d₄' : LdBrW p.G₄ p.kp₄ C.Wpa

namespace LdLinPsT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPs C} (T : LdLinPsT p)

@[reducible] def D₁ : LdRunD C.S :=
  { G := p.GU, neP := T.ne₁, kp := p.kp₁, hc := T.hc₁, B := C.Brc ⊕ Unit, Sb := fun _ => C.Sh6,
    sl := p.r₁, Z := T.Z₁, T := T.T₁, L := T.L₁, t := T.t₁ }
@[reducible] def D₂ : LdRunD p.S₁ :=
  { G := p.G₂, neP := T.ne₂, kp := p.kp₂, hc := T.hc₂, B := Unit, Sb := fun _ => C.Sh6, sl := p.r₂,
    Z := T.Z₂, T := T.T₂, L := T.L₂, t := T.t₂ }
@[reducible] def D₃ : LdRunD p.S₂ :=
  { G := p.G₃, neP := T.ne₃, kp := p.kp₃, hc := T.hc₃, B := Unit, Sb := fun _ => C.St6, sl := p.r₃,
    Z := T.Z₃, T := T.T₃, L := T.L₃, t := T.t₃ }
@[reducible] def D₄ : LdRunD p.S₃ :=
  { G := p.G₄, neP := T.ne₄, kp := p.kp₄, hc := T.hc₄, B := LinB₂, Sb := fun _ => C.St6, sl := p.r₄,
    Z := T.Z₄, T := T.T₄, L := T.L₄, t := T.t₄ }

/-- The four tests, then the closing of what is left. -/
def Q : LdTc C.S C.E₀ C.Wpa :=
  LdTc.cons T.D₁
    (LdTc.cons T.D₂ (LdTc.cons T.D₃ (LdTc.cons T.D₄ T.Q' T.d₄ T.d₄') T.d₃ T.d₃') T.d₂ T.d₂')
    T.d₁ T.d₁'

/-- the front of the plan, down to the first joint of the tests -/
def front : Front p.x ⟨T.Q.St, T.Q.base⟩ := p.front T.Q'.base T.fa

end LdLinPsT

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinPsT_ok : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p),
    T.D₁.OK → T.D₂.OK → T.D₃.OK → T.D₄.OK → T.Q'.OK → T.Q.OK

open Classical in
def ldLinPsT_demand : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₄.O → ℕ),
    (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    ∀ V, T.Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)

def ldLinPsT_plain : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p) (b' : p.S₄.O → ℕ) (o : C.S.O) (c : ℕ),
    (∀ a : p.S₄.O, a.1.1.1.1 = o → b' a ≤ c) →
    T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) o ≤ T.t₁ + (T.t₂ + (T.t₃ + (T.t₄ + c)))

/-- For a nonempty ι and under the hypotheses below: the test with the closing of the plan with two
splittings is a tail. -/
def ldLinPsT_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ)
      (b' : p.S₄.O → ℕ) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.GcW.msg m) = C.rest sa (C.aM m)) → p.Plain → p.Kept →
    (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) ≠ ⟨p.k₁.o, p.k₁.j⟩ → p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK →
    T.D₃.OK → T.D₄.OK → T.Q'.OK → (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    (∀ n, p.Rs₀ n → Rd n) → (∀ n, p.Rs₁ n → Rd n) →
    ((C.P.chain on0 Sn εf).append (C.chain C.fqS p.x.A)).FreshFor
      (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    ((C.P.chain on0 Sn εf).append (C.chain C.fqS p.x.A)).FreshFor
      (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).kc E
      (p.x.stage.wideFact Rd Rr (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).put →
    TailTr (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).R
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).ext
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).P (C.P.q0 qa)

end
end Spec

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPsT_ok : Spec.ldLinPsT_ok E ι κ J Y := fun C p T h₁ h₂ h₃ h₄ hQ =>
  ldChain_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' h₁
    (ldChain_cons E p.S₁ C.E₀ C.Wpa T.D₂ _ T.d₂ T.d₂' h₂
      (ldChain_cons E p.S₂ C.E₀ C.Wpa T.D₃ _ T.d₃ T.d₃' h₃
        (ldChain_cons E p.S₃ C.E₀ C.Wpa T.D₄ T.Q' T.d₄ T.d₄' h₄ hQ)))

omit [Fintype ι] [Nonempty ι] in
open Classical in
theorem ldLinPsT_demand : Spec.ldLinPsT_demand E ι κ J Y := by
  intro C p T Sn qa q₀ ba b' hQ hqa hA hW hU hO V hV
  exact ldDemand_lin E ι κ J Y C Sn qa q₀ ba _ hqa hA hW hU hO V
    (ldDemand_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' q₀ _
      (ldDemand_cons E p.S₁ C.E₀ C.Wpa T.D₂ _ T.d₂ T.d₂' q₀ _
        (ldDemand_cons E p.S₂ C.E₀ C.Wpa T.D₃ _ T.d₃ T.d₃' q₀ _
          (ldDemand_cons E p.S₃ C.E₀ C.Wpa T.D₄ T.Q' T.d₄ T.d₄' q₀ b' hQ)))
      V hV)

/-- One more test: the bound grows by at most D.t: if b' is at most c at o where o is kept (`h`),
`D.need b'` is at most D.t + c at o. -/
theorem LdRunD.need_le_of {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S)
    (b' : (S.sub D.kp).O → ℕ) (o : S.O) (c : ℕ) (h : ∀ hk : D.kp o, b' ⟨o, hk⟩ ≤ c) :
    D.need b' o ≤ D.t + c := by
  refine (ldDemand_le E S D b' o).trans (Nat.add_le_add_left ?_ _)
  by_cases hk : D.kp o
  · rw [dif_pos hk]
    exact h hk
  · rw [dif_neg hk]
    exact Nat.zero_le _

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPsT_plain : Spec.ldLinPsT_plain E ι κ J Y := fun _ _ T b' o c hc =>
  T.D₁.need_le_of _ o _ fun h₁ =>
    T.D₂.need_le_of _ ⟨o, h₁⟩ _ fun h₂ =>
      T.D₃.need_le_of _ ⟨⟨o, h₁⟩, h₂⟩ _ fun h₃ =>
        T.D₄.need_le_of b' ⟨⟨⟨o, h₁⟩, h₂⟩, h₃⟩ c fun h₄ => hc ⟨⟨⟨⟨o, h₁⟩, h₂⟩, h₃⟩, h₄⟩ rfl

theorem ldLinPsT_tail : Spec.ldLinPsT_tail E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd Rr hF hpy hS hr hP hK hne hA h₁ h₂ h₃ h₄ hQ' hq
    hqa i1 i2 i3 i4 r0 r1 f0 f1
  exact ldLinSp_tail E ι κ J Y C on0 εf Sn qa d p.x T.Q C.fqS T.front Rd Rr hF hpy hS
    (ldLinPs_says E ι κ J Y C p hr) (ldLinPsT_ok E ι κ J Y C p T h₁ h₂ h₃ h₄ hQ')
    (ldLinPsT_demand E ι κ J Y C p T Sn qa q₀ ba b' hq hqa i1 i2 i3 i4)
    (ldLinPs_hyp E ι κ J Y C p _ T.Q'.base T.fa hP hK hA)
    (ldLinPs_sd E ι κ J Y C p _ T.Q'.base T.fa T.Q.q)
    (ldLinPs_zk E ι κ J Y C p _ T.Q'.base T.fa Rd Rr _ hP hne r0 r1 f0 f1)

end
end Cb
