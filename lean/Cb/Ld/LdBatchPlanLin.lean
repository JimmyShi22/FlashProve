-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatchPlanLin.lean: round-by-round knowledge soundness of a proximity test with linear
claims, run on a batch of at most N instances that share one encoded index and its record, for one
way to run its last part: stated under the hypotheses that are listed under Limits.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.

The test is the test for linear constraints on the encoded index (Cb/Ld/LdLin.lean), with the plan
without a splitting. The plan is Cb/Ld/LdLinClosePlan.lean's (`p : LdLinPl C`: the rows that the
test for linear constraints leaves, as rows on two groups), its tests Cb/Ld/LdLinCloseDemand.lean's
(`T : LdLinPlT p`), unchanged. G_u, Ω and W are the oracle messages that hold u, ω and w (`C.nU`,
`C.nO`, `C.nW`, Cb/Ld/LdLinClosePre.lean). For a batch:
  the first test (the group with G_u and Ω: the record's rows, the columns at the locations, the
    fold's row) is run once, by the shared part of the prover, under shared verifier messages;
  the second test (the group with Ω, W and what the evaluation reads: evaluation, inner product) is
    run in every slot, in the slot's local rounds. Ω, a shared oracle message, is a member of it: it
    is in 1 + N tests;
  the rest are the oracle messages that are kept after both tests. What closes them (`T.Q'`, over
    `p.S₂`) is a parameter: a chain of annotated links cA' whose links are those of `T.Q'.c`. Asked
    of cA': it is knowledge sound for every vector of statements, as links in local rounds are (from
    the trivial key, `ldKeyU`: the key that says nothing: every vector of statements has one key).

In standard terms: a key (`JKey`, Cb/Ld/LdLinChainB.lean) is a function of the statement at a joint;
knowledge soundness for a batch (`KnowB`: in words in the head of Cb/Ld/LdBatchBlocks.lean) is
stated for the vectors of at most N statements on which the key is constant.

Main names:
  `T.QA cA' same'`: the plan for a batch (Cb/Ld/LdBatchBlocksPlan.lean); its plan is `T.Q` by
    definition.
  `Spec.ldRunAct_congr`: the acting part of a test reads the statement through: the rows of the
    claim (targets, states), and samples and words of the members of its group.
  `Spec.ldPlanLin_act`: if every member of the first group is a shared oracle message (`p.Shared`),
    the first test's acting part is the same for all statements with one key k6 (Cb/Ld/LdLinB.lean:
    record, shared point, G_u's and Ω's families with their samples, locations and folds read, ζ):
    the targets of the rows of its claim are 0, functions of the record and of shared verifier
    messages, or folds of symbols read at shared locations; their states are the shared part
    `C.Sh6`.
  `Spec.ldPlanLin_kb`: so, under the hypotheses of its statement, the closing is knowledge sound
    from k6.
  `Spec.ldPlanLin_know`: the whole test, under the hypotheses of its statement: `KnowB` for the
    vectors that share the encoded index and its record, on the statements with the condition of
    `C.P.j0 on0`; its term is the one-instance test's, `C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d` (of
    which `ldLinPlan_tail` of Cb/Ld/LdLinCloseDemand.lean speaks).
  `Spec.ldPlanLin_item`, `Spec.ldPlanLin_item_far`: over the one configuration (`O.Cf : LdCf F E`,
    Cb/Obj/LdObjectConf.lean; `O : LdOL F E`, Cb/Obj/LdObjectLin.lean, is the test's data over it),
    under the hypotheses of their statements: `Hiop.LinBKnowR` (Hiop/RecSubs.lean), by
    `Spec.ldOLB_item`, `Spec.ldOLB_item_far` (Cb/Ld/LdBatchBlocksObject.lean); the second regime:
    `O.onDec` for on0, 0 for εf.
    `LinBKnowR` is round-by-round knowledge soundness of the IOPP for the constraint relation, at
    most N instances that share the encoded index and its record: for each record, with that record
    in all slots, on the collision-free statements whose encoded index decodes with the record (to a
    message; it need not hold an index). One-instance errors in the rounds of an instance, joint
    errors in the shared rounds; one list for all records.
    The regimes are two choices of the condition on0, a parameter (Cb/Ld/LdLin.lean). First regime:
    no collision of the index at the record's seed. Second regime: the index decodes with its
    record.

Limits: what is still asked:
  `p.Shared`;
  "restG is rest" (`p.restG` on the second group's message equals `C.rest`);
  "`T.Q'.base` says Ab" (`p.SaysA`);
  each test's own hypotheses (`T.D₁.OK`, `T.D₂.OK`);
  whatever the arguments hold as proofs, among them: `T` (`LdLinPlT`, Cb/Ld/LdLinCloseDemand.lean):
    for each of the two groups, every oracle message of its signature (`C.S`, `p.S₁`) is a member of
    it or kept (`hc₁`, `hc₂`), and its set of positions is not empty (`ne₁`, `ne₂`); `p` (`LdLinPl`,
    Cb/Ld/LdLinClosePlan.lean): G_u and Ω are members of the first group (`hU`, `hO`), W and Ω are
    kept there (`kW`, `kO`) and are members of the second (`hW₂`, `hO₂`);
  the rest's knowledge soundness (`cA'.KB` from the trivial key; `same'`: the links of cA' are those
    of `T.Q'.c`);
  the core's hypotheses (`C.P.FoldErr on0 εf`, `Function.Injective C.P.D.py`, `Sn.OK`; ι is not
    empty, for the item `Nonempty (Fin O.Cf.C₀.n)`);
  for the item also those of Cb/Ld/LdBatchBlocksObject.lean on distance, radii and the condition
    on0.
The errors: the core's for N instances; then the first test's, paid once; then the second test's, in
local rounds; then those of cA' (a parameter, with its annotation). How to read these: the head of
Cb/Ld/LdBatchBlocksPlan.lean.
This file says nothing on plans with a splitting, and nothing on the honest side of a batch. It does
not say that the hypotheses can be met together: no tower, no code, no list bound is given here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatchBlocksObject
import Cb.Ld.LdLinCloseDemand
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the key that says nothing: every vector of statements has one key -/
def ldKeyU (Jn : Joint Unit) : JKey Jn := ⟨Unit, fun _ => ()⟩

namespace LdLinPlT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPl C} (T : LdLinPlT p)

/-- The plan for a batch: the first test once, the second in every slot, then the rest. -/
def QA (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ)
    (same' : cA'.forget = T.Q'.c) : LdTcA C.S C.E₀ C.Wpa :=
  LdTcA.consSh T.D₁ (LdTcA.consLo T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂') T.d₁ T.d₁'

end LdLinPlT

namespace Spec

/-- The acting part reads the rows of the claim, and samples and words of the members. -/
def ldRunAct_congr : Prop :=
  ∀ (E B St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) (Sb : B → Type)
      (E₀ : ExtSpec) (a a' : ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) × (E₀.prod S.ext).Str),
    a.1.1.1 = a'.1.1.1 → (∀ o, G.mem o → a.1.2 o = a'.1.2 o) → (∀ o, G.mem o → a.2.2 o = a'.2.2 o) →
    ldRunAct G Sb St₀ E₀ a = ldRunAct G Sb St₀ E₀ a'

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States, if `p.Shared`: the first test's acting part is the same for statements with one key k6.
-/
def ldPlanLin_act : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (St' : Type) (fa : C.Sta → St')
      (x x' : C.P.X6) (y y' : C.P.E5.Str),
    p.Shared → C.P.k6 (x, y) = C.P.k6 (x', y') →
    ldRunAct p.G₁ (fun _ : C.B₁ => C.Sh6) _ C.E₀ ((C.fq fa (C.toSt x), C.toSmp x), C.toE.map y) =
      ldRunAct p.G₁ (fun _ : C.B₁ => C.Sh6) _ C.E₀ ((C.fq fa (C.toSt x'), C.toSmp x'), C.toE.map y')

/-- States, under the hypotheses below: the closing is knowledge sound from k6. -/
def ldPlanLin_kb : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ),
    p.Shared →
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → cA'.KB N (ldKeyU _) ldKeyT →
    (C.cZA (T.QA cA' same') T.fq).KB N C.P.key6 ldKeyT

/-- The whole test for at most N instances. States, under the hypotheses below, its `KnowB`, and
that its term is the one-instance test's. -/
def ldPlanLin_know : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd) (d : C.P.W0),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK → p.Shared →
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → cA'.KB N (ldKeyU _) ldKeyT →
    (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') T.fq) d).l.R.KnowB
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') T.fq) d).ann N (SameKey C.P.k0) (C.P.j0 on0).on
      (C.P.j0 on0).relR (fun _ (_ : Unit) => True)
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') T.fq) d).l.ext
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') T.fq) d).err ∧
    (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') T.fq) d).l = C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d

end

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States the item of the object, `LinBKnowR` of `O.fullB` with the errors `O.errFB`, for the plan
without a splitting, under the hypotheses below. -/
def ldPlanLin_item : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ)
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (εf : ℕ) (Sn : O.toC.P.Snd)
      (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.Fits on0 → O.toC.P.FoldErr on0 εf →
    Function.Injective O.py → Sn.OK → p.Shared →
    (∀ sa m, p.restG.val sa (p.G₂.msg (O.toC.S.res (T := OMsg.Msg) p.kp₁ m)) =
      O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → cA'.KB N (ldKeyU _) ldKeyT →
    LinBKnowR O.left (O.fullB on0 Sn εf N (T.QA cA' same') T.fq d) N d0
      (O.errFB on0 Sn εf N (T.QA cA' same') T.fq d)

/-- The second regime: states the item at `O.onDec` for on0 and 0 for εf, under the hypotheses
below. -/
def ldPlanLin_item_far : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ)
      (Sn : O.toC.P.Snd) (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.e' + O.Cf.eM < O.Cf.C₀.d →
    Function.Injective O.py → Sn.OK → p.Shared →
    (∀ sa m, p.restG.val sa (p.G₂.msg (O.toC.S.res (T := OMsg.Msg) p.kp₁ m)) =
      O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → cA'.KB N (ldKeyU _) ldKeyT →
    LinBKnowR O.left (O.fullB O.onDec Sn 0 N (T.QA cA' same') T.fq d) N d0
      (O.errFB O.onDec Sn 0 N (T.QA cA' same') T.fq d)

end
end Spec

theorem ldRunAct_congr : Spec.ldRunAct_congr := by
  rintro E B St₀ _ _ _ S G Sb E₀ ⟨⟨⟨x, st⟩, σ⟩, ⟨y₀, w⟩⟩ ⟨⟨⟨x', st'⟩, σ'⟩, ⟨y₀', w'⟩⟩ hx hσ hw
  obtain rfl : x = x' := hx
  have hσ' : ∀ o, G.mem o → σ o = σ' o := hσ
  have hw' : ∀ o, G.mem o → w o = w' o := hw
  refine Prod.ext (Prod.ext (funext fun ν => ?_) (funext fun ν => ?_)) (funext fun q => ?_)
  · cases ν with
    | inl b => rfl
    | inr as =>
      show (σ as.1.1).2 as.2 = (σ' as.1.1).2 as.2
      rw [hσ' as.1.1 as.1.2]
  · cases ν with
    | inl b => rfl
    | inr as =>
      show (σ as.1.1).1 = (σ' as.1.1).1
      rw [hσ' as.1.1 as.1.2]
  · show (S.om q.1.1).upW (w q.1.1) q.2 = (S.om q.1.1).upW (w' q.1.1) q.2
    rw [hw' q.1.1 q.1.2]

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldPlanLin_act : Spec.ldPlanLin_act E ι κ J Y := by
  intro C p St' fa x x' y y' hSh hk
  have h6 : x.2 = x'.2 := congrArg (fun k => k.2) hk
  have h5 : (x.1.2, y.2) = (x'.1.2, y'.2) := congrArg (fun k => k.1.2) hk
  have h4 : x.1.1.2 = x'.1.1.2 := congrArg (fun k => k.1.1.2) hk
  have h3 : (x.1.1.1.2, y.1.2) = (x'.1.1.1.2, y'.1.2) := congrArg (fun k => k.1.1.1.2) hk
  have h2 : x.1.1.1.1.2 = x'.1.1.1.1.2 := congrArg (fun k => k.1.1.1.1.2) hk
  have h1 : x.1.1.1.1.1.1.2 = x'.1.1.1.1.1.1.2 := congrArg (fun k => k.1.1.1.1.1) hk
  have hs : C.sh (C.toSt x) = C.sh (C.toSt x') := by
    show (((x.1.1.1.1.1.1.2, x.1.1.1.1.2), x.1.1.2), x.2) =
      (((x'.1.1.1.1.1.1.2, x'.1.1.1.1.2), x'.1.1.2), x'.2)
    rw [h1, h2, h4, h6]
  refine ldRunAct_congr E C.B₁ _ C.S p.G₁ (fun _ => C.Sh6) C.E₀ _ _ ?_
    (fun o ho => ?_) (fun o ho => ?_)
  · show (C.tg₁ (C.sh (C.toSt x)), fun _ => C.sh (C.toSt x)) =
      (C.tg₁ (C.sh (C.toSt x')), fun _ => C.sh (C.toSt x'))
    rw [hs]
  · rcases hSh o ho with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact congrFun (congrArg Prod.fst h3) a
    · exact congrFun (congrArg Prod.fst h5) a
  · rcases hSh o ho with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact congrFun (congrArg Prod.snd h3) a
    · exact congrFun (congrArg Prod.snd h5) a

omit [Nonempty ι] in
theorem ldPlanLin_kb : Spec.ldPlanLin_kb E ι κ J Y := by
  intro C p T cA' same' N hSh hrest hA hD₁ hD₂ hQ'
  have hSays : C.Says (T.QA cA' same').Q.base T.fq :=
    ldLinPlan_says E ι κ J Y C p T.Q'.St T.Q'.base T.fa hrest hA
  have hT := ldLinPre_step_cf E ι κ J Y C _ _ T.fq hSays
  -- the rest, the second test, the first test
  have q2 : (LdTcA.consLo T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂').KB N (ldKeyU _) :=
    ldPlanB_cons_local E p.S₁ C.E₀ C.Wpa T.D₂ ⟨T.Q', cA', same'⟩ T.d₂ T.d₂' N (ldKeyU _) (ldKeyU _)
      (fun _ => ()) hD₂ hQ' fun _ _ _ _ => rfl
  have q1 : (T.QA cA' same').KB N ⟨_, ldRunAct p.G₁ (fun _ : C.B₁ => C.Sh6) _ C.E₀⟩ :=
    ldPlanB_cons_shared E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' N
      ⟨_, ldRunAct p.G₁ (fun _ : C.B₁ => C.Sh6) _ C.E₀⟩ (ldKeyU _) id (fun _ _ => ()) hD₁ q2
      (fun _ => rfl) fun _ _ _ _ => rfl
  -- the step without rounds in front
  refine chainA_kb_append Unit _ _ _ (ChainA.one (C.link T.fq (T.QA cA' same').Q.base).lo)
    (T.QA cA' same').cA N C.P.key6 ⟨_, ldRunAct p.G₁ (fun _ : C.B₁ => C.Sh6) _ C.E₀⟩ ldKeyT
    ((ChainA.kb_one _ N _ _).2 ⟨?_, ?_⟩) q1
  · refine knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _
      (knowB_local _ _ _ _ _ _ (C.link T.fq (T.QA cA' same').Q.base).R RAnn.allLocal (fun _ => rfl)
        N (fun _ => True) _ _ _ _ ?_)
      (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ w => w) (fun _ _ w => w)
    rintro ⟨x, y⟩ _ b w hb hw
    obtain rfl := Option.some.inj hb
    exact hT.know x y _ w trivial rfl hw
  · intro a ha τ j j' b b' hb hb'
    obtain ⟨⟨x, y⟩, haj, h2⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨⟨x', y'⟩, haj', h2'⟩ := Option.bind_eq_some_iff.mp hb'
    obtain rfl := Option.some.inj h2
    obtain rfl := Option.some.inj h2'
    exact ldPlanLin_act E ι κ J Y C p _ T.fa x x' y y' hSh (ha j j' _ _ haj haj')

theorem ldPlanLin_know :
    Spec.ldPlanLin_know E ι κ J
      Y := fun C p T cA' same' N on0 εf Sn d hF hpy hS hSh hrest hA hD₁ hD₂ hQ' =>
  ldLinB_close E ι κ J Y C on0 εf N Sn d (T.QA cA' same') T.fq hF hpy hS
    (ldPlanLin_kb E ι κ J Y C p T cA' same' N hSh hrest hA hD₁ hD₂ hQ')

end

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldPlanLin_item :
    Spec.ldPlanLin_item F
      E := fun O _ p T cA' same' N on0 εf Sn d d0 hd he hFit hF hpy hS hSh hrest hA hD₁ hD₂ hQ' =>
  ldOLB_item F E O on0 Sn εf N (T.QA cA' same') T.fq d d0 hd he hFit hF hpy hS
    (ldPlanLin_kb _ _ _ _ _ O.toC p T cA' same' N hSh hrest hA hD₁ hD₂ hQ')

theorem ldPlanLin_item_far :
    Spec.ldPlanLin_item_far F
      E := fun O _ p T cA' same' N Sn d d0 hd he hpy hS hSh hrest hA hD₁ hD₂ hQ' =>
  ldOLB_item_far F E O Sn N (T.QA cA' same') T.fq d d0 hd he hpy hS
    (ldPlanLin_kb _ _ _ _ _ O.toC p T cA' same' N hSh hrest hA hD₁ hD₂ hQ')

end
end Cb
