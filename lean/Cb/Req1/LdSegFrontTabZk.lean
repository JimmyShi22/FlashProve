-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontTabZk.lean: what zero knowledge asks of the front (`B.prog.Zk base`), beside its
hypotheses (`B.prog.Hyp`), from conditions on places.
(not all hypotheses are named here: see `Spec.ldSegTabZk`)

Definitions, statements (in `Cb.Spec`) and proofs.
The front is `B.prog` for `B : LdFrontTab E Kc z` (Cb/Req1/LdSegFrontTab.lean); "pre" is `B.pre`,
what comes first in it. A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). Fresh after a list of
moves: `LdProg.After` (Cb/Req1/LdReq.lean). `LdProg.Zk`: the same file. A masked block:
`Link.GoodM` (Ior/KnowCollRulesChain.lean).
Cb/Req1/LdSegFrontTab.lean asks, for zero knowledge of the front in the table's order, beside its
hypotheses (asked as `B.OK`) and `B.pre.Zk base`: each sumcheck's link is a masked block, and its
fact is fresh: after `B.pre` for `B.Z.T`, after `B.upTo i` for `B.T i` (i ≤ B.m). Here both are
reduced:
  the first to the conditions on the places of the sumcheck's own masks (`T.OwnOur Rd`: own places
    pairwise different and in Rd; maps and incoming form read Rd only and no own place:
    Cb/Ld/LdPscZk.lean), with `PscOK` from `B.OK`, by `pscBk_goodM` (Cb/Req1/LdSegRefPscZk.lean);
  the second to: the fact is fresh after "pre", and no earlier sumcheck reads what it overwrites
    ("quiet"; exactly: `ldQuiet`, below), by `pscBk_carry`; draws and steps never look.

Main names:
  `ldQuiet S f msg Rd`: overwriting the masks of the fact f changes no entry in Rd, as msg reads the
    entries (exactly:
    `∀ w w' M, f.kc w' = f.put M (f.kc w) → ∀ j, Rd j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j`).
  `B.f0 Rd0`, `B.f i (Rd i)`: the facts of the sumchecks.
  `Spec.ldSegTabZk_carry`: under `B.OK` and `OwnOur` of each sumcheck (`B.Z.T` at Rd0, `B.T j` at
    Rd j for j ≤ B.m): any fact f that is fresh after pre and quiet for all sumchecks of the front
    is fresh after the front: so masks of later blocks (the batching of tensor rows, the splits,
    the next segments) pass.
  `Spec.ldSegTabZk_upTo`: under the same and i ≤ B.m: any fact f that is fresh after pre and quiet
    for the sumchecks before the i-th (`B.T i`) is fresh where the i-th begins.
  `Spec.ldSegTabZk`: `B.prog.Zk base` from: `B.OK`; `B.pre.Zk base`; the places of each sumcheck's
    own masks (`OwnOur`); each sumcheck's fact is fresh after pre, and quiet for the sumchecks
    before it.

Limits: this file does not say that a layout has these properties, or that pairwise different
places for the masks of different blocks, read by nothing else, give them; on `ldQuiet` see
`psc_quiet` and, with the conclusion `¬ ldQuiet ..`, `psc_not_quiet` (each under its own hypotheses:
Cb/Req1/LdSegFrontToyKit.lean). It does not say what "pre" (the lookup) asks and carries.
-/
import Cb.Req1.LdSegFrontTab
import Cb.Req1.LdSegRefPscZk
import Cb.Req1.LdSegCarry
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

/-- Overwriting the masks of f changes no entry in Rd (exactly: the clause below, which speaks of
all pairs of witnesses whose readings by f differ by the overwriting). -/
def ldQuiet {E : Type} (S : Sig E) {Wp J : Type} (f : MaskFact (S.Wit × Wp))
    (msg : S.Msg → J → E) (Rd : J → Prop) : Prop :=
  ∀ w w' M, f.kc w' = f.put M (f.kc w) → ∀ j, Rd j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j

namespace LdFrontTab
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (B : LdFrontTab E Kc z)

def f0 (Rd0 : B.Z.T.J → Prop) : MaskFact (z.S.Wit × z.Wp) :=
  frFact Kc B.Z.T z.S z.E₀ z.Wp (B.Z.ride B.R0) B.msg0 Rd0
def f (i : ℕ) (Rd : (B.T i).J → Prop) : MaskFact (z.S.Wit × z.Wp) :=
  frFact Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i) Rd

end LdFrontTab

namespace Spec

/-- Fresh where the i-th further sumcheck begins. (not all hypotheses are named here: see the
statement below) -/
def ldSegTabZk_upTo : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z)
      (Rd0 : B.Z.T.J → Prop) (Rd : ∀ i, (B.T i).J → Prop) (base : MaskFact B.a.J.W → Prop)
      (f : MaskFact (z.S.Wit × z.Wp)) (i : ℕ),
    B.OK → B.Z.T.OwnOur Rd0 → (∀ j ≤ B.m, (B.T j).OwnOur (Rd j)) → i ≤ B.m → B.pre.After base f →
    ldQuiet z.S f B.msg0 Rd0 → (∀ j < i, ldQuiet z.S f (B.msg j) (Rd j)) → (B.upTo i).After base f

/-- Under the hypotheses below, masks of later blocks pass the front. -/
def ldSegTabZk_carry : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z)
      (Rd0 : B.Z.T.J → Prop) (Rd : ∀ i, (B.T i).J → Prop)
      (base : MaskFact B.a.J.W → Prop) (f : MaskFact (z.S.Wit × z.Wp)),
    B.OK → B.Z.T.OwnOur Rd0 → (∀ j ≤ B.m, (B.T j).OwnOur (Rd j)) → B.pre.After base f →
    ldQuiet z.S f B.msg0 Rd0 → (∀ j ≤ B.m, ldQuiet z.S f (B.msg j) (Rd j)) → B.prog.After base f

/-- What zero knowledge asks of the front, beside its hypotheses, from conditions on places.
(not all hypotheses are named here: see the statement below) -/
def ldSegTabZk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z)
      (Rd0 : B.Z.T.J → Prop) (Rd : ∀ i, (B.T i).J → Prop) (base : MaskFact B.a.J.W → Prop),
    B.OK → B.pre.Zk base → B.Z.T.OwnOur Rd0 → (∀ j ≤ B.m, (B.T j).OwnOur (Rd j)) →
    B.pre.After base (B.f0 Rd0) → (∀ i ≤ B.m, B.pre.After base (B.f i (Rd i))) →
    (∀ i ≤ B.m, ldQuiet z.S (B.f i (Rd i)) B.msg0 Rd0) →
    (∀ i ≤ B.m, ∀ j < i, ldQuiet z.S (B.f i (Rd i)) (B.msg j) (Rd j)) → B.prog.Zk base

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- a step that only maps the explicit part does not look -/
theorem ldStepF_carry (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec} (A : Rels Kc St E₀ (S.Msg × Wp))
    (A' : Rels Kc St' E₀ (S.Msg × Wp)) (g : St → St') (base : MaskFact (S.Wit × Wp) → Prop)
    (f : MaskFact (S.Wit × Wp)) (hb : base f) :
    (ldStepF S A A' g).After base f := by
  unfold ldStepF
  exact segCarry_step (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀, Wp, A'⟩
    _ _ _ _ base f _ f.kc f.put hb (fun _ _ _ _ h => ⟨rfl, h⟩)

/-- the sumcheck alone -/
theorem frPsc_carry (T : PscOur E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E) (Rd : T.J → Prop)
    (h : LdFrontTab.PscOK T) (hO : T.OwnOur Rd) (base : MaskFact (S.Wit × Wp) → Prop)
    (f : MaskFact (S.Wit × Wp)) (hq : ldQuiet S f msg Rd) (hb : base f) :
    (frPsc Kc T S E₀ Wp A0 msg).After base f := by
  unfold frPsc
  rw [LdProg.after_snoc, LdProg.after_nil]
  exact pscBk_carry S T E₀ Wp A0 msg Rd h.vars h.degX h.degY hO base f hq hb

/-- claims joined, then the sumcheck -/
theorem frIn_carry (Z : PscIn E) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E) (Rd : Z.T.J → Prop)
    (h : LdFrontTab.PscOK Z.T) (hO : Z.T.OwnOur Rd) (base : MaskFact (S.Wit × Wp) → Prop)
    (f : MaskFact (S.Wit × Wp)) (hq : ldQuiet S f msg Rd) (hb : base f) :
    (frIn Kc Z S E₀ Wp R0 msg).After base f := by
  unfold frIn
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  refine pscBk_carry S Z.T E₀ Wp (Z.ride R0) msg Rd h.vars h.degX h.degY hO _ f hq ?_
  exact mvA_carry (frInS Kc Z S E₀ Wp R0 msg) _ _ (inBk_plain Z E₀ S.Msg Wp Kc)
    (inBk_sameOn Z E₀ S.Msg Wp Kc Z.T.J msg fun _ => False) base f (fun _ _ _ _ _ h => h.elim) hb

namespace LdFrontTab
variable {z : LdStage E Kc} (B : LdFrontTab E Kc z)

theorem head_carry (h : B.OK) (Rd0 : B.Z.T.J → Prop) (hO : B.Z.T.OwnOur Rd0)
    (base : MaskFact B.a.J.W → Prop) (f : MaskFact (z.S.Wit × z.Wp))
    (hb : B.pre.After base f) (hq : ldQuiet z.S f B.msg0 Rd0) :
    B.head.After base f := by
  unfold LdFrontTab.head
  rw [LdProg.after_snoc, ldProg_app_after]
  exact ldStepF_carry z.S _ _ _ _ f
    (frIn_carry B.Z z.S z.E₀ z.Wp B.R0 B.msg0 Rd0 h.psc0 hO _ f hq hb)

theorem tw_carry (h : B.OK) (Rd : ∀ i, (B.T i).J → Prop) (hO : ∀ j ≤ B.m, (B.T j).OwnOur (Rd j))
    (X : MaskFact (z.S.Wit × z.Wp) → Prop) (f : MaskFact (z.S.Wit × z.Wp)) (hb : X f) :
    ∀ k ≤ B.m, (∀ j ≤ k, ldQuiet z.S f (B.msg j) (Rd j)) → (B.tw k).After X f
  | 0, hk, hq => frPsc_carry _ _ _ _ _ _ (Rd 0) (h.psc 0 hk) (hO 0 hk) X f (hq 0 le_rfl) hb
  | k + 1, hk, hq => by
      rw [tw_succ, ldProg_app_after, LdProg.after_snoc]
      exact frPsc_carry _ _ _ _ _ _ (Rd (k + 1)) (h.psc (k + 1) hk)
        (hO (k + 1) hk) _ f (hq (k + 1) le_rfl)
        (ldStepF_carry z.S _ _ _ _ f
          (tw_carry h Rd hO X f hb k (Nat.le_of_succ_le hk) fun j hj =>
            hq j (Nat.le_succ_of_le hj)))

end LdFrontTab
end

theorem ldSegTabZk_upTo : Spec.ldSegTabZk_upTo := by
  intro E Kc _ _ z B Rd0 Rd base f i h hO0 hO hi hb hq0 hq
  have hh := B.head_carry h Rd0 hO0 base f hb hq0
  cases i with
  | zero => exact hh
  | succ i =>
      rw [LdFrontTab.upTo_succ, LdProg.after_snoc, ldProg_app_after]
      exact ldStepF_carry z.S _ _ _ _ f
        (B.tw_carry h Rd hO _ f hh i (Nat.le_of_succ_le hi) fun j hj => hq j (Nat.lt_succ_of_le hj))

theorem ldSegTabZk_carry : Spec.ldSegTabZk_carry := by
  intro E Kc _ _ z B Rd0 Rd base f h hO0 hO hb hq0 hq
  unfold LdFrontTab.prog
  rw [LdProg.after_snoc, ldProg_app_after]
  exact ldStepF_carry z.S _ _ _ _ f
    (B.tw_carry h Rd hO _ f (B.head_carry h Rd0 hO0 base f hb hq0) B.m le_rfl hq)

theorem ldSegTabZk : Spec.ldSegTabZk := by
  intro E Kc _ _ z B Rd0 Rd base h hp hO0 hO hf0 hf hq0 hq
  refine ldSegTab_zk E Kc z B Rd0 Rd base h hp ?_ hf0 (fun i hi => ?_) (fun i hi => ?_)
  · exact pscBk_goodM z.S B.Z.T z.E₀ z.Wp (B.Z.ride B.R0) B.msg0 Rd0 h.psc0.vars h.psc0.degX
      h.psc0.degY h.psc0.inj hO0
  · exact pscBk_goodM z.S (B.T i) z.E₀ z.Wp (B.A0 i) (B.msg i) (Rd i) (h.psc i hi).vars
      (h.psc i hi).degX (h.psc i hi).degY (h.psc i hi).inj (hO i hi)
  · exact ldSegTabZk_upTo E Kc z B Rd0 Rd base (B.f i (Rd i)) i h hO0 hO hi
      (hf i hi) (hq0 i hi) (hq i hi)

end Cb
