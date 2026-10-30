-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarryTen.lean: from the wide fact to the facts that the blocks on tensor rows need.

Definitions, statements (Cb.Spec.segTen_*) and proofs. Glue.

Cb/Req1/LdSegCarry.lean carries one standard fact on masks sent in advance from move to move of a
request (`a.wideFact Rd Rr own Mk val`). The batching of tensor rows on the encoded index
(Cb/Req1/LdSegRefTen.lean: `X.link`, letters `X.mask`) and the toy block that makes such rows
(Cb/Ld/LdTenSay.lean: `X.sayLink`, letters `X.sayMask κ`) ask for a narrow fact: of a witness they
read the matrix of the prover's index message and the entries in X.Rd; their overwriting is
"overwrite the entries at named places".

Main names:
  `X.tenCut w`: that reading. `X.atOwn at'`, `X.atVal at' M`: the set of the places at' i, and the
    vector M laid at them. `X.tenG`: the narrow reading as a function of the wide one.
  `Spec.segTen_rd`, `Spec.segTen_com`, `Spec.segTen_key`: X.tenCut w = X.tenG (wide reading of w),
    if X.Rd lies in Rd; X.tenG commutes with the two overwritings, if the places are different and
    lie in X.Rd; so: two witnesses whose wide readings differ by the overwriting have narrow
    readings that differ by the overwriting.
  `Spec.segTen_narrow`: under these three conditions, for a finite non-empty type Mk of masks: after
    any chain that ends at a stage over X.S with the further witness (prover encoded index, X.Wp):
    the wide fact at places at' gives the narrow fact at these places. (At at' := X.μAt ∘ κ that is
    (X.sayMask κ).fact, at at' := X.wAt it is X.mask.fact, by definition.)
  `Spec.segTen_in`, `Spec.segTen_say`, `Spec.segTen_tail` are under `X.Own` and "X.Rd lies in Rd".
  `Spec.segTen_in`: the re-bracketing before the batching: wide fact at X.wAt before it ⇒
    X.stepIn.After base X.mask.fact: a premise of the statements on zero knowledge of
    Cb/Req1/LdSegRefTen.lean and Cb/Obj/LdObjectReqEnd.lean.
  `Spec.segTen_say`: the toy block does not look at the batching's own masks in this sense: the wide
    fact at X.wAt goes through it. (It says values of forms that read the matrix and the places
    X.μAt a; by X.Own these lie in X.Rd and are no places X.wAt i.)
  `Spec.segTen_tail`: so through "the values are said; the rows come out; the re-bracketing": wide
    fact at X.wAt before ⇒ X.stepIn.After (X.sayT.After base) X.mask.fact.

Limits: this file does not say that the wide fact is fresh there (Cb/Req1/LdSegCarry.lean,
Cb/Req1/LdSegCarryClose.lean, Cb/Req1/LdSegSendFresh.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry
import Cb.Ld.LdTenSay
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

namespace LdTenD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc)

open Classical in
/-- What the blocks on tensor rows read of a witness. -/
def tenCut (w : X.S.Wit × (X.C.PIdx × X.Wp)) : X.bt.J → E := fun j =>
  if X.RdJ j then X.msg (w.2.1.1.1, X.S.msgs w.1) j else 0

/-- the places; a vector laid at them -/
def atOwn {I : Type} (at' : I → X.S.Ent) : X.S.Ent → Prop := fun n => ∃ i, at' i = n
def atVal {I : Type} (at' : I → X.S.Ent) (M : I → E) : X.S.Ent → E :=
  Function.extend at' M fun _ => 0

open Classical in
/-- the narrow reading as a function of the wide one -/
def tenG (k : X.S.Msg × (∀ o, Option (X.S.om o).Rnd) × (X.C.PIdx × X.Wp)) :
    X.bt.J → E :=
  fun j => if X.RdJ j then X.msg (k.2.2.1.1.1, k.1) j else 0

/-- a stage over X.S with the further witness (prover encoded index, X.Wp) -/
@[reducible] def stg (St : Type) (E₀ : ExtSpec) (A : Rels Kc St E₀ (X.S.Msg × (X.C.PIdx × X.Wp))) :
    LdStage E Kc :=
  ⟨X.S, St, E₀, X.C.PIdx × X.Wp, A⟩

end LdTenD

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

def segTen_rd : Prop :=
  ∀ (X : LdTenD E Kc) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    (∀ n, X.Rd n → Rd n) → ∀ w, X.tenCut w = X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w)

def segTen_com : Prop :=
  ∀ (X : LdTenD E Kc) (I : Type) (at' : I → X.S.Ent), Function.Injective at' → (∀ i, X.Rd (at' i)) →
    ∀ (M : I → E) k, X.tenG (X.S.ow (X.atOwn at') (X.atVal at' M) k.1, k.2) =
      Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) M (X.tenG k)

def segTen_key : Prop :=
  ∀ (X : LdTenD E Kc) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (I : Type) (at' : I → X.S.Ent),
    (∀ n, X.Rd n → Rd n) → Function.Injective at' → (∀ i, X.Rd (at' i)) →
    ∀ (w w' : X.S.Wit × (X.C.PIdx × X.Wp)) (M : I → E), X.S.wide (X.C.PIdx × X.Wp) Rd Rr w' =
        (X.S.ow (X.atOwn at') (X.atVal at' M) (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w).1,
          (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w).2) →
      X.tenCut w' = Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) M (X.tenCut w)

/-- Under the hypotheses below, after any chain: the wide fact gives the narrow one. -/
def segTen_narrow : Prop :=
  ∀ (X : LdTenD E Kc) (St : Type) (E₀ : ExtSpec) (A : Rels Kc St E₀ (X.S.Msg × (X.C.PIdx × X.Wp)))
      (Aj : Joint Kc) (c : Chain Kc Aj (X.stg St E₀ A).J) (base : MaskFact Aj.W → Prop)
      (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (I : Type) (at' : I → X.S.Ent) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (v : Mk → I → E),
    (∀ n, X.Rd n → Rd n) → Function.Injective at' → (∀ i, X.Rd (at' i)) →
    c.FreshGiven base ((X.stg St E₀ A).wideFact Rd Rr (X.atOwn at') Mk fun M => X.atVal at' (v M)) →
    c.FreshGiven base
      ⟨X.bt.J → E, X.tenCut, Mk,
        fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k⟩

/-- The re-bracketing before the batching. -/
def segTen_in : Prop :=
  ∀ (X : LdTenD E Kc) (base : MaskFact X.src.J.W → Prop) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    X.Own → (∀ n, X.Rd n → Rd n) →
    base (X.src.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M) →
    X.stepIn.After base X.mask.fact

/-- Under the hypotheses below, the toy block does not look at the batching's own masks in this
sense: the wide fact at X.wAt goes through it (if that fact is in `base`, it is in
`(LdMv.sub X.p1 X.m0 (.one X.sayLink)).After base`). -/
def segTen_say : Prop :=
  ∀ (X : LdTenD E Kc) (base : MaskFact X.p1.J.W → Prop) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    X.Own → (∀ n, X.Rd n → Rd n) →
    base (X.p1.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M) →
    (LdMv.sub X.p1 X.m0 (.one X.sayLink)).After
      base (X.m0.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M)

/-- The values are said; the rows come out; the re-bracketing. -/
def segTen_tail : Prop :=
  ∀ (X : LdTenD E Kc) (base : MaskFact X.p1.J.W → Prop) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    X.Own → (∀ n, X.Rd n → Rd n) →
    base (X.p1.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M) →
    X.stepIn.After (X.sayT.After base) X.mask.fact

end
end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem segTen_rd : Spec.segTen_rd E Kc := by
  classical
  intro X Rd Rr hR w
  funext j
  cases j with
  | inl a => rfl
  | inr n =>
      show (if X.Rd n then X.S.msgs w.1 n.1 n.2 else 0) =
        if X.Rd n then (if Rd ⟨n.1, n.2⟩ then X.S.msgs w.1 n.1 n.2 else 0) else 0
      by_cases hn : X.Rd n
      · rw [if_pos hn, if_pos hn, if_pos (hR n hn)]
      · rw [if_neg hn, if_neg hn]

theorem segTen_com : Spec.segTen_com E Kc := by
  classical
  intro X I at' hi hr M k
  have hi' : Function.Injective fun i => (Sum.inr (at' i) : X.bt.J) := fun _ _ e =>
    hi (Sum.inr_injective e)
  funext j
  cases j with
  | inl a =>
      rw [Function.extend_apply' _ _ _ fun ⟨i, e⟩ => Sum.inr_ne_inl e]
      rfl
  | inr n =>
      by_cases hn : ∃ i, at' i = n
      · obtain ⟨i, rfl⟩ := hn
        rw [hi'.extend_apply]
        show (if X.Rd (at' i) then
              (if X.atOwn at' ⟨(at' i).1, (at' i).2⟩ then X.atVal at' M ⟨(at' i).1, (at' i).2⟩
                else k.1 (at' i).1 (at' i).2)
            else 0) = M i
        rw [if_pos (hr i), if_pos (show X.atOwn at' (at' i) from ⟨i, rfl⟩)]
        exact hi.extend_apply M _ i
      · rw [Function.extend_apply' _ _ _ fun ⟨i, e⟩ => hn ⟨i, Sum.inr_injective e⟩]
        show (if X.Rd n then
              (if X.atOwn at' ⟨n.1, n.2⟩ then X.atVal at' M ⟨n.1, n.2⟩ else k.1 n.1 n.2)
            else 0) =
          if X.Rd n then k.1 n.1 n.2 else 0
        rw [if_neg (show ¬ X.atOwn at' n from hn)]

theorem segTen_key : Spec.segTen_key E Kc := by
  intro X Rd Rr I at' hR hi hr w w' M h
  rw [segTen_rd X Rd Rr hR w', h, segTen_com X I at' hi hr M, ← segTen_rd X Rd Rr hR w]

theorem segTen_narrow : Spec.segTen_narrow E Kc := by
  intro X St E₀ A Aj c base Rd Rr I at' Mk _ _ v hR hi hr h
  have h1 := freshGiven_conseq Kc Aj _ c base _ (X.bt.J → E) X.tenG
    (fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k)
    (fun M k => segTen_com X I at' hi hr (v M) k) h
  have e : (fun w => X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w)) = X.tenCut :=
    funext fun w => (segTen_rd X Rd Rr hR w).symm
  have h2 : c.FreshGiven base
      ⟨X.bt.J → E,
        fun w => X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w),
        Mk,
        fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k⟩ := h1
  rw [e] at h2
  exact h2

theorem segTen_in : Spec.segTen_in E Kc := by
  intro X base Rd Rr hO hR hb
  unfold LdTenD.stepIn
  exact segCarry_step X.src X.m0 _ _ _ _ base
    (X.src.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M) _ X.mask.kc X.mask.put
    hb fun _ w w' M h => ⟨rfl, segTen_key X Rd Rr _ X.wAt hR hO.inj hO.own w w' M h⟩

/-- under `hO`: two witnesses whose narrow readings differ at the places X.wAt only give the same
values of the forms -/
theorem LdTenD.lhs_same (X : LdTenD E Kc) (hO : X.Own) (w w' : X.S.Wit × (X.C.PIdx × X.Wp))
    (M : PIdx (List.replicate X.k (pfCube E X.n)) → E)
    (h : X.tenCut w' = Function.extend (fun i => (Sum.inr (X.wAt i) : X.bt.J)) M (X.tenCut w))
    (st : X.bt.St) (q : X.bt.Q) :
    X.bt.lhs st q (X.msg (w'.2.1.1.1, X.S.msgs w'.1)) =
      X.bt.lhs st q (X.msg (w.2.1.1.1, X.S.msgs w.1)) := by
  classical
  have hj : ∀ j, X.RdJ j → (∀ i, (Sum.inr (X.wAt i) : X.bt.J) ≠ j) →
      X.msg (w'.2.1.1.1, X.S.msgs w'.1) j = X.msg (w.2.1.1.1, X.S.msgs w.1) j := fun j hr hn => by
    have e := congrFun h j
    rw [Function.extend_apply' _ _ _ fun ⟨i, e'⟩ => hn i e'] at e
    have e1 : X.tenCut w' j = X.msg (w'.2.1.1.1, X.S.msgs w'.1) j := if_pos hr
    have e2 : X.tenCut w j = X.msg (w.2.1.1.1, X.S.msgs w.1) j := if_pos hr
    rw [← e1, ← e2, e]
  refine X.bt.lhs_congr (fun a => hj (Sum.inl a) trivial fun _ e => Sum.inr_ne_inl e) fun j hs => ?_
  cases j with
  | inl a => exact hj (Sum.inl a) trivial fun _ e => Sum.inr_ne_inl e
  | inr n =>
      have hx : ∃ a, X.μAt a = n := by
        by_contra hc
        exact hs (placed_off X.μAt _ n fun a e => hc ⟨a, e⟩)
      obtain ⟨a, rfl⟩ := hx
      exact hj _ (hO.rdM a) fun i e => hO.wM i a (Sum.inr_injective e)

theorem segTen_say : Spec.segTen_say E Kc := by
  intro X base Rd Rr hO hR hb
  refine (freshGiven_one X.sayLink base _).2
    (Or.inr ⟨_, (X.p1.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M).kc,
        (X.p1.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M).put,
        hb, ?_⟩)
  intro w w' M x _ ρ h
  have e : (fun q => X.bt.lhs x.1 q (X.msg (w'.2.1.1.1, X.S.msgs w'.1))) =
      fun q => X.bt.lhs x.1 q (X.msg (w.2.1.1.1, X.S.msgs w.1)) :=
    funext fun q =>
      X.lhs_same hO w w' M (segTen_key X Rd Rr _ X.wAt hR hO.inj hO.own w w' M h) x.1 q
  refine ⟨?_, ?_, h⟩
  · show ((((), fun q => X.bt.lhs x.1 q (X.msg (w'.2.1.1.1, X.S.msgs w'.1))),
        ρ.1,
        ()) : Tr [sayRound (X.bt.Q → E) 0]) =
      (((), fun q => X.bt.lhs x.1 q (X.msg (w.2.1.1.1, X.S.msgs w.1))), ρ.1, ())
    rw [e]
    rfl
  · show (((fun q => X.bt.lhs x.1 q (X.msg (w'.2.1.1.1, X.S.msgs w'.1))), x.1), x.2) =
      (((fun q => X.bt.lhs x.1 q (X.msg (w.2.1.1.1, X.S.msgs w.1))), x.1), x.2)
    rw [e]

theorem segTen_tail : Spec.segTen_tail E Kc := by
  intro X base Rd Rr hO hR hb
  refine segTen_in X _ Rd Rr hO hR ?_
  unfold LdTenD.sayT
  rw [LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
  unfold LdTenD.stepBack
  exact segCarry_step X.m0 X.src _ _ _ _ _
    (X.m0.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M) _
    (X.src.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M).kc
    (X.src.wideFact Rd Rr (X.atOwn X.wAt) X.mask.Mk fun M => X.atVal X.wAt M).put
    (segTen_say X base Rd Rr hO hR hb) fun _ _ _ _ h => ⟨rfl, h⟩

end
end Cb
