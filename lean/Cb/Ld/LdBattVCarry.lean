-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVCarry.lean: from wide facts to the fact that the batching with a value shown needs: one
wide fact on all its own entries; and that one from two, one for each holder.

Definitions, statements and proofs. The lemmas are auxiliary: they connect two files.
Cb/Req1/LdSegCarry.lean carries one standard fact on masks sent in advance from move to move of a
request (`a.wideFact Rd Rr own Mk val`). The block (Cb/Ld/LdBattVSeg.lean: `X.link`, letters
`X.mask`) asks for a narrow fact: of a witness it reads the matrix of the prover's index message and
the entries in `X.Rd`; its overwriting is "overwrite the entries at named places".
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`. (Cb/Req1/LdSegFresh.lean.)

Main names:
  `Spec.ldBattVSeg_rd`, `Spec.ldBattVSeg_com`, `Spec.ldBattVSeg_key`: as in
    Cb/Req1/LdSegCarryTen.lean, for any injective family of places in `X.Rd` (`X.tenCut`, `X.tenG`:
    their doc comments below; the wide reading: `Sig.wide`, Cb/Req1/LdSegCarry.lean). If Rd holds of
    every entry in `X.Rd`, `X.tenCut w` is `X.tenG` of the wide reading of w (rd). `X.tenG` of a
    wide reading overwritten at the places by M is `X.tenG` of that reading, overwritten there by M
    (com). So, if Rd holds of every entry in `X.Rd`: if the wide reading of w' is that of w
    overwritten at the places by M, `X.tenCut w'` is `X.tenCut w` overwritten there by M (key).
  `Spec.ldBattVSeg_narrow`: if Rd holds of every entry in `X.Rd`, at' is injective with its places
    in `X.Rd`, and the set Mk of values is finite and not empty, then after any chain that ends at a
    stage over X.S with the further witness (prover encoded index, X.Wp) the wide fact at places at'
    gives the narrow fact at these places.
  `Spec.ldBattVSeg_in` (the re-bracketing before the block): under `X.Own`, and if Rd holds of every
    entry in `X.Rd`, the wide fact at `X.ownAt` before it ⇒ `X.stepIn.After base X.mask.fact`, the
    last premise of `Spec.ldBattVSeg_zk`.
  `Spec.ldBattVSeg_pair` (two holders: the head of Cb/Ld/LdBattV.lean): under `X.Own`, at any stage
    over X.S with that further witness (`X.stg`), in every set of facts closed under joining (in
    this sense: `MaskFact.JCl`, Cb/Req1/LdSegFreshS.lean), a wide fact on the hiding coefficients
    and a wide fact on the inner entry give the wide fact at `X.ownAt`, at every reading within both
    that holds all own entries.

Limits: this file does not say that the two wide facts are fresh there. In the calculus that closes
the set of fresh facts after every move, `Spec.ldBattVSeg_two` (Cb/Ld/LdBattVSeg.lean) does the same
in one step at the block's own stage.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSegProofs
import Cb.Req1.LdSegCarryJoin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)

open Classical in
/-- What the block reads of a witness. -/
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

/-- The places of all own entries; their values in one vector. -/
def ownAt : X.bt.WIx ⊕ Unit → X.S.Ent := Sum.elim X.wAt fun _ => X.cAt
def mkOf (M : X.mask.Mk) : X.bt.WIx ⊕ Unit → E := Sum.elim M.1 M.2

end LdTenVD

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

def ldBattVSeg_rd : Prop :=
  ∀ (X : LdTenVD E Kc) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    (∀ n, X.Rd n → Rd n) → ∀ w, X.tenCut w = X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w)

def ldBattVSeg_com : Prop :=
  ∀ (X : LdTenVD E Kc) (I : Type) (at' : I → X.S.Ent), Function.Injective at' →
    (∀ i, X.Rd (at' i)) →
    ∀ (M : I → E) k, X.tenG (X.S.ow (X.atOwn at') (X.atVal at' M) k.1, k.2) =
      Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) M (X.tenG k)

def ldBattVSeg_key : Prop :=
  ∀ (X : LdTenVD E Kc) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (I : Type) (at' : I → X.S.Ent),
    (∀ n, X.Rd n → Rd n) → Function.Injective at' → (∀ i, X.Rd (at' i)) →
    ∀ (w w' : X.S.Wit × (X.C.PIdx × X.Wp)) (M : I → E), X.S.wide (X.C.PIdx × X.Wp) Rd Rr w' =
        (X.S.ow (X.atOwn at') (X.atVal at' M) (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w).1,
          (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w).2) →
      X.tenCut w' = Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) M (X.tenCut w)

/-- Under the hypotheses below, after any chain: the wide fact gives the narrow one. -/
def ldBattVSeg_narrow : Prop :=
  ∀ (X : LdTenVD E Kc) (St : Type) (E₀ : ExtSpec) (A : Rels Kc St E₀ (X.S.Msg × (X.C.PIdx × X.Wp)))
      (Aj : Joint Kc) (c : Chain Kc Aj (X.stg St E₀ A).J) (base : MaskFact Aj.W → Prop)
      (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop) (I : Type) (at' : I → X.S.Ent) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (v : Mk → I → E),
    (∀ n, X.Rd n → Rd n) → Function.Injective at' → (∀ i, X.Rd (at' i)) →
    c.FreshGiven base ((X.stg St E₀ A).wideFact Rd Rr (X.atOwn at') Mk fun M => X.atVal at' (v M)) →
    c.FreshGiven base
      ⟨X.bt.J → E, X.tenCut, Mk,
        fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k⟩

/-- The re-bracketing before the block. -/
def ldBattVSeg_in : Prop :=
  ∀ (X : LdTenVD E Kc) (base : MaskFact X.src.J.W → Prop) (Rd : X.S.Ent → Prop) (Rr : X.S.O → Prop),
    X.Own → (∀ n, X.Rd n → Rd n) →
    base (X.src.wideFact Rd Rr (X.atOwn X.ownAt) X.mask.Mk fun M => X.atVal X.ownAt (X.mkOf M)) →
    X.stepIn.After base X.mask.fact

/-- Two holders: the wide fact on all own entries from two wide facts. (not all hypotheses are named
here: see the statement below) -/
def ldBattVSeg_pair : Prop :=
  ∀ (X : LdTenVD E Kc) (St : Type) (E₀ : ExtSpec)
      (A : Rels Kc St E₀ (X.S.Msg × (X.C.PIdx × X.Wp))) (Y : MaskFact (X.stg St E₀ A).J.W → Prop)
      (Rd₁ Rd₂ Rd : X.S.Ent → Prop) (Rr₁ Rr₂ Rr : X.S.O → Prop),
    X.Own → (∀ n, Rd n → Rd₁ n ∧ Rd₂ n) → (∀ o, Rr o → Rr₁ o ∧ Rr₂ o) → (∀ i, Rd (X.ownAt i)) →
    MaskFact.JCl Y
      ((X.stg St E₀ A).wideFact Rd₁ Rr₁ (X.atOwn X.wAt) (X.bt.WIx → E) fun M => X.atVal X.wAt M) →
    MaskFact.JCl Y
      ((X.stg St E₀ A).wideFact Rd₂ Rr₂ (X.atOwn fun _ : Unit => X.cAt) (Unit → E)
        fun M => X.atVal (fun _ : Unit => X.cAt) M) →
    MaskFact.JCl Y
      ((X.stg St E₀ A).wideFact Rd Rr (X.atOwn X.ownAt) X.mask.Mk fun M =>
        X.atVal X.ownAt (X.mkOf M))

end
end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem ldBattVSeg_rd : Spec.ldBattVSeg_rd E Kc := by
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

theorem ldBattVSeg_com : Spec.ldBattVSeg_com E Kc := by
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

theorem ldBattVSeg_key : Spec.ldBattVSeg_key E Kc := by
  intro X Rd Rr I at' hR hi hr w w' M h
  rw [ldBattVSeg_rd X Rd Rr hR w', h, ldBattVSeg_com X I at' hi hr M, ← ldBattVSeg_rd X Rd Rr hR w]

theorem ldBattVSeg_narrow : Spec.ldBattVSeg_narrow E Kc := by
  intro X St E₀ A Aj c base Rd Rr I at' Mk _ _ v hR hi hr h
  have h1 := freshGiven_conseq Kc Aj _ c base _ (X.bt.J → E) X.tenG
    (fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k)
    (fun M k => ldBattVSeg_com X I at' hi hr (v M) k) h
  have e : (fun w => X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w)) = X.tenCut :=
    funext fun w => (ldBattVSeg_rd X Rd Rr hR w).symm
  have h2 : c.FreshGiven base
      ⟨X.bt.J → E,
        fun w => X.tenG (X.S.wide (X.C.PIdx × X.Wp) Rd Rr w),
        Mk,
        fun M k => Function.extend (fun i => (Sum.inr (at' i) : X.bt.J)) (v M) k⟩ := h1
  rw [e] at h2
  exact h2

namespace LdTenVD
variable (X : LdTenVD E Kc)

theorem ownAt_inj (hO : X.Own) : Function.Injective X.ownAt := by
  rintro (i | _) (j | _) e
  · exact congrArg Sum.inl (hO.inj e)
  · exact absurd e (hO.wc i)
  · exact absurd e.symm (hO.wc j)
  · rfl

theorem ownAt_rd (hO : X.Own) : ∀ i, X.Rd (X.ownAt i)
  | .inl i => hO.own i
  | .inr _ => hO.ownC

/-- the block's overwriting, in terms of places -/
theorem put_eq (M : X.mask.Mk) (k : X.bt.J → E) :
    X.mask.put M k = Function.extend (fun i => (Sum.inr (X.ownAt i) : X.bt.J)) (X.mkOf M) k := by
  have e : (fun i => (Sum.inr (X.ownAt i) : X.bt.J)) =
      Sum.elim X.bt.wAt fun _ : Unit => X.bt.cAt := funext fun i => by
    cases i <;> rfl
  rw [e]
  rfl

end LdTenVD

theorem ldBattVSeg_in : Spec.ldBattVSeg_in E Kc := by
  intro X base Rd Rr hO hR hb
  unfold LdTenVD.stepIn
  exact segCarry_step X.src X.m0 _ _ _ _ base
    (X.src.wideFact Rd Rr (X.atOwn X.ownAt) X.mask.Mk fun M => X.atVal X.ownAt (X.mkOf M))
    _ X.mask.kc X.mask.put hb fun _ w w' M h =>
      ⟨rfl, (ldBattVSeg_key X Rd Rr _ X.ownAt hR (X.ownAt_inj hO) (X.ownAt_rd hO)
            w w' (X.mkOf M) h).trans
          (X.put_eq M _).symm⟩

open Classical in
theorem ldBattVSeg_pair : Spec.ldBattVSeg_pair E Kc := by
  intro X St E₀ A Y Rd₁ Rd₂ Rd Rr₁ Rr₂ Rr hO h1 h2 h3 hW hC
  have hp := wideJ_pair (X.stg St E₀ A) Y Rd₁ Rd₂ Rd Rr₁ Rr₂ Rr (X.atOwn X.wAt)
    (X.atOwn fun _ : Unit => X.cAt) (X.bt.WIx → E) (Unit → E) (fun M => X.atVal X.wAt M)
    (fun M => X.atVal (fun _ : Unit => X.cAt) M) h1 h2
    (by
      rintro n (⟨i, rfl⟩ | ⟨_, rfl⟩)
      · exact h3 (.inl i)
      · exact h3 (.inr ())) hW hC
  have hput : ∀ (M : (X.bt.WIx → E) × (Unit → E)) (m : X.S.Msg),
      X.S.ow (X.atOwn X.ownAt) (X.atVal X.ownAt (Sum.elim M.1 M.2)) m =
        X.S.ow (fun n => X.atOwn X.wAt n ∨ X.atOwn (fun _ : Unit => X.cAt) n)
          (fun n =>
            if X.atOwn X.wAt n then X.atVal X.wAt M.1 n else X.atVal (fun _ : Unit => X.cAt) M.2 n)
          m := by
    intro M m
    funext a j
    have op : ∀ (own : X.S.Ent → Prop) (v : X.S.Ent → E),
        own ⟨a, j⟩ → X.S.ow own v m a j = v ⟨a, j⟩ :=
      fun _ _ h => if_pos h
    have on : ∀ (own : X.S.Ent → Prop) (v : X.S.Ent → E),
        ¬ own ⟨a, j⟩ → X.S.ow own v m a j = m a j :=
      fun _ _ h => if_neg h
    by_cases hw : X.atOwn X.wAt ⟨a, j⟩
    · obtain ⟨i, hi⟩ := hw
      rw [op _ _ (show X.atOwn X.ownAt ⟨a, j⟩ from ⟨.inl i, hi⟩),
        op _ _
          (show X.atOwn X.wAt ⟨a, j⟩ ∨ X.atOwn (fun _ : Unit => X.cAt) ⟨a, j⟩ from Or.inl ⟨i, hi⟩)]
      refine Eq.trans ?_ (if_pos (show X.atOwn X.wAt ⟨a, j⟩ from ⟨i, hi⟩)).symm
      rw [← hi]
      exact ((X.ownAt_inj hO).extend_apply (Sum.elim M.1 M.2) _ (.inl i)).trans
        (hO.inj.extend_apply M.1 _ i).symm
    · by_cases hc : (⟨a, j⟩ : X.S.Ent) = X.cAt
      · rw [op _ _ (show X.atOwn X.ownAt ⟨a, j⟩ from ⟨.inr (), hc.symm⟩),
          op _ _ (show X.atOwn X.wAt ⟨a, j⟩ ∨ X.atOwn (fun _ : Unit => X.cAt) ⟨a, j⟩
              from Or.inr ⟨(), hc.symm⟩)]
        refine Eq.trans ?_ (if_neg hw).symm
        rw [hc]
        exact ((X.ownAt_inj hO).extend_apply (Sum.elim M.1 M.2) _ (.inr ())).trans
          ((show Function.Injective (fun _ : Unit => X.cAt) from fun _ _ _ => rfl).extend_apply
            M.2 _ ()).symm
      · rw [on _ _ (show ¬ X.atOwn X.ownAt ⟨a, j⟩ by
            rintro ⟨i | _, e⟩
            · exact hw ⟨i, e⟩
            · exact hc e.symm), on _ _ (show ¬ (X.atOwn X.wAt ⟨a, j⟩ ∨ X.atOwn (fun _ : Unit => X.cAt) ⟨a, j⟩) by
            rintro (h | ⟨_, h⟩)
            · exact hw h
            · exact hc h.symm)]
  have he := @MaskFact.JCl.equiv _ Y _ X.mask.Mk X.mask.finMk X.mask.neMk (Equiv.refl _) hp
  have key : (X.stg St E₀ A).wideFact
        Rd Rr (X.atOwn X.ownAt) X.mask.Mk (fun M => X.atVal X.ownAt (X.mkOf M)) =
      @MaskFact.mk _ (X.S.Msg × (∀ o, Option (X.S.om o).Rnd) × (X.C.PIdx × X.Wp))
        (X.S.wide (X.C.PIdx × X.Wp) Rd Rr) X.mask.Mk X.mask.finMk X.mask.neMk
        (fun M k =>
          (X.S.ow (fun n => X.atOwn X.wAt n ∨ X.atOwn (fun _ : Unit => X.cAt) n)
              (fun n =>
                if X.atOwn X.wAt n then X.atVal X.wAt M.1 n
                else X.atVal (fun _ : Unit => X.cAt) M.2 n) k.1,
            k.2)) :=
    congrArg (fun p =>
        @MaskFact.mk _ (X.S.Msg × (∀ o, Option (X.S.om o).Rnd) × (X.C.PIdx × X.Wp))
          (X.S.wide (X.C.PIdx × X.Wp) Rd Rr) X.mask.Mk X.mask.finMk X.mask.neMk p)
      (funext fun M => funext fun k => congrArg (fun u => (u, k.2)) (hput M k.1))
  rw [key]
  exact he

end
end Cb
