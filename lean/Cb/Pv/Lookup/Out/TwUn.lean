-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwUn.lean.
A right inverse of the reading of a typed transcript as plain data, block for block.

The reading is Tw.fseq, fchain, fdraw (Cb/Pv/Lookup/Out/TwFlat.lean) and flSc, flScC
(Cb/Pv/Lookup/Out/TwSc.lean). Definitions and proofs. The inverse is not computable: a challenge is
found by Function.invFun.

Main names:
  `RSp`, `RFit`: what plain data must look like at a round: how many scalars are sent, how many
    elements are drawn, must the drawn be other than 0.
  `Un f sp`: un : Rounds E → Tr s, with f (un rs) = rs for every rs that fits sp round for round
    (List.Forall₂ RFit sp rs).
  `Un.seq` (by Tr.app, in the block's own nesting), `Un.chain`, `Un.draw`: the rules.
  `Un.full`, `Un.core`: one short sumcheck, with and without the round of the shown values, for
    every Y whose variables' sets of challenges are met by the spec (`VFit`); `Un.full` for every
    list sh of shown values without repeats.
Limits: off what fits nothing is said of un.

-/
import Cb.Pv.Lookup.Out.TwFlat

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Johnson.L5.Layers

/-- what plain data must look like at a round -/
structure RSp where
  sent : ℕ
  drawn : ℕ
  nz : Bool
  deriving DecidableEq, Repr

section
variable {E : Type}

def RFit [Zero E] (s : RSp) (r : List E × List E) : Prop :=
  r.1.length = s.sent ∧ r.2.length = s.drawn ∧ (s.nz = true → ∀ x ∈ r.2, x ≠ 0)

/-- A right inverse of a reading, on what fits. -/
structure Un [Zero E] {s : Shape} (f : Tr s → Rounds E) (sp : List RSp) where
  un : Rounds E → Tr s
  inv : ∀ rs, List.Forall₂ RFit sp rs → f (un rs) = rs

theorem f2_split {α β : Type} {R : α → β → Prop} : ∀ (a b : List α) (u : List β),
    List.Forall₂ R (a ++ b) u → ∃ u₁ u₂, u = u₁ ++ u₂ ∧ List.Forall₂ R a u₁ ∧ List.Forall₂ R b u₂
  | [], _, u, h => ⟨[], u, rfl, .nil, h⟩
  | _ :: a, b, _, .cons h1 h2 =>
    let ⟨u₁, u₂, e, ha, hb⟩ := f2_split a b _ h2
    ⟨_ :: u₁, u₂, congrArg (_ :: ·) e, .cons h1 ha, hb⟩

theorem ofFn_getD [Zero E] (l : List E) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i.1 0) = l := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ h2

theorem one_of_len [Zero E] (l : List E) (h : l.length = 1) : [l.headD 0] = l := by
  match l, h with
  | [_], _ => rfl

theorem nil_of_len (l : List E) (h : l.length = 0) : l = [] := List.length_eq_zero_iff.1 h

end

noncomputable section Rules
variable {E : Type} [Zero E] {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

def Un.seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {f : Fl E a} {g : Fl E b} {sa sb : List RSp}
    (u : Un f sa) (v : Un g sb) : Un (fseq f g) (sa ++ sb) where
  un := fun rs => Tr.app (u.un (rs.take sa.length)) (v.un (rs.drop sa.length))
  inv := fun rs h => by
    obtain ⟨u₁, u₂, rfl, ha, hb⟩ := f2_split sa sb rs h
    rw [fseq_app, ha.length_eq, List.take_left, List.drop_left, u.inv _ ha, v.inv _ hb]

/-- the specs of the blocks 0, .., n in a row -/
def chainSp (sp : ℕ → List RSp) : ℕ → List RSp
  | 0 => sp 0
  | n + 1 => chainSp sp n ++ sp (n + 1)

def Un.chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ∀ l, Fl E (b l))
    (sp : ℕ → List RSp)
    (u : ∀ l, Un (f l) (sp l)) : ∀ n, Un (fchain X b f n) (chainSp sp n)
  | 0 => u 0
  | n + 1 => Un.seq (Un.chain X b f sp u n) (u (n + 1))

def Un.draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    (err : ℕ)
    (dl : D → List E) (k : ℕ) (mk : List E → D) (h : ∀ l, l.length = k → dl (mk l) = l) :
    Un (fdraw D nx Ex err dl) [⟨0, k, false⟩] where
  un := fun rs => (show Tr [drawRound D] from (((), ()), mk (rs.headD ([], [])).2, ()))
  inv := fun rs hf => by
    match rs, hf with
    | [r], .cons h1 .nil =>
      show [(([] : List E), dl (mk r.2))] = [r]
      rw [h _ h1.2.1]
      exact congrArg (fun a => [((a, r.2) : List E × List E)]) (nil_of_len _ h1.1).symm

end Rules

/-! ### one short sumcheck -/
section Sc
variable {E : Type} [Field E]

/-- the spec meets the variables: as many scalars as the degree, one draw, and every element that
the spec lets through is the value of a challenge -/
def VFit : List (PFmt E) → List RSp → Prop
  | [], [] => True
  | f :: l, s :: sp => (s.sent = f.n ∧ s.drawn = 1 ∧ ∀ x : E, (s.nz = true → x ≠ 0) → ∃ c : f.Ch,
      f.val c = x) ∧ VFit l sp
  | _, _ => False

noncomputable def unS : (l : List (PFmt E)) → (t : Shape) → Tr t → Rounds E → Tr (sRounds l ++ t)
  | [], _, τ, _ => τ
  | f :: l, t, τ, rs =>
    (((), fun i : Fin f.n => (rs.headD ([], [])).1.getD i.1 0),
        Function.invFun f.val ((rs.headD ([], [])).2.headD 0),
      unS l t τ rs.tail)

theorem round_inv (f : PFmt E) (s : RSp) (r : List E × List E)
    (hv : s.sent = f.n ∧ s.drawn = 1 ∧ ∀ x : E, (s.nz = true → x ≠ 0) → ∃ c : f.Ch, f.val c = x)
        (hr : RFit s r) :
    ((List.ofFn fun i : Fin f.n => r.1.getD i.1 0, [f.val (Function.invFun f.val (r.2.headD 0))]) :
        List E × List E) = r := by
  have h1 : r.2.length = 1 := hr.2.1.trans hv.2.1
  have h2 : [r.2.headD 0] = r.2 := one_of_len _ h1
  have h3 : f.val (Function.invFun f.val (r.2.headD 0)) = r.2.headD 0 :=
    Function.invFun_eq (hv.2.2 _ fun hz => hr.2.2 hz _
        (by rw [← h2]; exact List.mem_singleton.2 rfl))
  rw [h3, h2, ofFn_getD _ _ (hr.1.trans hv.1)]

theorem flS_unS : ∀ (l : List (PFmt E)) (sp : List RSp),
    VFit l sp → ∀ (t : Shape) (τ : Tr t) (mid rest : Rounds E),
    List.Forall₂ RFit sp mid → flS l t (unS l t τ (mid ++ rest)) = mid
  | [], [], _, _, _, _, _, .nil => rfl
  | f :: l, s :: sp, hv, t, τ, _, rest, .cons (b := r) (l₂ := mid) h1 h2 => by
    show ((List.ofFn fun i : Fin f.n => r.1.getD i.1 0,
        [f.val (Function.invFun f.val (r.2.headD 0))]) : List E × List E) ::
      flS l t (unS l t τ (mid ++ rest)) = r :: mid
    rw [round_inv f s r hv.1 h1, flS_unS l sp hv.2 t τ mid rest h2]

theorem snd_unS : ∀ (l : List (PFmt E)) (t : Shape) (τ : Tr t) (rs : Rounds E),
    Tr.snd (s := sRounds l) (unS l t τ rs) = τ
  | [], _, _, _ => rfl
  | _ :: l, t, τ, rs => snd_unS l t τ rs.tail

noncomputable def unS0 : (l : List (PFmt E)) → Rounds E → Tr (sRounds l)
  | [], _ => ()
  | f :: l, rs =>
    (((), fun i : Fin f.n => (rs.headD ([], [])).1.getD i.1 0),
        Function.invFun f.val ((rs.headD ([], [])).2.headD 0),
      unS0 l rs.tail)

theorem flS0_unS0 : ∀ (l : List (PFmt E)) (sp : List RSp), VFit l sp → ∀ (mid : Rounds E),
    List.Forall₂ RFit sp mid → flS0 l (unS0 l mid) = mid
  | [], [], _, _, .nil => rfl
  | f :: l, s :: sp, hv, _, .cons (b := r) (l₂ := mid) h1 h2 => by
    show ((List.ofFn fun i : Fin f.n => r.1.getD i.1 0,
        [f.val (Function.invFun f.val (r.2.headD 0))]) : List E × List E) ::
      flS0 l (unS0 l mid) = r :: mid
    rw [round_inv f s r hv.1 h1, flS0_unS0 l sp hv.2 mid h2]

open Classical in
/-- the shown values, from their list in the order sh -/
noncomputable def valsOf {A : Type} (sh : List A) (vals : List E) : A → E :=
  fun a => vals.getD (sh.idxOf a) 0

theorem map_valsOf {A : Type} (sh : List A) (hn : sh.Nodup) (vals : List E)
    (h : vals.length = sh.length) :
    sh.map (valsOf sh vals) = vals := by
  classical
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  rw [List.getElem_map]
  unfold valsOf
  rw [hn.idxOf_getElem]
  exact List.getD_eq_getElem _ _ h2

end Sc

section Full
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

noncomputable def Un.full (Y : PscPar E) (sh : List Y.A) (hn : sh.Nodup) (sp : List RSp)
    (hv : VFit Y.fmt sp) :
    Un (flFull Ex Y sh) (⟨1, 1, false⟩ :: (sp ++ [⟨sh.length, 0, false⟩])) where
  un := fun rs => (show Tr (shapeS Y) from
    (((), (rs.headD ([], [])).1.headD 0), (rs.headD ([], [])).2.headD 0,
      unS Y.fmt [pRoundV E Y.A] (((), valsOf sh (rs.getLastD ([], [])).1), (), ()) rs.tail))
  inv := fun rs hf => by
    match rs, hf with
    | r0 :: u, .cons h0 h1 =>
      obtain ⟨mid, lst, rfl, hm, hl⟩ := f2_split sp _ u h1
      match lst, hl with
      | [rv], .cons hrv .nil =>
        have e0 : (([r0.1.headD 0], [r0.2.headD 0]) : List E × List E) = r0 := by
          rw [one_of_len _ h0.1, one_of_len _ h0.2.1]
        have eL : (r0 :: (mid ++ [rv])).getLastD ([], []) = rv :=
          List.getLastD_concat (l := r0 :: mid)
        show (([r0.1.headD 0], [r0.2.headD 0]) : List E × List E) ::
          (flS Y.fmt [pRoundV E Y.A] (unS Y.fmt [pRoundV E Y.A]
              (((), valsOf sh ((r0 :: (mid ++ [rv])).getLastD ([], [])).1), (), ()) (mid ++ [rv]))
                  ++
            [(sh.map (Tr.snd (s := sRounds Y.fmt) (t := [pRoundV E Y.A]) (unS Y.fmt [pRoundV E Y.A]
              (((), valsOf sh ((r0 :: (mid ++ [rv])).getLastD ([], [])).1), (), ())
                  (mid ++ [rv]))).1.2, [])]) =
          r0 :: (mid ++ [rv])
        rw [e0, flS_unS Y.fmt sp hv _ _ mid [rv] hm, snd_unS, eL]
        show r0 :: (mid ++ [(sh.map (valsOf sh rv.1), [])]) = _
        rw [map_valsOf sh hn rv.1 hrv.1, ← nil_of_len rv.2 hrv.2.1]

noncomputable def Un.core (Y : PscPar E) (sp : List RSp) (hv : VFit Y.fmt sp) :
    Un (flCore Ex Y) (⟨1, 1, false⟩ :: sp) where
  un := fun rs => (show Tr (shapeSC Y) from
    (((), (rs.headD ([], [])).1.headD 0), (rs.headD ([], [])).2.headD 0, unS0 Y.fmt rs.tail))
  inv := fun rs hf => by
    match rs, hf with
    | r0 :: u, .cons h0 h1 =>
      have e0 : (([r0.1.headD 0], [r0.2.headD 0]) : List E × List E) = r0 := by
        rw [one_of_len _ h0.1, one_of_len _ h0.2.1]
      show (([r0.1.headD 0], [r0.2.headD 0]) : List E × List E) :: flS0 Y.fmt (unS0 Y.fmt u) = r0 ::
          u
      rw [e0, flS0_unS0 Y.fmt sp hv u h1]

end Full
end Tw

#print axioms Tw.f2_split
#print axioms Tw.ofFn_getD
#print axioms Tw.one_of_len
#print axioms Tw.nil_of_len
#print axioms Tw.round_inv
#print axioms Tw.flS_unS
#print axioms Tw.snd_unS
#print axioms Tw.flS0_unS0
#print axioms Tw.map_valsOf
#print axioms Tw.Un.seq
#print axioms Tw.Un.chain
#print axioms Tw.Un.draw
#print axioms Tw.Un.full
#print axioms Tw.Un.core
