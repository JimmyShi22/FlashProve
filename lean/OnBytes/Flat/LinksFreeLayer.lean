-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeLayer.lean: the check of a group of layers at two lists of tokens: `LayerFree`
(OnBytes/Flat/LinksFree.lean), one of the four statements from which the rounds of a proof's first
chain do not hang on the request, is shown.

Where the tokens go, by the program's text. A group that is not the first never reads them: its
check at two lists of tokens is one term, by unfolding. In the first group they are read once, in
the embedding's claim on the weights (`ClaimEnv.claimE`, OnBytes/Model/LayerPanels.lean): one factor
of that claim is an array of V elements that is made of them. `wsForkEnd` (OnBytes/Model/Merge.lean)
makes three public tests on the claims (their number, their units, their sizes) and lays what is
left of each into the field `recs` of what it returns; its messages do not take the claims. No
routine writes a value made of the tokens into the state, and the rest of the check reads the other
fields alone. So the two runs are compared from one state (`cmpS`, `cmpL`: every relation on states
is equality), and wherever the two texts agree up to unfolding nothing is asked of a routine but
that it leaves the two flags of a run as they are.

Main definitions: `FacAlike`, `ClaimAlike` (two claims: one unit, factors of the same sizes),
`OptRel`, `cmpS`, `cmpL`, `OwnAlike`. Main theorems: `shape_alike`, `rowPart_alike`, `wsForkEnd_rel`
(at two lists of claims that are alike; the head's check calls it too), `claimE_alike`,
`hearOwn_rel`, `runForkHidG2_rel`, `runFree_of_rel`, `layerFree`.

Not claimed: the other three statements. Nothing on a run on a view. That the two lists have as many
tokens, and that both or neither have a token from V on, are premises of `LayerFree`. For proofs
only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFree

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Layer

/-! ## Claims on the weights that are alike -/

/-- Two factors have the same sizes. -/
def FacAlike (x x' : WsFac) : Prop :=
  x.HV.size = x'.HV.size ∧ x.pt.size = x'.pt.size ∧ x.AV.size = x'.AV.size

/-- Two claims: one unit, factors of the same sizes. -/
def ClaimAlike (c c' : WsClaim) : Prop := c.ui = c'.ui ∧ All2 FacAlike c.f c'.f

/-- Two values that may be missing: both are, or neither is and they are in R. -/
def OptRel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some a, some a' => R a a'
  | _, _ => False

theorem fits_alike {x x' : WsFac} (h : FacAlike x x') (g : WsGrp) : x.fits g = x'.fits g := by
  unfold WsFac.fits Array.isEmpty
  rw [h.1, h.2.1, h.2.2]

theorem all_zip_alike {α β γ : Type} {R : α → β → Prop} {p : α × γ → Bool} {q : β × γ → Bool}
    (hp : ∀ a b c, R a b → p (a, c) = q (b, c)) {l : List α} {l' : List β} (h : All2 R l l') :
    ∀ gs : List γ, (l.zip gs).all p = (l'.zip gs).all q := by
  induction h with
  | nil => intro gs; rfl
  | cons h0 _ ih =>
    intro gs
    cases gs with
    | nil => rfl
    | cons g gs => simp only [List.zip_cons_cons, List.all_cons, hp _ _ _ h0, ih gs]

theorem all2_zip_map {α β γ δ ε : Type} {R : α → β → Prop} {S : δ → ε → Prop} {f : α × γ → δ}
    {f' : β × γ → ε} (hf : ∀ a b c, R a b → S (f (a, c)) (f' (b, c))) {l : List α} {l' : List β}
    (h : All2 R l l') : ∀ gs : List γ, All2 S ((l.zip gs).map f) ((l'.zip gs).map f') := by
  induction h with
  | nil => intro gs; exact .nil
  | cons h0 _ ih =>
    intro gs
    cases gs with
    | nil => exact .nil
    | cons g gs =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact .cons (hf _ _ _ h0) (ih gs)

theorem all_alike {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hp : ∀ a b, R a b → p a = q b) {l : List α} {l' : List β} (h : All2 R l l') :
    l.all p = l'.all q := by
  induction h with
  | nil => rfl
  | cons h0 _ ih => simp only [List.all_cons, hp _ _ h0, ih]

theorem shape_alike (lay : WsLay) {c c' : WsClaim} (h : ClaimAlike c c') :
    wsClaimShape lay c = wsClaimShape lay c' := by
  unfold wsClaimShape
  rw [h.1]
  cases lay.U[c'.ui]? with
  | none => rfl
  | some u =>
    dsimp only
    rw [h.2.length, all_zip_alike (p := fun y => y.1.fits y.2) (q := fun y => y.1.fits y.2)
      (fun a b g hab => fits_alike hab g) h.2]

theorem length_filterMap_if {α β : Type} (p : α → Bool) (f f' : α → β) (l : List α) :
    (l.filterMap fun i => if p i = true then none else some (f i)).length =
      (l.filterMap fun i => if p i = true then none else some (f' i)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    by_cases hp : p a = true
    · simp only [hp, if_true]
      exact ih
    · simp only [hp, Bool.false_eq_true, if_false, List.length_cons, ih]

theorem onRows_alike {x x' : WsFac} (h : FacAlike x x') (g : WsGrp) :
    RowFacAlike (x.onRows g) (x'.onRows g) := by
  unfold WsFac.onRows
  split
  · exact ⟨h.1, by simp only [List.size_toArray]; exact length_filterMap_if _ _ _ _, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, h.2.2⟩

theorem rowPart_alike (lay : WsLay) {c c' : WsClaim} (h : ClaimAlike c c') (ka ka' : E) :
    RecAlike (wsRowPart lay c ka) (wsRowPart lay c' ka') := by
  unfold wsRowPart
  rw [h.1]
  cases lay.U[c'.ui]? with
  | none => exact ⟨rfl, .nil⟩
  | some u =>
    exact ⟨rfl, all2_zip_map (f := fun y => y.1.onRows y.2) (f' := fun y => y.1.onRows y.2)
      (fun a b g hab => onRows_alike hab g) h.2 u.g⟩

/-! ## The two layers above blocks, with equal states -/

/-- How two routines of a sub-proof's check are compared: from one state. -/
abbrev cmpS : Cmp SubM := Cmp.state Eq Cmp.blk

/-- How two routines of a link are compared: from one context of the link and one state. -/
abbrev cmpL : Cmp LinkM := Cmp.state Eq cmpS

theorem same_cmpS : cmpS.Same := same_state same_blk

theorem same_cmpL : cmpL.Same := same_state same_cmpS

/-- `form` at two values that may be missing. -/
theorem form_rel {α : Type} {R : α → α → Prop} {x x' : Option α} (h : OptRel R x x') :
    cmpS.Rel R (form x) (form x') := by
  cases x with
  | none =>
    cases x' with
    | none => exact fun _ _ _ _ _ => trivial
    | some a' => exact h.elim
  | some a =>
    cases x' with
    | none => exact h.elim
    | some a' =>
      intro s s' hs c _
      exact ⟨⟨h, hs⟩, rfl⟩

/-- **The end of a sub-proof's claims on the weights**, at two lists of claims that are alike. -/
theorem wsForkEnd_rel (lay : WsLay) {l l' : List WsClaim} (h : All2 ClaimAlike l l')
    (sv : Array Nat) :
    cmpS.Rel OutAlike (wsForkEnd lay l.toArray sv) (wsForkEnd lay l'.toArray sv) := by
  unfold wsForkEnd
  have e1 : (!l.toArray.isEmpty && decide (l.toArray.size ≤ 4096) && sv.size == l.toArray.size) =
      (!l'.toArray.isEmpty && decide (l'.toArray.size ≤ 4096) && sv.size == l'.toArray.size) := by
    simp only [Array.isEmpty, List.size_toArray, h.length]
  have e2 : (l.toArray.all fun c => decide (c.ui < lay.U.size)) =
      (l'.toArray.all fun c => decide (c.ui < lay.U.size)) := by
    simp only [List.all_toArray]
    exact all_alike (fun a b hab => by rw [hab.1]) h
  have e3 : (l.toArray.all fun c => (wsClaimShape lay c).isOk) =
      (l'.toArray.all fun c => (wsClaimShape lay c).isOk) := by
    simp only [List.all_toArray]
    exact all_alike (fun a b hab => by rw [shape_alike lay hab]) h
  rw [e1, e2, e3]
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun x => ?_
  obtain ⟨o, rho⟩ := x
  refine cmpS.pure' ⟨rfl, ?_⟩
  dsimp only
  rw [Array.toList_zip, Array.toList_zip]
  exact all2_zip_map (f := fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    (f' := fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    (fun a b c hab => rowPart_alike lay hab _ _) h _

/-! ## The embedding's claim -/

theorem size_foldl_modify {α : Type} (i : α → Nat) (g : α → E → E) :
    ∀ (l : List α) (init : Array E),
      (l.foldl (fun a t => a.modify (i t) (g t)) init).size = init.size
  | [], _ => rfl
  | t :: l, init => by
      rw [List.foldl_cons, size_foldl_modify i g l, Array.size_modify]

theorem mapM_opt_rel {α β : Type} {R : β → β → Prop} {f f' : α → Option β}
    (h : ∀ a, OptRel R (f a) (f' a)) : ∀ l : List α, OptRel (All2 R) (l.mapM f) (l.mapM f')
  | [] => by
      rw [List.mapM_nil, List.mapM_nil]
      exact .nil
  | a :: l => by
      rw [List.mapM_cons, List.mapM_cons]
      have h0 := h a
      have h1 := mapM_opt_rel h l
      revert h0 h1
      cases f a <;> cases f' a <;> cases l.mapM f <;> cases l.mapM f' <;> intro h0 h1 <;>
        first
          | trivial
          | exact h0.elim
          | exact h1.elim
          | exact All2.cons h0 h1

theorem FacAlike.refl (x : WsFac) : FacAlike x x := ⟨rfl, rfl, rfl⟩

theorem OptRel.refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) : ∀ x : Option α, OptRel R x x
  | none => trivial
  | some a => h a

theorem optRel_bind {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : Option α}
    {f f' : α → Option β} (hx : OptRel S x x') (hf : ∀ a a', S a a' → OptRel R (f a) (f' a')) :
    OptRel R (x >>= f) (x' >>= f') := by
  cases x <;> cases x'
  · trivial
  · exact hx.elim
  · exact hx.elim
  · exact hf _ _ hx

theorem optRel_map {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {x x' : Option α}
    {f : α → β} (hx : OptRel R x x') (hf : ∀ a a', R a a' → S (f a) (f a')) :
    OptRel S (x.map f) (x'.map f) := by
  cases x <;> cases x'
  · trivial
  · exact hx.elim
  · exact hx.elim
  · exact hf _ _ hx

theorem optRel_bind_same {α β : Type} {R : β → β → Prop} {x : Option α} {f f' : α → Option β}
    (hf : ∀ a, OptRel R (f a) (f' a)) : OptRel R (x >>= f) (x >>= f') := by
  cases x
  · trivial
  · exact hf _

/-- **The embedding's claim at two lists of tokens**: both are missing, or neither is and they are
alike. -/
theorem claimE_alike (c : ClaimEnv) (ZE tkh : Array E) (V : Nat) {t t' : Array Nat}
    (hs : t.size = t'.size) (ha : t.any (· ≥ V) = t'.any (· ≥ V)) :
    OptRel ClaimAlike (c.claimE ZE tkh V t) (c.claimE ZE tkh V t') := by
  unfold ClaimEnv.claimE
  rw [ha, hs]
  dsimp only
  by_cases hc : (t'.size != c.v.y.T || t'.any fun x => decide (x ≥ V)) = true
  · simp only [hc, if_true]
    trivial
  · simp only [hc, Bool.false_eq_true, if_false]
    refine optRel_bind_same fun _ => ?_
    refine optRel_bind_same fun ui => ?_
    refine optRel_bind_same fun u => ?_
    refine optRel_bind_same fun x => ?_
    obtain ⟨low, tok⟩ := x
    dsimp only
    refine optRel_bind (S := All2 FacAlike) (mapM_opt_rel (fun G => ?_) _)
      fun f f' hf => ⟨rfl, hf⟩
    split
    · refine ⟨rfl, rfl, ?_⟩
      show Array.size _ = Array.size _
      rw [size_foldl_modify, size_foldl_modify]
    · exact OptRel.refl FacAlike.refl _

/-! ## The sub-proof's own messages, in the first group -/

/-- Two values of `hearOwn`: all is equal but what is left of each claim on the weights. -/
def OwnAlike (o o' : Own) : Prop :=
  ∃ r', o' = { o with wo := { o.wo with recs := r' } } ∧ All2 RecAlike o.wo.recs r'

theorem ClaimAlike.refl (c : WsClaim) : ClaimAlike c c := ⟨rfl, All2.refl FacAlike.refl _⟩

theorem hearOwn_rel (P : Pub) {t t' : Array Nat} (hs : t.size = t'.size)
    (ha : t.any (· ≥ P.V) = t'.any (· ≥ P.V)) (hp : HPlan2) (fo : Forest.Heard) :
    cmpS.Rel OwnAlike (hearOwn { P with tokv := t } hp 0 fo)
      (hearOwn { P with tokv := t' } hp 0 fo) := by
  unfold hearOwn
  dsimp only
  repeat (refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_)
  rename_i cP
  simp only [beq_self_eq_true, if_true]
  refine cmpS.bind' (S := All2 ClaimAlike) (by keeps) (form_rel ?_) fun y y' hy => ?_
  · exact optRel_map (claimE_alike _ _ _ _ hs ha) fun _ _ h => .cons h .nil
  have hall : All2 ClaimAlike (cP ++ y) (cP ++ y') := (All2.refl ClaimAlike.refl _).append hy
  rw [show (cP ++ y).toArray.size = (cP ++ y').toArray.size by
    simp only [List.size_toArray, hall.length]]
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun sVE => ?_
  refine cmpS.bind' (by keeps) (wsForkEnd_rel _ hall _) fun wo wo' hw => ?_
  obtain ⟨m, r⟩ := wo
  obtain ⟨m', r'⟩ := wo'
  obtain ⟨e, hr⟩ := hw
  have e' : m = m' := e
  subst e'
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  exact cmpS.pure' ⟨r', rfl, hr⟩

/-! ## The check of a group of layers -/

/-- A routine of the sub-proof's engine, used inside a link. -/
theorem sub_rel {α : Type} {R : α → α → Prop} {x x' : SubM α} (hk : Over.K x)
    (hx : cmpS.Rel R x x') : cmpL.Rel R (LinkM.sub x) (LinkM.sub x') := by
  intro C C' hC
  subst hC
  exact cmpS.bind' hk hx fun _ _ h => cmpS.pure' ⟨h, rfl⟩

theorem runForkHidG2_rel (P : Pub) {t t' : Array Nat} (hs : t.size = t'.size)
    (ha : t.any (· ≥ P.V) = t'.any (· ≥ P.V)) (hp : HPlan2) (g : Nat) :
    cmpL.Rel OutAlike (runForkHidG2 { P with tokv := t } hp g)
      (runForkHidG2 { P with tokv := t' } hp g) := by
  cases g with
  | succ g =>
    have e : runForkHidG2 { P with tokv := t } hp (g + 1) =
        runForkHidG2 { P with tokv := t' } hp (g + 1) := rfl
    rw [e]
    exact cmpL.refl same_cmpL OutAlike.refl _
  | zero =>
    unfold runForkHidG2
    dsimp only
    iterate 6 (refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_)
    refine cmpL.bind' (S := OwnAlike) (by keeps)
      (sub_rel (by keeps) (cmpS.bind_same same_cmpS (by keeps) fun fo => hearOwn_rel P hs ha hp fo))
      fun o o' ho => ?_
    obtain ⟨r', e, hr⟩ := ho
    subst e
    dsimp only
    repeat (refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_)
    exact cmpL.pure' ⟨rfl, hr⟩

/-- From the relation of the layers above to the relation of two checks of a link. -/
theorem runFree_of_rel {r r' : LinkM WsForkOut} (hk : Over.K r) (h : cmpL.Rel OutAlike r r') :
    RunFree (some <$> r) (some <$> r') := fun C F =>
  relB_mono (fun _ _ k => ⟨k.1.1, k.1.2, fun _ _ => by rw [k.2]⟩)
    ((cmpL.map (R := OptAlike) (f := some) (f' := some) hk h fun _ _ k => k) C C rfl F F rfl)

/-- **The check of a group of layers at two lists of tokens.** -/
theorem layerFree : LayerFree := fun P _ _ hp g hs ha =>
  runFree_of_rel (by keeps) (runForkHidG2_rel P hs ha hp g)

end OnBytes.Flat
