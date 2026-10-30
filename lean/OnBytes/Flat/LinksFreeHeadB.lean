-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadB.lean: the two groups of the head's claims that hold values made of the
request, `claimJoin` and `claimPolicy` (OnBytes/Model/Head.lean), at two requests.

Where the request stands in a form, by the program's text, and here by theorems: in the constant
alone. `gapAt`, `middleDigit` and `lowDigit` take an element made of the request and lay it into
`Aff.ofConst`; `LINE` does so in three of its branches; every other operation on forms is
`Aff.addMul` under a factor that is the same at both requests. So the two forms agree in their
entries and in their part on the slots (`AffC`), and adding them keeps the states alike (`lin_rel`,
over `lin_alike` of OnBytes/Flat/LinksFreeFork.lean).

How the comparison goes: from states that are alike (`cmpA`). A routine that does not read the
covered positions, the checked tokens or the tables' weights is the same term at both requests up to
unfolding, and OnBytes/Flat/LinksRespBank.lean has that it gives the same from two such states
(`cmpA_same`, `cmpA_refl`).

Main definitions: `AffC`, `AffsC`, `LinesRel`, `KeysRel`. Main theorems: `affC_addMul`, `affC_add`,
`affC_sub`, `affC_scale`, `affC_const`; `RunAlike.open`; `gapAt_rel`, `middleDigit_rel`,
`lowDigit_rel`, `LINE_rel`, `keyForm_rel`, `join_rel`, `claimJoin_rel`, `claimPolicy_rel`.

Not claimed: anything on a run on a view. For proofs only; no module of the program imports this
file.


-/
import OnBytes.Flat.LinksFreeHeadA

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-! ## Forms that differ in the constant alone -/

/-- Two forms agree in all but the constant. -/
def AffC (a a' : Aff) : Prop := a' = { a with const := a'.const }

theorem AffC.refl (a : Aff) : AffC a a := rfl

theorem AffC.alike {a a' : Aff} (h : AffC a a') : AffAlike a a' := by
  unfold AffC at h
  rw [h]
  exact ⟨rfl, rfl⟩

theorem affC_const (v v' : E) : AffC (Aff.ofConst v) (Aff.ofConst v') := rfl

theorem affC_addMul {a a' b b' : Aff} (ha : AffC a a') (hb : AffC b b') (k : E) :
    AffC (a.addMul b k) (a'.addMul b' k) := by
  unfold AffC at ha hb
  generalize a'.const = c at ha
  generalize b'.const = d at hb
  subst ha hb
  rfl

theorem affC_add {a a' b b' : Aff} (ha : AffC a a') (hb : AffC b b') : AffC (a + b) (a' + b') :=
  affC_addMul ha hb _

theorem affC_sub {a a' b b' : Aff} (ha : AffC a a') (hb : AffC b b') : AffC (a - b) (a' - b') :=
  affC_addMul ha hb _

theorem affC_scale {a a' : Aff} (ha : AffC a a') (k : E) : AffC (a.scale k) (a'.scale k) :=
  affC_addMul (AffC.refl _) ha k

/-! ## Steps of a comparison from states that are alike -/

/-- One and the same such routine, at a relation that holds of every value with itself. -/
theorem cmpA_refl {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) {x : SubM α} (h : Resp.K x) :
    cmpA.Rel R x x := cmpA.mono' (fun a a' e => by subst e; exact hR a) (resp_sub h).2

/-- `SubM.lin` at two forms that differ in the constant. -/
theorem lin_rel {a a' : Aff} (h : AffC a a') : cmpA.Rel Eq (SubM.lin a) (SubM.lin a') :=
  change_rel fun _ _ hF => lin_alike hF h.alike

/-- R' is R with other covered positions, other checked tokens and other weights of the tables. -/
theorem RunAlike.open {R R' : Head.Run} (h : RunAlike R R') :
    ∃ (cov' : Covered) (w' : Array Nat) (f' : Array HFun),
      R' = { R with cov := cov', x := { R.x with win := w' }, t := { R.t with funs := f' } } := by
  obtain ⟨e, -, ⟨ex, -⟩, ⟨et, -⟩⟩ := h
  refine ⟨R'.cov, R'.x.win, R'.t.funs, ?_⟩
  rw [← ex, ← et]
  exact e

/-! ## The forms that hold a value made of the request -/

theorem gapAt_rel {R R' : Head.Run} (hR : RunAlike R R') (P : String) (i : Nat) (w w' : E) :
    cmpA.Rel AffC (gapAt R P i w) (gapAt R' P i w') := by
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold gapAt
  dsimp only
  refine cmpA_same (by resp) fun t => ?_
  refine cmpA.bind' (S := AffC) (by keeps)
    (cmpA.forIn_range (fun _ _ => by keeps) (fun l s s' hs => ?_) _ (AffC.refl _))
    fun s s' hs => cmpA.pure' hs
  refine cmpA_same (by resp) fun u => ?_
  refine cmpA_same (by resp) fun _ => ?_
  exact cmpA.pure' (R := StepRel AffC)
    (affC_addMul hs (affC_add (AffC.refl u) (affC_const _ _)) _)

theorem middleDigit_rel {R R' : Head.Run} (hR : RunAlike R R') (sn : String) (w w' : E) :
    cmpA.Rel AffC (middleDigit R sn w) (middleDigit R' sn w') := by
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold middleDigit
  dsimp only
  refine cmpA_same (by resp) fun u => ?_
  exact cmpA.pure' (affC_add (affC_const _ _) (AffC.refl u))

theorem lowDigit_rel {R R' : Head.Run} (hR : RunAlike R R') (sn : String) (w w' : E) :
    cmpA.Rel AffC (lowDigit R sn w) (lowDigit R' sn w') := by
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold lowDigit
  dsimp only
  refine cmpA_same (by resp) fun u => ?_
  exact cmpA.pure' (affC_add (affC_const _ _) (AffC.refl u))

theorem LINE_rel {R R' : Head.Run} (hR : RunAlike R R') (sn : String) :
    cmpA.Rel AffC (LINE R sn) (LINE R' sn) := by
  have hR0 := hR
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold LINE
  dsimp only
  refine cmpA_same (by resp) fun ew => ?_
  split
  · exact cmpA_refl AffC.refl (by resp)
  split
  · exact cmpA_refl AffC.refl (by resp)
  split
  · refine cmpA_same (by resp) fun zt => ?_
    split
    · exact middleDigit_rel hR0 _ _ _
    split
    · exact lowDigit_rel hR0 _ _ _
    refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun g0 g0' h0 => ?_
    refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun g1 g1' h1 => ?_
    refine cmpA.bind' (by keeps) (middleDigit_rel hR0 _ _ _) fun m m' hm => ?_
    refine cmpA.bind' (by keeps) (lowDigit_rel hR0 _ _ _) fun l l' hl => ?_
    exact cmpA.pure' (affC_scale (affC_sub (affC_sub (affC_sub
      (affC_add (AffC.refl _) (affC_scale (affC_add h0 (affC_scale h1 _)) _)) (affC_const _ _))
      (affC_scale hm _)) hl) _)
  split
  · refine cmpA_same (by resp) fun zt => ?_
    refine cmpA_same (by resp) fun s1 => ?_
    refine cmpA_same (by resp) fun s2 => ?_
    exact cmpA.pure' (affC_add (affC_add (affC_const _ _) (AffC.refl _)) (AffC.refl _))
  split
  · exact cmpA_refl AffC.refl (by resp)
  split
  · exact cmpA_refl AffC.refl (by resp)
  · exact cmpA_refl AffC.refl (by resp)

/-- The state of `keyForm`'s first loop: the form so far, and the marks on the columns. -/
def LinesRel (r r' : MProd Aff (Array Nat)) : Prop := AffC r.fst r'.fst ∧ r.snd = r'.snd

theorem keyForm_rel {R R' : Head.Run} (hR : RunAlike R R') (q : Nat) (laid : Array Nat) :
    cmpA.Rel (fun p p' => AffC p.1 p'.1 ∧ p.2 = p'.2) (keyForm R q laid) (keyForm R' q laid) := by
  have hR0 := hR
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold keyForm
  dsimp only
  refine cmpA.bind' (S := LinesRel) (by keeps)
    (cmpA.forIn_list (fun _ _ => by keeps) (fun g r r' hr => ?_) _ ⟨AffC.refl _, rfl⟩)
    fun r r' hr => ?_
  · obtain ⟨a, w⟩ := r
    obtain ⟨a', w'⟩ := r'
    obtain ⟨ha, hw⟩ := hr
    have hw' : w = w' := hw
    subst hw'
    refine cmpA.bind' (by keeps) (LINE_rel hR0 _) fun l l' hl => ?_
    refine cmpA_same (by resp) fun w2 => ?_
    refine cmpA_same (by resp) fun _ => ?_
    exact cmpA.pure' (show StepRel LinesRel (.yield _) (.yield _) from ⟨affC_add ha hl, rfl⟩)
  · obtain ⟨a, w⟩ := r
    obtain ⟨a', w'⟩ := r'
    obtain ⟨ha, hw⟩ := hr
    have hw' : w = w' := hw
    subst hw'
    refine cmpA_same (by resp) fun r1 => ?_
    exact cmpA.pure' ⟨affC_add (AffC.refl _) ha, rfl⟩

/-- Two lists of forms, member by member. -/
def AffsC (K K' : Array Aff) : Prop := All2 AffC K.toList K'.toList

theorem all2_getElem? {α : Type} {R : α → α → Prop} {l l' : List α} (h : All2 R l l') :
    ∀ c : Nat, OptRel R l[c]? l'[c]? := by
  induction h with
  | nil => intro c; trivial
  | cons h0 _ ih =>
    intro c
    cases c with
    | zero => exact h0
    | succ c => simpa only [List.getElem?_cons_succ] using ih c

theorem affsC_getD {K K' : Array Aff} (h : AffsC K K') (c : Nat) (d : Aff) :
    AffC (K.getD c d) (K'.getD c d) := by
  have h0 := all2_getElem? h c
  rw [Array.getElem?_toList, Array.getElem?_toList] at h0
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  revert h0
  cases K[c]? <;> cases K'[c]? <;> intro h0
  · exact AffC.refl d
  · exact h0.elim
  · exact h0.elim
  · exact h0

theorem join_rel (g : Forest.Heard) {K K' : Array Aff} (h : AffsC K K') :
    cmpA.Rel AffC (Forest.join g K) (Forest.join g K') := by
  have hs : K.size = K'.size := by
    have := h.length
    simpa only [Array.length_toList] using this
  unfold Forest.join
  dsimp only
  rw [← hs]
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.pure' (affC_sub (affC_add ?_ (AffC.refl _)) (AffC.refl _))
  have key : ∀ (l : List Nat) (f f' : Aff), AffC f f' →
      AffC (l.foldl (fun (f : Aff) c =>
          Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
            K.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE)) f)
        (l.foldl (fun (f : Aff) c =>
          Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
            K'.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE)) f') := by
    intro l
    induction l with
    | nil => exact fun _ _ hf => hf
    | cons c l ih =>
      intro f f' hf
      exact ih _ _ (affC_addMul hf (affC_sub (AffC.refl _) (affsC_getD h c _)) _)
  exact key _ _ _ (AffC.refl _)

/-- The state of `claimJoin`'s loop: the forms so far, and the counts of places. -/
def KeysRel (r r' : MProd (Array Aff) (Array Nat)) : Prop := AffsC r.fst r'.fst ∧ r.snd = r'.snd

theorem claimJoin_rel {R R' : Head.Run} (hR : RunAlike R R') :
    cmpA.Rel Eq (claimJoin R) (claimJoin R') := by
  have hR0 := hR
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold claimJoin
  dsimp only
  refine cmpA.bind' (S := KeysRel) (by keeps)
    (cmpA.forIn_range (fun _ _ => by keeps) (fun q r r' hr => ?_) _ ⟨.nil, rfl⟩) fun r r' hr => ?_
  · obtain ⟨K, w⟩ := r
    obtain ⟨K', w'⟩ := r'
    obtain ⟨hK, hw⟩ := hr
    have hw' : w = w' := hw
    subst hw'
    refine cmpA.bind' (by keeps) (keyForm_rel hR0 q w) fun p p' hp => ?_
    refine cmpA_same (by resp) fun _ => ?_
    refine cmpA.pure' (show StepRel KeysRel (.yield _) (.yield _) from ⟨?_, hp.2⟩)
    show All2 AffC (Array.push _ _).toList (Array.push _ _).toList
    rw [Array.toList_push, Array.toList_push]
    exact All2.append hK (.cons hp.1 .nil)
  · obtain ⟨K, w⟩ := r
    obtain ⟨K', w'⟩ := r'
    obtain ⟨hK, hw⟩ := hr
    have hw' : w = w' := hw
    subst hw'
    refine cmpA_same (by resp) fun _ => ?_
    exact cmpA.bind' (by keeps) (join_rel _ hK) fun a a' ha => lin_rel ha

theorem claimPolicy_rel {R R' : Head.Run} (hR : RunAlike R R') :
    cmpA.Rel Eq (claimPolicy R) (claimPolicy R') := by
  have hR0 := hR
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold claimPolicy
  dsimp only
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun a0 a0' h0 => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun a1 a1' h1 => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun a2 a2' h2 => ?_
  refine cmpA.bind' (by keeps)
    (lin_rel (affC_sub (affC_add (affC_add h0 (affC_scale h1 _)) h2) (affC_const _ _)))
    fun _ _ _ => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun b1 b1' k1 => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun b4 b4' k4 => ?_
  refine cmpA.bind' (by keeps) (lin_rel (affC_sub (affC_add k1 k4) (affC_const _ _)))
    fun _ _ _ => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun c0 c0' m0 => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun c3 c3' m3 => ?_
  refine cmpA.bind' (by keeps) (lin_rel (affC_sub (affC_add m0 m3) (affC_const _ _)))
    fun _ _ _ => ?_
  refine cmpA_same (by resp) fun te => ?_
  refine cmpA.bind' (by keeps) (gapAt_rel hR0 _ _ _ _) fun c5 c5' m5 => ?_
  refine cmpA.bind' (S := AffC) (by keeps)
    (cmpA.forIn_range (fun _ _ => by keeps) (fun l r r' hr => ?_) _
      (affC_add m5 (affC_const _ _))) fun r r' hr => lin_rel hr
  refine cmpA.bind' (S := AffC) (by keeps)
    (cmpA.forIn_range (fun _ _ => by keeps) (fun xh r r' hr => ?_) _ hr) fun r r' hr => ?_
  · refine cmpA_same (by resp) fun u => ?_
    refine cmpA_same (by resp) fun _ => ?_
    exact cmpA.pure' (show StepRel AffC (.yield _) (.yield _) from
      affC_addMul hr (AffC.refl u) _)
  · refine cmpA_same (by resp) fun _ => ?_
    exact cmpA.pure' (show StepRel AffC (.yield _) (.yield _) from hr)

end OnBytes.Flat
