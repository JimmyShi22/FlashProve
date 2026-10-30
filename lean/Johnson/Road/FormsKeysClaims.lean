-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysClaims.lean: which forms a stretch of a layer sub-proof's check adds as
claims.

The check of a layer sub-proof (runForkHidG2 in OnBytes/Model/Layer.lean) adds its claims one by
one: each call of SubM.lin puts the next power of one drawn element, theta, times a form into the
coefficients of one equation. The state (Fork in OnBytes/Model/Hide.lean) keeps these coefficients;
it keeps no list of the forms. To say "all claims hold", or "this form is among the claims", one
needs the list. This file writes, for five stretches of the check, the list as a function of what
the verifier holds, and shows that a run of the stretch does to the equation's coefficients what
adding that list does.

The five stretches are those behind the identities of a feed-forward segment: claimsNorms,
claimRowBatch, claimsLedger5, claimsOneHot, claimEmbedding. What their forms are worth is shown in
Johnson/Road/FormsKeysIdnW.lean and FormsKeysIdnL.lean.

How a statement reads. sumOf F is the state F without four fields: what was shown under the slots
(vp, mf, gotF) and the list of owed claims. What Fork.lin does to the other fields does not depend
on these four (lin_sumOf). They are set aside because a stretch may turn them: the routine that
makes a sumcheck's claim (pscRow) puts the coefficients of the hiding polynomial under their slots,
and claimsLedger5 calls it.
AddsV m P ol says: whenever the routine m returns, from any state F and context, with a value a and
a state G, then a has the property P, the list ol is there, say l, and
(sumOf F).lins l = some (sumOf G). AddsL is the case of a routine without a value. A run is written
as in Johnson/Road/FormsKeysSubM.lean: (m F).Yields c (a, G) c'; runs_iff there turns it into the
equation m F c = .ok ((a, G), c').

Main definitions: sumOf; AddsV, AddsL, appL; the lists normsL, ledgerL (with ledS0, shownL, carryL,
linesL), oneHotL, embL.
Main theorems.
 - lin_sumOf, hideRun_sumOf.
 - The rules, by which AddsV passes through the text of a routine: addsV_pure, addsV_keep,
   addsV_bind, addsV_after, addsV_before, addsV_tail, addsV_pure_bind, addsV_form, addsV_mustAs,
   addsV_yield, addsV_pscRow; addsL_lin, addsL_forM, addsL_forIn (a loop with any step).
 - The stretches: adds_claimsNorms, adds_claimRowBatch, adds_claimsLedger5, adds_claimsOneHot,
   adds_claimEmbedding; adds_noteClaims.
 - The members: mem_normsL, mem_ledger_row, mem_ledger_shown, mem_ledger_carry, mem_ledger_line,
   mem_oneHotL.
 - lins_trans (one stretch after another); total_of_lins (what a list does to Fork.total).

In claimsLedger5 one form is made from values that the routine reads off the state: the shown end
values of the token sumcheck of the row products. So its list has them as an argument, sh, and
adds_claimsLedger5 says that there is such an sh, returned by the verifier's own shownRun from the
state in which the stretch began.

What is compared with what: the verifier's text with itself, through lists that are this file's own.

What is reused: lins_append of Johnson/Road/HeadKit.lean. Johnson/Road/HeadWalk.lean has rules of
this kind for the head's check; there the lists are not named and the states are compared whole.

Hypotheses that no theorem concludes: that the stretch returns.
Johnson/Road/FormsKeysClaimsRun.lean
runs the five stretches from a made-up state.

What is not claimed. Nothing on the worth of a form, on theta's draw or on soundness. The nine other
stretches of the check are not treated, the smallness test's among them, whose claims are added by
another routine and read theta. That the total is 0 and no claim is counted where the claims begin
is not shown. The caller is not walked: each theorem takes one run of one stretch. The program does
not import this file.
-/
import Johnson.Road.FormsKeysSubM
import Johnson.Road.FormsKeysIdnL
import Johnson.Road.HeadKit

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Fork SubM Aff Psc pscRow layerObject ledCarry5 ledLines5 ledProducts5 Row5)
open OnBytes.Model.Layer (Env Lay Heard Pub form shownRun claimsNorms claimRowBatch claimsLedger5
  claimsOneHot claimEmbedding epsOf twoM)

/-! ## The part of a state that the one equation is made of -/

/-- The state without what was shown under the slots and without the list of owed claims. What
Fork.lin does to the other fields does not depend on these four (lin_sumOf); putting a value under a
slot turns nothing else (hideRun_sumOf). -/
def sumOf (F : Fork) : Fork := { F with vp := #[], mf := #[], gotF := #[], owed := #[] }

/-- Handing out a weight does not read the four fields. -/
theorem kapTake_sumOf (F : Fork) (n : ℕ) :
    (sumOf F).kapTake n = (F.kapTake n).map fun x => (x.1, sumOf x.2) := by
  unfold Fork.kapTake
  have e : (sumOf F).kapAt n = F.kapAt n := rfl
  show (if F.doorShutF = true then none
    else if F.kapMapF.isEmpty = true then ((sumOf F).kapAt n).map fun k => (k, sumOf F)
    else if (decide (n < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
        !F.kapMapF.getD n true) = true then
      ((sumOf F).kapAt n).map fun k => (k, { sumOf F with kapMapF := F.kapMapF.set! n true })
    else none) = _
  rw [e]
  split_ifs <;> first | rfl | (cases F.kapAt n <;> rfl)

/-- The next claim's weight. -/
theorem kap_sumOf (F : Fork) : (sumOf F).kap = F.kap.map fun x => (x.1, sumOf x.2) := by
  unfold Fork.kap
  have e : (sumOf F).nClaim = F.nClaim := rfl
  rw [e, kapTake_sumOf]
  cases F.kapTake F.nClaim <;> rfl

/-- Adding a multiple of a form does not read the four fields. -/
theorem push_sumOf (F : Fork) (w : E) (a : Aff) :
    (sumOf F).push w a = (F.push w a).map sumOf := by
  have e1 : (sumOf F).push w a = (if F.doorShutF = true then none
    else match a.ents.foldlM (Model.Fork.pushEnt w) F.trees,
        a.slots.foldlM (Model.Fork.pushSlot w F.ns) F.LS with
      | some trees', some LS' =>
        some { sumOf F with trees := trees', LS := LS', c0 := addE F.c0 (mulE w a.const) }
      | _, _ => none) := rfl
  have e2 : F.push w a = (if F.doorShutF = true then none
    else match a.ents.foldlM (Model.Fork.pushEnt w) F.trees,
        a.slots.foldlM (Model.Fork.pushSlot w F.ns) F.LS with
      | some trees', some LS' =>
        some { F with trees := trees', LS := LS', c0 := addE F.c0 (mulE w a.const) }
      | _, _ => none) := rfl
  rw [e1, e2]
  split_ifs
  · rfl
  · generalize a.ents.foldlM (Model.Fork.pushEnt w) F.trees = X
    generalize a.slots.foldlM (Model.Fork.pushSlot w F.ns) F.LS = Y
    cases X <;> cases Y <;> rfl

/-- Adding a claim does not read the four fields. -/
theorem lin_sumOf (F : Fork) (f : Aff) : (sumOf F).lin f = (F.lin f).map sumOf := by
  unfold Fork.lin
  rw [kap_sumOf]
  cases F.kap with
  | none => rfl
  | some x => exact push_sumOf x.2 x.1 f

/-- Putting a value under a slot turns none but the four fields. -/
theorem hide_sumOf {F G : Fork} {j : ℕ} {x k : E} (h : F.hide j x k = some G) :
    sumOf G = sumOf F := by
  unfold Fork.hide at h
  split_ifs at h
  cases h
  rfl

/-- The same for a run of values. -/
theorem hideRun_sumOf {F G : Fork} {first : ℕ} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : sumOf G = sumOf F := by
  have key : ∀ (l : List E) (s t : ℕ × Fork), l.foldlM (Model.Fork.hideStep k) s = some t →
      sumOf t.2 = sumOf s.2 := by
    intro l
    induction l with
    | nil =>
      intro s t h
      cases h
      rfl
    | cons y l ih =>
      intro s t h
      rw [List.foldlM_cons] at h
      obtain ⟨u, hu, h⟩ := bind_some h
      obtain ⟨H, hH, e⟩ := map_some hu
      rw [ih u t h, ← e]
      exact hide_sumOf hH
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hx : v.toList.foldlM (Model.Fork.hideStep k) (first, F) with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    cases h
    exact key _ _ _ hx

/-! ## What a routine adds -/

/-- The routine m adds the claims of the list and returns a value with the property P: whenever it
returns, the value has P, the list is there, and the part of the state that the one equation is made
of has become what Fork.lins makes of it with that list. -/
def AddsV {α : Type} (m : SubM α) (P : α → Prop) (ol : Option (List Aff)) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx) (a : α), (m F).Yields c (a, G) c' →
    P a ∧ ∃ l, ol = some l ∧ (sumOf F).lins l = some (sumOf G)

/-- The same for a routine that returns no value. -/
abbrev AddsL (m : SubM Unit) (ol : Option (List Aff)) : Prop := AddsV m (fun _ => True) ol

/-- Two lists that may be missing, one after the other. -/
def appL (a b : Option (List Aff)) : Option (List Aff) := a.bind fun x => b.map (x ++ ·)

/-- A member of the first list is a member of the whole. -/
theorem mem_appL_left {a b : Option (List Aff)} {l x : List Aff} {y : Aff}
    (h : appL a b = some l) (ha : a = some x) (hy : y ∈ x) : y ∈ l := by
  subst ha
  obtain ⟨z, -, e⟩ := map_some h
  rw [← e]
  exact List.mem_append_left _ hy

/-- A member of the second list is a member of the whole. -/
theorem mem_appL_right {a b : Option (List Aff)} {l x : List Aff} {y : Aff}
    (h : appL a b = some l) (hb : b = some x) (hy : y ∈ x) : y ∈ l := by
  subst hb
  obtain ⟨z, -, h⟩ := bind_some h
  cases h
  exact List.mem_append_right _ hy

/-- If the whole is there, so are both lists. -/
theorem appL_some {a b : Option (List Aff)} {l : List Aff} (h : appL a b = some l) :
    ∃ x y, a = some x ∧ b = some y ∧ l = x ++ y := by
  obtain ⟨x, hx, h⟩ := bind_some h
  obtain ⟨y, hy, e⟩ := map_some h
  exact ⟨x, y, hx, hy, e.symm⟩

/-- A member of one member's list is a member of all lists laid end to end. -/
theorem mem_flatten_mapM {α : Type} {l : α → Option (List Aff)} : ∀ {xs : List α}
    {L : List (List Aff)}, xs.mapM l = some L → ∀ {a : α} {x : List Aff} {y : Aff}, a ∈ xs →
      l a = some x → y ∈ x → y ∈ L.flatten
  | [], _, _, _, _, _, ha, _, _ => by cases ha
  | b :: xs, L, h, a, x, y, ha, hl, hy => by
    obtain ⟨z, zs, hz, hzs, e⟩ := mapM_cons_some h
    subst e
    rw [List.flatten_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [hl] at hz
      cases hz
      exact List.mem_append_left _ hy
    · exact List.mem_append_right _ (mem_flatten_mapM hzs ha' hl hy)

/-- A routine that only returns a value. -/
theorem addsV_pure {α : Type} (a : α) {P : α → Prop} (h : P a) :
    AddsV (pure a : SubM α) P (some []) := by
  intro F G c c' x hx
  obtain ⟨rfl, rfl, -⟩ := (sub_pure _ _ _ _ _ _).mp hx
  exact ⟨h, [], rfl, rfl⟩

/-- A routine that leaves that part of the state as it was adds nothing. -/
theorem addsV_keep {α : Type} {m : SubM α} {P : α → Prop}
    (hm : ∀ (F G : Fork) (c c' : Ctx) (a : α), (m F).Yields c (a, G) c' →
      sumOf G = sumOf F ∧ P a) : AddsV m P (some []) := by
  intro F G c c' a h
  obtain ⟨e, p⟩ := hm F G c c' a h
  exact ⟨p, [], rfl, by rw [e]; rfl⟩

/-- One claim. -/
theorem addsL_lin (f : Aff) : AddsL (SubM.lin f) (some [f]) := by
  intro F G c c' a h
  obtain ⟨h1, -⟩ := (sub_lin f F G c c').mp h
  refine ⟨trivial, [f], rfl, ?_⟩
  show ((sumOf F).lin f).bind (fun x => pure x) = _
  rw [lin_sumOf, h1]
  rfl

/-- One routine after the other, where the second's list does not depend on the first's value. -/
theorem addsV_bind {α β : Type} {m : SubM α} {k : α → SubM β} {Q : α → Prop} {P : β → Prop}
    {a b : Option (List Aff)} (hm : AddsV m Q a) (hk : ∀ x, Q x → AddsV (k x) P b) :
    AddsV (m >>= k) P (appL a b) := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨q, la, rfl, hx⟩ := hm F F1 c c1 x h1
  obtain ⟨p, lb, rfl, hy⟩ := hk x q F1 G c1 c' y h2
  exact ⟨p, la ++ lb, rfl, by rw [Hd.lins_append, hx]; exact hy⟩

/-- A routine that adds nothing, and then one that may read its value. -/
theorem addsV_after {α β : Type} {m : SubM α} {k : α → SubM β} {Q : α → Prop} {P : β → Prop}
    {b : Option (List Aff)} (hm : AddsV m Q (some [])) (hk : ∀ x, Q x → AddsV (k x) P b) :
    AddsV (m >>= k) P b := by
  intro F G c c' y h
  obtain ⟨p, l, e, hl⟩ := addsV_bind hm hk F G c c' y h
  obtain ⟨x, z, e1, e2, rfl⟩ := appL_some e
  cases e1
  exact ⟨p, z, e2, hl⟩

/-- A routine, and then one that adds nothing. -/
theorem addsV_before {α β : Type} {m : SubM α} {k : α → SubM β} {Q : α → Prop} {P : β → Prop}
    {a : Option (List Aff)} (hm : AddsV m Q a) (hk : ∀ x, Q x → AddsV (k x) P (some [])) :
    AddsV (m >>= k) P a := by
  intro F G c c' y h
  obtain ⟨p, l, e, hl⟩ := addsV_bind hm hk F G c c' y h
  obtain ⟨x, z, e1, e2, rfl⟩ := appL_some e
  cases e2
  rw [List.append_nil] at hl
  exact ⟨p, x, e1, hl⟩

/-- A routine, and then only a value. -/
theorem addsV_tail {α β : Type} {m : SubM α} {Q : α → Prop} {a : Option (List Aff)}
    (hm : AddsV m Q a) {u : β} {P : β → Prop} (hu : P u) :
    AddsV (m >>= fun _ => (pure u : SubM β)) P a := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨e0, e1, -⟩ := (sub_pure _ _ _ _ _ _).mp h2
  obtain ⟨-, l, e, hl⟩ := hm F F1 c c1 x h1
  rw [e0, e1]
  exact ⟨hu, l, e, hl⟩

/-- Only a value, and then a routine. -/
theorem addsV_pure_bind {α β : Type} (a : α) {k : α → SubM β} {P : β → Prop}
    {l : Option (List Aff)} (hk : AddsV (k a) P l) : AddsV ((pure a : SubM α) >>= k) P l := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨e0, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h1
  rw [e0, e1, e2] at h2
  exact hk F G c c' y h2

/-- A value that must be there, and then a routine that reads it. -/
theorem addsV_form {α β : Type} (x : Option α) {k : α → SubM β} {P : β → Prop}
    {l : α → Option (List Aff)} (hk : ∀ a, AddsV (k a) P (l a)) :
    AddsV (form x >>= k) P (x.bind l) := by
  intro F G c c' y h
  obtain ⟨a, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨e0, e1, e2⟩ := (sub_form _ _ _ _ _ _).mp h1
  rw [e1, e2] at h2
  rw [e0]
  exact hk a F G c c' y h2

/-- A public condition, and then a routine. -/
theorem addsV_mustAs {β : Type} (n : String) (b : Bool) {k : SubM β} {P : β → Prop}
    {l : Option (List Aff)} (hk : AddsV k P l) :
    AddsV ((monadLift (Model.mustAs n b) : SubM Unit) >>= fun _ => k) P l := by
  intro F G c c' y h
  obtain ⟨_, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨-, e1, e2⟩ := (sub_mustAs _ _ _ _ _ _).mp h1
  rw [e1, e2] at h2
  exact hk F G c c' y h2

/-- One claim for each entry of an array of forms. -/
theorem addsL_forM (as : Array Aff) : AddsL (as.forM SubM.lin) (some as.toList) := by
  intro F G c c' a h
  refine ⟨trivial, as.toList, rfl, ?_⟩
  exact sub_forM SubM.lin as (fun pre H _ => (sumOf F).lins pre = some (sumOf H))
    (fun pre a rest _ F1 c1 G1 c2 hI h1 => by
      obtain ⟨-, x, e, hx⟩ := addsL_lin a F1 G1 c1 c2 () h1
      cases e
      rw [Hd.lins_append, hI]
      exact hx) rfl h

/-- A loop over a list, with any step: if each run of the step goes on and adds the list of its
member, the loop adds the lists of all members, one after the other. -/
theorem addsL_forIn {α : Type} (f : α → PUnit → SubM (ForInStep PUnit)) (xs : List α)
    (l : α → Option (List Aff))
    (hf : ∀ a, AddsV (f a PUnit.unit) (fun s => s = ForInStep.yield PUnit.unit) (l a)) :
    AddsL (forIn xs PUnit.unit f) ((xs.mapM l).map List.flatten) := by
  intro F G c c' u h
  have key := sub_forIn f xs
    (fun pre H _ => ∃ L, pre.mapM l = some L ∧ (sumOf F).lins L.flatten = some (sumOf H))
    (fun pre a rest _ F1 c1 s G1 c2 hI h1 => by
      obtain ⟨es, x, ex, hx⟩ := hf a F1 G1 c1 c2 s h1
      obtain ⟨L, eL, hL⟩ := hI
      refine ⟨es, L ++ [x], ?_, ?_⟩
      · rw [List.mapM_append, eL]
        simp [ex]
      · rw [List.flatten_append, Hd.lins_append, hL]
        simpa using hx)
    xs [] F G c c' rfl ⟨[], rfl, rfl⟩ h
  obtain ⟨L, eL, hL⟩ := key
  exact ⟨trivial, L.flatten, by rw [eL]; rfl, hL⟩

/-- The end of a loop's step. -/
theorem addsV_yield :
    AddsV (pure (ForInStep.yield PUnit.unit) : SubM (ForInStep PUnit))
      (fun s => s = ForInStep.yield PUnit.unit) (some []) :=
  addsV_pure _ rfl

/-- The routine that makes the claim of a sumcheck returns Psc.rowForm and adds nothing: it puts the
coefficients of the hiding polynomial under their slots. -/
theorem addsV_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    AddsV (pscRow p S0 kept) (fun x => x.1 = p.rowForm S0 kept) (some []) := by
  refine addsV_keep fun F G c c' a h => ?_
  unfold Model.pscRow at h
  obtain ⟨_, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨_, F2, c2, h3, h4⟩ := (sub_bind _ _ _ _ _ _ _).mp h2
  obtain ⟨-, e1, -⟩ := (sub_must _ _ _ _ _).mp h1
  obtain ⟨h5, -⟩ := (sub_change _ _ _ _ _).mp h3
  obtain ⟨e0, e2, -⟩ := (sub_pure _ _ _ _ _ _).mp h4
  rw [e2, hideRun_sumOf h5, e1, e0]
  exact ⟨rfl, rfl⟩

/-! ## The stretches of the identities' half -/

/-- The claim of claimRowBatch. -/
theorem adds_claimRowBatch (y : Lay) (H : Heard) :
    AddsL (claimRowBatch y H) (some [rowBatchForm y H]) := addsL_lin _

/-- The three claims of claimsNorms. -/
def normsL (P : Pub) (v : Env) (H : Heard) : Option (List Aff) :=
  appL (some [H.wpl.row]) (appL (some [Aff.slot H.wpl.sL - Aff.slot H.wpl.sR])
    ((P.y.T_ "xs").bind fun txs => (v.tabAt "xbI@Z_V").bind fun tI =>
      (v.tabAt "af@Z_V").bind fun tA =>
        (Model.hiTab H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption.bind fun e =>
          (normsSum P.y v tI tA txs e H.gp).bind fun sum => some [Aff.slot H.wpl.sL + sum]))

/-- claimsNorms adds them. -/
theorem adds_claimsNorms (P : Pub) (v : Env) (H : Heard) :
    AddsL (claimsNorms P v H) (normsL P v H) := by
  rw [claimsNorms_eq]
  exact addsV_bind (addsL_lin _) fun _ _ => addsV_bind (addsL_lin _) fun _ _ =>
    addsV_form _ fun txs => addsV_mustAs _ _ (addsV_form _ fun tI => addsV_form _ fun tA =>
      addsV_form _ fun e => addsV_form _ fun sum => addsL_lin _)

/-- The claim of claimEmbedding. -/
def embL (v : Env) (H : Heard) (sVE : ℕ) : Option (List Aff) :=
  (v.tabAt "xbI@Z_E").bind fun t => (embSum v t H.tkh).bind fun s =>
    some [(Aff.slot sVE).scale (negE oneE) + s]

/-- claimEmbedding adds it. -/
theorem adds_claimEmbedding (v : Env) (H : Heard) (sVE : ℕ) :
    AddsL (claimEmbedding v H sVE) (embL v H sVE) := by
  rw [claimEmbedding_eq]
  exact addsV_form _ fun t => addsV_form _ fun s => addsL_lin _

/-- The claims of claimsOneHot: one for each routed layer, if there are routed experts. -/
def oneHotL (v : Env) : Option (List Aff) :=
  if v.y.h.p3 then
    ((List.range v.y.LamM).mapM fun lm => (hotSum v lm).bind fun s =>
      some [Aff.ofConst (negE oneE) + s]).map List.flatten
  else some []

/-- claimsOneHot adds them. -/
theorem adds_claimsOneHot (v : Env) : AddsL (claimsOneHot v) (oneHotL v) := by
  rw [claimsOneHot_eq]
  unfold oneHotL
  by_cases h : v.y.h.p3 = true
  · rw [if_pos h, if_pos h]
    refine addsV_tail (addsL_forIn _ _ _ ?_) trivial
    intro lm
    exact addsV_form _ fun s => addsV_tail (addsL_lin _) rfl
  · rw [if_neg h, if_neg h]
    exact addsV_pure _ trivial

/-! ## claimsLedger5 -/

/-- The values that were shown under n slots: the routine leaves state and context as they were. -/
theorem shownRun_keeps {first n : ℕ} {F G : Fork} {c c' : Ctx} {sh : Array E}
    (h : (shownRun first n F).Yields c (sh, G) c') : G = F ∧ c' = c := by
  unfold Model.Layer.shownRun at h
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind] at h
  obtain ⟨r, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨-, e1, e2⟩ := (sub_pure _ _ _ _ _ _).mp h2
  obtain ⟨g1, g2, -⟩ := sub_mapM_list (fun i => SubM.shown (first + i)) (fun _ _ => True)
    (fun a F c b G c' hb => by
      obtain ⟨-, x1, x2⟩ := (sub_ask _ _ _ _ _ _).mp hb
      exact ⟨x1, x2, trivial⟩) _ F F1 c c1 r h1
  exact ⟨e1.trans g1, e2.trans g2⟩

/-- What the token sumcheck of the row products is compared with at its end, from the shown end
values sh: the verifier's S0. -/
def ledS0 (v : Env) (H : Heard) (sh : Array E) : E :=
  (List.range v.y.NI).foldl
    (fun s i => addE s (ledProducts5 H.omV (7 * i) (sh.getD (4 * i) zeroE)
      (sh.getD (4 * i + 1) zeroE) (sh.getD (4 * i + 2) zeroE) (sh.getD (4 * i + 3) zeroE)))
    zeroE

/-- The four claims of norm i on the shown end values. -/
def shownL (v : Env) (H : Heard) (i : ℕ) : Option (List Aff) :=
  (v.row5At "r_tV" i).bind fun r =>
    (([r.a, r.b, r.Rlo, r.Rhi].zipIdx.map fun x => (x.2, x.1)).mapM fun x =>
      some [Aff.slot (H.tV.sEnd + 4 * i + x.1) - x.2]).map List.flatten

/-- The nine claims of a norm on the carries. x: the row at P_V and the norm's number. -/
def carryL (H : Heard) (x : Row5 Aff × ℕ) : Option (List Aff) :=
  ((List.range 9).mapM fun s =>
    some [ledCarry5 x.1 s (Aff.slot (H.sW + 9 * x.2 + s))]).map List.flatten

/-- The eight claims of a norm after the carries. -/
def linesL (v : Env) (H : Heard) (x : Row5 Aff × ℕ) : Option (List Aff) :=
  some (ledLines5 x.1 ((Array.range 7).map fun j => Aff.slot (H.sPv + 7 * x.2 + j))
    (epsOf v.y x.2) (twoM v x.2)).toList

/-- The claims of claimsLedger5, from the shown end values sh: the token sumcheck's; four for each
norm on the shown values; nine for each norm on the carries; eight for each norm. -/
def ledgerL (v : Env) (H : Heard) (sh : Array E) : Option (List Aff) :=
  appL (some [H.tV.p.rowForm (ledS0 v H sh) {}])
    (appL (((List.range v.y.NI).mapM (shownL v H)).map List.flatten)
      (((Array.range v.y.NI).mapM fun i => v.row5At "P_V" i).bind fun rP =>
        appL ((rP.toList.zipIdx.mapM (carryL H)).map List.flatten)
          ((rP.toList.zipIdx.mapM (linesL v H)).map List.flatten)))

/-- claimsLedger5 adds them: whenever it returns, there are shown end values sh, read off the state
in which it began, with which the list is there and has been added. -/
theorem adds_claimsLedger5 (v : Env) (H : Heard) {F G : Fork} {c c' : Ctx}
    (h : (claimsLedger5 v H F).Yields c ((), G) c') :
    ∃ sh, (shownRun H.tV.sEnd (4 * v.y.NI) F).Yields c (sh, F) c ∧
      ∃ l, ledgerL v H sh = some l ∧ (sumOf F).lins l = some (sumOf G) := by
  unfold Model.Layer.claimsLedger5 at h
  obtain ⟨_, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  obtain ⟨-, e1, e2⟩ := (sub_mustAs _ _ _ _ _ _).mp h1
  rw [e1, e2] at h2
  obtain ⟨sh, F2, c2, h3, h4⟩ := (sub_bind _ _ _ _ _ _ _).mp h2
  obtain ⟨e3, e4⟩ := shownRun_keeps h3
  rw [e3, e4] at h3 h4
  refine ⟨sh, h3, ?_⟩
  have key : ∀ m : SubM Unit, AddsL m (ledgerL v H sh) → (m F).Yields c ((), G) c' →
      ∃ l, ledgerL v H sh = some l ∧ (sumOf F).lins l = some (sumOf G) :=
    fun m A hm => (A F G c c' () hm).2
  refine key _ ?_ h4
  unfold ledgerL
  refine addsV_after (addsV_pscRow H.tV.p (ledS0 v H sh) {}) fun x hx => ?_
  have hrow : AddsL (SubM.lin x.1) (some [H.tV.p.rowForm (ledS0 v H sh) {}]) := by
    rw [← hx]
    exact addsL_lin x.1
  refine addsV_bind hrow fun _ _ => ?_
  refine addsV_bind (addsL_forIn _ _ _ ?_) fun _ _ => ?_
  · intro i
    unfold shownL
    refine addsV_form _ fun r => ?_
    refine addsV_before (addsL_forIn _ _ _ ?_) fun _ _ => addsV_pure_bind _ addsV_yield
    rintro ⟨k, f⟩
    exact addsV_tail (addsL_lin _) rfl
  · refine addsV_form _ fun rP => ?_
    refine addsV_bind (addsL_forIn _ _ _ ?_) fun _ _ => addsV_tail (addsL_forIn _ _ _ ?_) trivial
    · rintro ⟨r, i⟩
      unfold carryL
      refine addsV_before (addsL_forIn _ _ _ ?_) fun _ _ => addsV_pure_bind _ addsV_yield
      intro s
      exact addsV_tail (addsL_lin _) rfl
    · rintro ⟨r, i⟩
      unfold linesL
      exact addsV_tail (addsL_forM _) rfl

/-! ## The members -/

/-- Where the lists of all members, laid end to end, are there: each member has its list, and what
is in that list is in the whole. -/
theorem mem_flat {α : Type} {l : α → Option (List Aff)} {xs : List α} {L' : List Aff}
    (h : (xs.mapM l).map List.flatten = some L') {a : α} (ha : a ∈ xs) :
    ∃ x, l a = some x ∧ ∀ y ∈ x, y ∈ L' := by
  obtain ⟨L, hL, e⟩ := map_some h
  subst e
  have ex : ∀ (xs : List α) (L : List (List Aff)), xs.mapM l = some L → a ∈ xs →
      ∃ x, l a = some x := by
    intro xs
    induction xs with
    | nil =>
      intro L _ ha
      cases ha
    | cons b xs ih =>
      intro L h ha
      obtain ⟨z, zs, hz, hzs, -⟩ := mapM_cons_some h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨z, hz⟩
      · exact ih zs hzs ha'
  obtain ⟨x, hx⟩ := ex xs L hL ha
  exact ⟨x, hx, fun y hy => mem_flatten_mapM hL ha hx hy⟩

/-- Member k of what a function that may refuse returns on the numbers below n. -/
theorem range_mapM_at {β : Type} {f : ℕ → Option β} {n : ℕ} {r : Array β}
    (h : (Array.range n).mapM f = some r) {k : ℕ} (hk : k < n) {y : β} (hy : f k = some y) :
    r.toList[k]? = some y := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hl, e⟩ := map_some h
  subst e
  have hk' : (Array.range n).toList[k]? = some k := by simp [hk]
  obtain ⟨z, h1, h2⟩ := mapM_get _ ys hl k k hk'
  rw [hy] at h2
  cases h2
  exact h1

section Members

variable {v : Env} {H : Heard} {sh : Array E} {l : List Aff}

/-- The parts of the list of claimsLedger5. -/
theorem ledgerL_parts (h : ledgerL v H sh = some l) :
    ∃ (lA lC lD : List Aff) (rP : Array (Row5 Aff)),
      ((List.range v.y.NI).mapM (shownL v H)).map List.flatten = some lA ∧
      (Array.range v.y.NI).mapM (fun i => v.row5At "P_V" i) = some rP ∧
      (rP.toList.zipIdx.mapM (carryL H)).map List.flatten = some lC ∧
      (rP.toList.zipIdx.mapM (linesL v H)).map List.flatten = some lD ∧
      l = [H.tV.p.rowForm (ledS0 v H sh) {}] ++ (lA ++ (lC ++ lD)) := by
  obtain ⟨x1, l2, e1, h2, rfl⟩ := appL_some h
  obtain ⟨lA, l3, hA, h3, rfl⟩ := appL_some h2
  obtain ⟨rP, hrP, h4⟩ := bind_some h3
  obtain ⟨lC, lD, hC, hD, rfl⟩ := appL_some h4
  cases e1
  exact ⟨lA, lC, lD, rP, hA, hrP, hC, hD, rfl⟩

/-- The token sumcheck's claim is a member. -/
theorem mem_ledger_row (h : ledgerL v H sh = some l) :
    H.tV.p.rowForm (ledS0 v H sh) {} ∈ l := by
  obtain ⟨lA, lC, lD, rP, -, -, -, -, rfl⟩ := ledgerL_parts h
  simp

/-- The nine claims of each norm on the carries are members. -/
theorem mem_ledger_carry (h : ledgerL v H sh = some l) {ν : ℕ} (hν : ν < v.y.NI) {r : Row5 Aff}
    (hr : v.row5At "P_V" ν = some r) {s : ℕ} (hs : s < 9) :
    ledCarry5 r s (Aff.slot (H.sW + 9 * ν + s)) ∈ l := by
  obtain ⟨lA, lC, lD, rP, -, hrP, hC, -, rfl⟩ := ledgerL_parts h
  have hm : (r, ν) ∈ rP.toList.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (range_mapM_at hrP hν hr)
  obtain ⟨x, hx, hin⟩ := mem_flat hC hm
  obtain ⟨x', hx', hin'⟩ := mem_flat hx (List.mem_range.mpr hs)
  cases hx'
  have h1 := hin _ (hin' _ (List.mem_singleton.mpr rfl))
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inl h1))

/-- The eight claims of each norm after the carries are members. -/
theorem mem_ledger_line (h : ledgerL v H sh = some l) {ν : ℕ} (hν : ν < v.y.NI) {r : Row5 Aff}
    (hr : v.row5At "P_V" ν = some r) {f : Aff}
    (hf : f ∈ (ledLines5 r ((Array.range 7).map fun j => Aff.slot (H.sPv + 7 * ν + j))
      (epsOf v.y ν) (twoM v ν)).toList) : f ∈ l := by
  obtain ⟨lA, lC, lD, rP, -, hrP, -, hD, rfl⟩ := ledgerL_parts h
  have hm : (r, ν) ∈ rP.toList.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (range_mapM_at hrP hν hr)
  obtain ⟨x, hx, hin⟩ := mem_flat hD hm
  cases hx
  have h1 := hin _ hf
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr h1))

/-- The four claims of each norm on the shown end values are members. -/
theorem mem_ledger_shown (h : ledgerL v H sh = some l) {ν : ℕ} (hν : ν < v.y.NI) {r : Row5 Aff}
    (hr : v.row5At "r_tV" ν = some r) :
    Aff.slot (H.tV.sEnd + 4 * ν + 0) - r.a ∈ l ∧ Aff.slot (H.tV.sEnd + 4 * ν + 1) - r.b ∈ l ∧
      Aff.slot (H.tV.sEnd + 4 * ν + 2) - r.Rlo ∈ l ∧
      Aff.slot (H.tV.sEnd + 4 * ν + 3) - r.Rhi ∈ l := by
  obtain ⟨lA, lC, lD, rP, hA, -, -, -, rfl⟩ := ledgerL_parts h
  obtain ⟨x, hx, hin⟩ := mem_flat hA (List.mem_range.mpr hν)
  unfold shownL at hx
  rw [hr] at hx
  have hi : (([r.a, r.b, r.Rlo, r.Rhi].zipIdx.map fun x => (x.2, x.1)).mapM fun x =>
      some [Aff.slot (H.tV.sEnd + 4 * ν + x.1) - x.2]).map List.flatten = some x := hx
  have one : ∀ p : ℕ × Aff, p ∈ ([r.a, r.b, r.Rlo, r.Rhi].zipIdx.map fun x => (x.2, x.1)) →
      Aff.slot (H.tV.sEnd + 4 * ν + p.1) - p.2 ∈
        [H.tV.p.rowForm (ledS0 v H sh) {}] ++ (lA ++ (lC ++ lD)) := by
    intro p hp
    obtain ⟨x', hx', hin'⟩ := mem_flat hi hp
    cases hx'
    have h1 := hin _ (hin' _ (List.mem_singleton.mpr rfl))
    simp only [List.mem_append]
    exact Or.inr (Or.inl h1)
  exact ⟨one (0, r.a) (by simp), one (1, r.b) (by simp), one (2, r.Rlo) (by simp),
    one (3, r.Rhi) (by simp)⟩

end Members

/-- The three claims of claimsNorms, as members: the product layer's claim; that its two end values
are one; and, where the sum is sum, the claim on the end value. -/
theorem mem_normsL {P : Pub} {v : Env} {H : Heard} {l : List Aff} (h : normsL P v H = some l) :
    H.wpl.row ∈ l ∧ Aff.slot H.wpl.sL - Aff.slot H.wpl.sR ∈ l ∧
      ∃ txs tI tA e sum, P.y.T_ "xs" = some txs ∧ v.tabAt "xbI@Z_V" = some tI ∧
        v.tabAt "af@Z_V" = some tA ∧
        (Model.hiTab H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption = some e ∧
        normsSum P.y v tI tA txs e H.gp = some sum ∧ Aff.slot H.wpl.sL + sum ∈ l := by
  obtain ⟨x0, l1, e0, h1, rfl⟩ := appL_some h
  obtain ⟨x1, l2, e1, h2, rfl⟩ := appL_some h1
  cases e0
  cases e1
  obtain ⟨txs, a1, h2⟩ := bind_some h2
  obtain ⟨tI, a2, h2⟩ := bind_some h2
  obtain ⟨tA, a3, h2⟩ := bind_some h2
  obtain ⟨e, a4, h2⟩ := bind_some h2
  obtain ⟨sum, a5, h2⟩ := bind_some h2
  cases h2
  exact ⟨by simp, by simp, txs, tI, tA, e, sum, a1, a2, a3, a4, a5, by simp⟩

/-- The claim of each routed layer on the selector's entries is a member. -/
theorem mem_oneHotL {v : Env} {l : List Aff} (h : oneHotL v = some l) (hp : v.y.h.p3 = true)
    {lm : ℕ} (hlm : lm < v.y.LamM) :
    ∃ s, hotSum v lm = some s ∧ Aff.ofConst (negE oneE) + s ∈ l := by
  unfold oneHotL at h
  rw [if_pos hp] at h
  obtain ⟨x, hx, hin⟩ := mem_flat h (List.mem_range.mpr hlm)
  obtain ⟨s, hs, hx⟩ := bind_some hx
  cases hx
  exact ⟨s, hs, hin _ (List.mem_singleton.mpr rfl)⟩

/-! ## From the lists to the one equation; one stretch after another -/

/-- Two stretches, one after the other: the lists are laid end to end. -/
theorem lins_trans {F0 F1 F2 : Fork} {a b : List Aff} (h1 : (sumOf F0).lins a = some (sumOf F1))
    (h2 : (sumOf F1).lins b = some (sumOf F2)) : (sumOf F0).lins (a ++ b) = some (sumOf F2) := by
  rw [Hd.lins_append, h1]
  exact h2

/-- The note of the constant between two stretches adds nothing. -/
theorem adds_noteClaims (w : String) : AddsL (Model.Layer.noteClaims w) (some []) := by
  refine addsV_keep fun F G c c' a h => ⟨?_, trivial⟩
  unfold Model.Layer.noteClaims at h
  obtain ⟨x, F1, c1, h1, h2⟩ := (sub_bind _ _ _ _ _ _ _).mp h
  have e1 : F1 = F := by
    have h1' : ((get : SubM Fork) F).Yields c (x, F1) c1 := h1
    rw [runs_iff] at h1'
    cases h1'
    rfl
  rw [(sub_note h2).1, e1]

/-- What a list of claims does to the one equation. If the part of the state that the equation is
made of has become what Fork.lins makes of it with the list l, the total has grown by the sum of
theta^(n + i) times the worth of form number i, where n is the number of claims before: it is
Fork.lins_total (OnBytes/Model/HideLaws.lean), at the two states without the four fields, of which
the total, the number of claims, theta and the number of slots read none. -/
theorem total_of_lins {K : Type} [CommRing K] (ρ : Model.Reading K) (W : Model.World K)
    {F G : Fork} {l : List Aff} (hs : F.LS.size = F.ns)
    (h : (sumOf F).lins l = some (sumOf G)) :
    G.total ρ W = F.total ρ W + Model.claimsValue ρ W (ρ.val F.theta) F.nClaim l ∧
      G.nClaim = F.nClaim + l.length ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns :=
  Model.Fork.lins_total ρ W l (sumOf F) (sumOf G) hs h

#print axioms lin_sumOf
#print axioms hideRun_sumOf
#print axioms addsV_bind
#print axioms addsL_forM
#print axioms addsL_forIn
#print axioms addsV_pscRow
#print axioms adds_claimsNorms
#print axioms adds_claimEmbedding
#print axioms adds_claimsOneHot
#print axioms shownRun_keeps
#print axioms adds_claimsLedger5
#print axioms mem_ledger_row
#print axioms mem_ledger_carry
#print axioms mem_ledger_line
#print axioms mem_ledger_shown
#print axioms mem_normsL
#print axioms mem_oneHotL
#print axioms adds_noteClaims
#print axioms total_of_lins

end OnBytes.Road
