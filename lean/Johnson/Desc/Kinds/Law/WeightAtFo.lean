-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightAtFo.lean: weightAt_kept (Johnson/Desc/Kinds/Law/WeightAtSame.lean) AT
THE WEAKER OF THE LIBRARY'S TWO RELATIONS "a later ledger".

Why. The library has two: OnBytes.PscRun.Later and Fo.Later
(OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean). They differ in one field: the first also says that a
ledger whose three arrays have the ledger's size stays so. KeptW asks the first. The sentence
WeightAt reads nothing of that field. A kind whose law on its own accept ends in Fo.Later could not
call weightAt_kept. The first gives the second (a library lemma): so the form here serves both.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  KeptWFo s s': KeptW's text with Fo.Later in the place of OnBytes.PscRun.Later: WHAT A SUB-PROTOCOL
      BETWEEN OWES ON ITS OWN ACCEPT. KeptW.fo: KeptW gives it.
  shown_fo, hidAt_fo, hidsAt_fo, sumOf_fo, allOf_fo: what is read back of a ledger is read back of
      every later one. THEY FOLLOW, LINE BY LINE, the lemmas shown_later
      (OnBytes/Tie/Pv/Psc/PscLater.lean), hidAt_later, hidsAt_later (Law/HeardBack.lean),
      sumOf_later, allOf_later (Law/RunsFixed.lean), which stand at the stronger relation.
  heard_keptFo, hidden_keptFo.
  weightAt_keptFo: UNDER KeptWFo s s', WHERE heard ANSWERS AT THE EARLIER STATE s: the sentence
      holds at both states or at none.

Every letter under "there is": KeptWFo: o, o': pinned by the two states' field here. In
weightAt_keptFo's premise: H: pinned by heard at s.
What it does not say. As WeightAtSame.lean: that heard answers at the earlier state is a premise;
that any sub-protocol meets KeptWFo is not said. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WeightAtSame
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.First (S HeadOwn)

/-- **What a sub-protocol between owes**, at the weaker relation. -/
def KeptWFo (s s' : S) : Prop :=
  ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧ o'.x = o.x ∧ o'.squaresP = o.squaresP ∧
    o'.opened = o.opened ∧ o'.lookHeard = o.lookHeard ∧ s'.out.reply = s.out.reply ∧
    s'.req = s.req ∧ _root_.Fo.Later o.F o'.F

/-- KeptW gives it. -/
theorem KeptW.fo {s s' : S} (a : KeptW s s') : KeptWFo s s' := by
  obtain ⟨o, o', ho, ho', e1, e2, e3, e4, e5, e6, hL⟩ := a
  exact ⟨o, o', ho, ho', e1, e2, e3, e4, e5, e6, ⟨hL.next, hL.ns, hL.keep⟩⟩

theorem shown_fo {F G : Fork} (h : _root_.Fo.Later F G) {j : Nat} {y : E}
    (hs : F.shown j = some y) : G.shown j = some y := by
  obtain ⟨h1, h2, rfl⟩ := (OnBytes.PscRun.shown_iff F j y).1 hs
  obtain ⟨a1, a2, -⟩ := h.keep j h2
  exact (OnBytes.PscRun.shown_iff G j _).2 ⟨by rw [h.ns]; exact h1, a1, a2.symm⟩

theorem hidAt_fo {F G : Fork} (h : _root_.Fo.Later F G) {j : Nat} {a : Hid}
    (e : hidAt F j = some a) : hidAt G j = some a := by
  unfold hidAt at e ⊢
  cases hs : F.shown j with
  | none => rw [hs] at e; simp at e
  | some x => rw [hs] at e; rw [shown_fo h hs]; exact e

theorem hidsAt_fo {F G : Fork} (h : _root_.Fo.Later F G) {j n : Nat} {a : Array Hid}
    (e : hidsAt F j n = some a) : hidsAt G j n = some a := by
  unfold hidsAt at e ⊢
  cases hm : (List.range n).mapM (fun i => hidAt F (j + i)) with
  | none => rw [hm] at e; simp at e
  | some l =>
    rw [hm] at e
    rw [mapM_mono (f := fun i => hidAt F (j + i)) (g := fun i => hidAt G (j + i))
      (fun i b hb => hidAt_fo h hb) _ _ hm]
    exact e

theorem sumOf_fo {F G : Fork} (h : _root_.Fo.Later F G) (t : OnBytes.Model.Tsc) (r : Point)
    (n : Nat) (s : Sum) (e : sumOf F t r n = some s) : sumOf G t r n = some s := by
  unfold sumOf at e ⊢
  exact bind_mono (fun _ => hidAt_fo h) (fun _ _ e1 =>
    bind_mono (fun _ => hidsAt_fo h) (fun _ _ e2 => e2) e1) e

/-- What the seat reads back is read back at every later ledger. -/
theorem allOf_fo {F G : Fork} (h : _root_.Fo.Later F G) (x : OnBytes.Model.Head.Heard)
    (sq : Option Part.MaskedSum.Heard) (H : HeardAll) (e : allOf F x sq = some H) :
    allOf G x sq = some H := by
  unfold allOf at e ⊢
  exact bind_mono (fun _ => hidsAt_fo h) (fun _ _ e1 =>
    bind_mono (fun _ => id) (fun _ _ e2 =>
    bind_mono (fun _ => hidAt_fo h) (fun _ _ e3 =>
    bind_mono (fun _ => hidAt_fo h) (fun _ _ e4 =>
    bind_mono (fun _ => hidsAt_fo h) (fun _ _ e5 =>
    bind_mono (fun _ => id) (fun _ _ e6 =>
    bind_mono (fun _ => sumOf_fo h _ _ _ _) (fun _ _ e7 =>
    bind_mono (fun _ => sumOf_fo h _ _ _ _) (fun _ _ e8 =>
    bind_mono (fun _ => sumOf_fo h _ _ _ _) (fun _ _ e9 => e9) e8) e7) e6) e5) e4) e3) e2) e1) e

theorem given_keptFo (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) {s s' : S}
    (a : KeptWFo s s') : given p (seatAt h iU3) s' = given p (seatAt h iU3) s := by
  obtain ⟨o, o', ho, ho', _, _, eo, el, er, eq, _⟩ := a
  refine given_congr p (seatAt h iU3) ?_ er (requestOf_congr eq)
  show s'.lookHeard?.map _ = s.lookHeard?.map _
  unfold S.lookHeard?
  rw [ho, ho']
  simp only [eo, el]

theorem heard_keptFo (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s s' : S} (a : KeptWFo s s')
    (H : HeardAll) (e : (seatAt h iU3).heard s = some H) : (seatAt h iU3).heard s' = some H := by
  obtain ⟨o, o', ho, ho', ex, es, _, _, _, _, hL⟩ := a
  have e' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := e
  show (match s'.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H
  rw [ho] at e'
  rw [ho']
  simp only [ex, es] at e' ⊢
  obtain ⟨q, hq, e1⟩ := Option.bind_eq_some_iff.mp e'
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp e1
  rw [hq, hx]
  exact allOf_fo hL x _ H e2

theorem hidden_keptFo {F G : Fork} (m : Nat → E) {j : Nat} (hL : _root_.Fo.Later F G)
    (hf : OnBytes.PscRun.Filled F j) : hidden G m j = hidden F m j := by
  obtain ⟨_, h1, h2⟩ := hL.keep j hf
  unfold hidden
  rw [zero_is, h1, h2]

/-- **UNDER KeptWFo, WHERE heard ANSWERS AT THE EARLIER STATE, THE SENTENCE HOLDS AT BOTH STATES OR
AT NONE.** -/
theorem weightAt_keptFo (W : OnBytes.Model.Verify.Public) {s s' : S} (a : KeptWFo s s')
    (hh : ∃ H, (seatAt W.hS (readsOf W)).heard s = some H) (c : Cells) (m : Nat → E) :
    WeightAt W s' c m ↔ WeightAt W s c m := by
  obtain ⟨H0, h0⟩ := hh
  refine weightAt_same W s s' c m (given_keptFo _ _ _ a)
    ((heard_keptFo _ _ a H0 h0).trans h0.symm) ?_
  intro H hH
  obtain ⟨o, o', ho, ho', _, _, eo, _, _, _, hL⟩ := a
  obtain ⟨x, _, hv, hf⟩ := weightSlot_filled _ _ ho hH
  rw [hv, atWorld_slot, atWorld_slot]
  have l1 : (seatAt W.hS (readsOf W)).ledger s = (if o.opened then some o.F else none).getD {} := by
    show s.fork?.getD {} = _
    unfold S.fork?
    rw [ho]
  have l2 : (seatAt W.hS (readsOf W)).ledger s' =
      (if o'.opened then some o'.F else none).getD {} := by
    show s'.fork?.getD {} = _
    unfold S.fork?
    rw [ho']
  rw [l1, l2, eo]
  cases o.opened with
  | false => rfl
  | true =>
    show _ + _ * hidden o'.F m _ = _ + _ * hidden o.F m _
    rw [hidden_keptFo m hL hf]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.KeptW.fo
#print axioms VerifiableInference.Desc.Kinds.Head.Law.allOf_fo
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_keptFo
#print axioms VerifiableInference.Desc.Kinds.Head.Law.weightAt_keptFo
