-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HearJoined.lean: THE JOINED PARTS OF A HEARING
(Johnson/Desc/Kinds/HeadParts.lean: drawPoint, sendThenBatch, heardBy, sumcheck, level) IN THE FRAME
OF HearFrame.lean: each has a step on the ledger's shape, which returns the shape of its value and
of the ledger behind. General laws; nothing is evaluated.
  1 `HearSh.drawPoint` (the point's size). `hear_bind`, `hear_pure`, `hear_need`: a bind, a pure, a
    need that returns. `HearSh.sendThenBatch`: n scalars are sent and laid (hideS n); the drawn
    element is left out.
  2 `ownD`, `ownSlots_d`, `zip_degrees`, `leadScalars_length`, `hear_stretch`. `heardByS lead CS m
    ends`, **`HearSh.heardBy`**: the lead is laid; the part's hearing at the degrees 3, …, 3 (m
    times) and 3 for the further variable; the own slots are filled; the end values' forms are read:
    where the start form's shape is CS of the lead's shapes.
  3 `sumcheckS`, **`HearSh.sumcheck`**; `levelS`, **`HearSh.level`**.
By HearFrame.lean's HearSh.hide, HearSh.round, HearSh.hiddenFrom and HearSum.lean's ms_hear_sh,
rowLaid_sh.
Limits. THE WEAK FORM, as in HearFrame.lean: under the step's own return. That a hearing returns
where its step does is not said. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HearSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Kinds (Hear Hid Sum Point)
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots)

/-! ## 1 A point is drawn; scalars are sent and batched -/

theorem HearSh.drawPoint (n : Nat) :
    HearSh (Kinds.drawPoint n) Array.size fun L => some (n, L) := by
  intro F rs a G left y hx hf
  have h := HearSh.bind (sh' := Array.size) (HearSh.round 0 n)
    (kS := fun b L => some (b.2, L))
    (k := fun x => (Pure.pure x.2.toArray : Hear Point))
    (fun x => by
      have := HearSh.pure (α := Point) x.2.toArray Array.size
      simpa using this)
  exact h F rs a G left y hx (by simpa using hf)

/-- A bind that returns. -/
theorem hear_bind {α β : Type} {x : Hear α} {k : α → Hear β} {F : Fork} {rs : List Fmt.RoundView}
    {r : β × Fork × List Fmt.RoundView} (h : (x >>= k) F rs = some r) :
    ∃ a G l, x F rs = some (a, G, l) ∧ k a G l = some r := by
  have h' : (match x F rs with
    | some (a, G, l) => k a G l
    | none => none) = some r := h
  cases hx : x F rs with
  | none =>
    rw [hx] at h'
    cases h'
  | some q =>
    obtain ⟨a, G, l⟩ := q
    rw [hx] at h'
    exact ⟨a, G, l, rfl, h'⟩

theorem hear_pure {α : Type} {a : α} {F : Fork} {rs : List Fmt.RoundView} {r : α × Fork × List Fmt.RoundView}
    (h : (Pure.pure a : Hear α) F rs = some r) : r = (a, F, rs) := (Option.some.inj h).symm

theorem hear_need {α : Type} {o : Option α} {F : Fork} {rs : List Fmt.RoundView}
    {r : α × Fork × List Fmt.RoundView} (h : Hear.need o F rs = some r) :
    o = some r.1 ∧ r.2 = (F, rs) := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨ha, rfl⟩

/-- n scalars are sent and laid; one element is drawn. The element is left out of the shape. The
letter rows plays no part in the step. -/
theorem HearSh.sendThenBatch (n rows : Nat) :
    HearSh (Kinds.sendThenBatch n rows) (fun x => x.1.toList.map hidSh) (hideS n) := by
  intro F rs a G left y hx hf
  unfold Kinds.sendThenBatch at hx
  obtain ⟨⟨v, g⟩, F₁, l₁, h1, hx⟩ := hear_bind hx
  obtain ⟨c, F₂, l₂, h2, hx⟩ := hear_bind hx
  obtain ⟨e, F₃, l₃, h3, hx⟩ := hear_bind hx
  obtain ⟨rfl, rfl, -⟩ : (c, e) = a ∧ F₃ = G ∧ l₃ = left := by
    have q := hear_pure hx
    exact ⟨congrArg (·.1) q.symm, congrArg (·.2.1) q.symm, congrArg (·.2.2) q.symm⟩
  obtain rfl : F₃ = F₂ := congrArg (·.1) (hear_need h3).2
  have e1 := HearSh.round n 1 F rs (v, g) F₁ l₁ _ h1 rfl
  have eF : ledSh F = ledSh F₁ := congrArg (·.2) e1
  have en : n = v.length := congrArg (·.1.1) e1
  rw [eF, en] at hf
  exact HearSh.hide v F₁ l₁ c F₃ l₂ y h2 hf

/-! ## 2 The masked sumcheck as a kind's text hears it -/

/-- The part's own slots, of the degrees. A "degree" is the library's Var.d throughout: the number
of coefficients of the round's polynomial (Johnson/Desc/Part/MaskedSum4.lean). -/
def ownD (ds : List Nat) : Nat := ds.foldl (fun n d => n + (d - 1)) 1

theorem ownSlots_d (vs : List Var) : ownSlots vs = ownD (vs.map Var.d) := by
  unfold ownSlots ownD
  rw [List.foldl_map]

theorem zip_degrees : ∀ (vs : List Var) (r : List E), r.length = vs.length →
    (vs.zip r).map (·.1.d) = vs.map Var.d
  | [], _, _ => rfl
  | _ :: _, [], h => by cases h
  | v :: vs, x :: r, h => by
    show v.d :: ((vs.zip r).map (·.1.d)) = v.d :: vs.map Var.d
    rw [zip_degrees vs r (Nat.succ.inj h)]

theorem leadScalars_length {k : Part.MaskedSum.Call} {rs : List Fmt.RoundView} {v : List E}
    (h : Part.MaskedSum.leadScalars k rs = some v) : v.length = k.lead := by
  unfold Part.MaskedSum.leadScalars at h
  obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Part.MaskedSum.firstRound at hx
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hx
  show (q.1.take k.lead).length = k.lead
  rw [List.length_take, (roundOf_sizes hq).1]
  omega

theorem hear_stretch {n : Nat} {F : Fork} {rs : List Fmt.RoundView}
    {r : List Fmt.RoundView × Fork × List Fmt.RoundView} (h : Hear.stretch n F rs = some r) : r.2.1 = F := by
  unfold Hear.stretch at h
  split at h
  · cases h
  · rw [← Option.some.inj h]

/-- heardBy on shapes. lead: the caller's scalars in front; CS: the start form's shape, of the
lead's shapes; m: the number of the point's coordinates; ends: the number of end values. The step
counts no rounds and asks neither 1 ≤ ends nor that the start form's slots are filled. -/
def heardByS (lead : Nat) (CS : List AffSh → AffSh) (m ends : Nat) (L : LedSh) :
    Option ((List AffSh × KSumSh) × LedSh) :=
  let ds := List.replicate m 3 ++ [3]
  let own := ownD ds
  (hideS lead L).bind fun c =>
  (msHearS (CS c.1) ds own ends c.2).bind fun h =>
  (rowLaidS h.1 (hidingLen ds) h.2).map fun L' =>
    ((c.1, { r := m, claimed := AffSh.mk [] [], ends := slotsSh h.1.sEnd ends, psc := some h.1 }),
      L')

theorem HearSh.heardBy (lead : Nat) (C : Array Hid → Kinds.Form) (CS : List AffSh → AffSh)
    (hC : ∀ c, affSh (C c) = CS (c.toList.map hidSh)) (z : Point) (ends : Nat) :
    HearSh (Kinds.heardBy lead C z ends) (fun x => (x.1.toList.map hidSh, kSumSh x.2))
      (heardByS lead CS z.size ends) := by
  intro F rs a G left y hx hf
  unfold Kinds.heardBy at hx
  obtain ⟨rs₀, F₁, l₁, h1, k1⟩ := hear_bind hx
  obtain ⟨v, F₂, l₂, h2, k2⟩ := hear_bind k1
  obtain ⟨c, F₃, l₃, h3, k3⟩ := hear_bind k2
  obtain ⟨Fl, F₄, l₄, h4, k4⟩ := hear_bind k3
  obtain ⟨⟨h, Gh⟩, F₅, l₅, h5, k5⟩ := hear_bind k4
  obtain ⟨Gr, F₆, l₆, h6, k6⟩ := hear_bind k5
  obtain ⟨u, F₇, l₇, h7, k7⟩ := hear_bind k6
  obtain ⟨es, F₈, l₈, h8, k8⟩ := hear_bind k7
  clear hx k1 k2 k3 k4 k5 k6 k7
  obtain rfl : F₁ = F := hear_stretch h1
  obtain ⟨v1, v2⟩ := hear_need h2
  obtain rfl : F₂ = F₁ := congrArg (·.1) v2
  have hv : v.length = lead := leadScalars_length v1
  obtain ⟨rfl, rfl⟩ : F₃ = Fl ∧ F₃ = F₄ := by
    have q : (F₃, F₃, l₃) = (Fl, F₄, l₄) := Option.some.inj h4
    exact ⟨congrArg (·.1) q, congrArg (·.2.1) q⟩
  obtain ⟨w1, -⟩ := hear_need h5
  obtain ⟨x1, -⟩ := hear_need h6
  obtain rfl : Gr = F₇ := by
    have q : ((), Gr, l₆) = (u, F₇, l₇) := Option.some.inj h7
    exact congrArg (·.2.1) q
  have q := hear_pure k8
  obtain ⟨rfl, rfl⟩ : a = (c, _) ∧ F₈ = G := ⟨congrArg (·.1) q, (congrArg (·.2.1) q).symm⟩
  -- the step, line by line
  unfold heardByS at hf
  obtain ⟨c', hc', hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨m', hm', hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨L', hL', rfl⟩ := Option.map_eq_some_iff.1 hf
  rw [← hv] at hc'
  obtain rfl := HearSh.hide v F₂ l₂ c F₃ l₃ c' h3 hc'
  have hds : (Part.MaskedSum.Call.all ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩).map Var.d =
      List.replicate z.size 3 ++ [3] := by
    show ((z.toList.map (Var.point · 3)) ++ [Var.point zeroE (2 + 1)]).map Var.d = _
    rw [List.map_append, List.map_map]
    congr 1
    rw [← Array.length_toList]
    exact List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hb
      rfl⟩
  have hm2 : msHearS (affSh (C c))
      ((Part.MaskedSum.Call.all ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩).map Var.d)
      (ownSlots (Part.MaskedSum.Call.all ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩))
      (⟨2, ends⟩ : Ends).n (ledSh F₃) = some m' := by
    rw [ownSlots_d, hds, hC]
    exact hm'
  obtain rfl := ms_hear_sh rfl w1 hm2
  have hdeg : h.vars.map Var.d = List.replicate z.size 3 ++ [3] ∧
      h.r.length = (List.replicate z.size 3 ++ [3]).length := by
    unfold msHearS at hm'
    split at hm'
    · have e := congrArg (·.1) (Option.some.inj hm')
      exact ⟨(congrArg SumSh.degrees e).symm, (congrArg SumSh.r e).symm⟩
    · cases hm'
  have hlen : h.r.length = h.vars.length := by
    rw [hdeg.2, ← hdeg.1, List.length_map]
  obtain rfl := rowLaid_sh x1 (y := L') (by
    rw [zip_degrees h.vars h.r hlen, hdeg.1]
    exact hL')
  have e8 := HearSh.hiddenFrom h.sEnd ends Gr l₇ es F₈ l₈ _ h8 rfl
  have e8a : slotsSh h.sEnd ends = es.toList.map hidSh := congrArg (·.1) e8
  have e8b : ledSh Gr = ledSh F₈ := congrArg (·.2) e8
  have hr : (Part.MaskedSum.challenges
      ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩ h).toArray.size = z.size := by
    show ((h.r.take (z.toList.map (Var.point · 3)).length)).toArray.size = _
    rw [List.size_toArray, List.length_take, List.length_map, Array.length_toList, hdeg.2,
      List.length_append, List.length_replicate]
    simp
  refine Prod.ext (Prod.ext rfl ?_) e8b
  show KSumSh.mk z.size (AffSh.mk [] []) (slotsSh h.sEnd ends) (some (sumSh h)) =
    KSumSh.mk _ (hidSh {}) (es.toList.map hidSh) (some (sumSh h))
  rw [hr, e8a]
  rfl

/-! ## 3 The two forms of a call -/

/-- A sumcheck whose claimed sum the prover sends, on shapes. The two defaults (the empty form at an
empty list) are never taken: behind heardByS 1 the lead's list has one member. -/
def sumcheckS (m ends : Nat) (L : LedSh) : Option (KSumSh × LedSh) :=
  (heardByS 1 (fun c => c.getD 0 (AffSh.mk [] [])) m ends L).map fun y =>
    ({ y.1.2 with claimed := y.1.1.getD 0 (AffSh.mk [] []) }, y.2)

theorem HearSh.sumcheck (z : Point) (ends : Nat) :
    HearSh (Kinds.sumcheck z ends) kSumSh (sumcheckS z.size ends) := by
  intro F rs a G left y hx hf
  unfold Kinds.sumcheck at hx
  obtain ⟨⟨c, s⟩, F₁, l₁, h1, k1⟩ := hear_bind hx
  have q := hear_pure k1
  obtain ⟨rfl, rfl⟩ : a = _ ∧ F₁ = G := ⟨congrArg (·.1) q, (congrArg (·.2.1) q).symm⟩
  obtain ⟨y₁, hy, rfl⟩ := Option.map_eq_some_iff.1 hf
  have hC : ∀ c : Array Hid, affSh ((c.getD 0 {}).var) =
      (c.toList.map hidSh).getD 0 (AffSh.mk [] []) := by
    intro c
    rcases c with ⟨l⟩
    cases l <;> rfl
  obtain rfl := HearSh.heardBy 1 (fun c => (c.getD 0 {}).var) _ hC z ends F rs (c, s) F₁ l₁ y₁ h1 hy
  refine Prod.ext ?_ rfl
  show KSumSh.mk _ ((c.toList.map hidSh).getD 0 (AffSh.mk [] [])) _ _ =
    KSumSh.mk _ (hidSh (c.getD 0 {})) _ _
  rw [← hC c]
  rfl

/-- A level: the start form is fixed before; a last round hands one element down. -/
def levelS (start : AffSh) (m : Nat) (L : LedSh) : Option (KSumSh × LedSh) :=
  (heardByS 0 (fun _ => start) m 2 L).map fun y => (y.1.2, y.2)

theorem HearSh.level (z : Point) (start : Kinds.Form) :
    HearSh (Kinds.level z start) kSumSh (levelS (affSh start) z.size) := by
  intro F rs a G left y hx hf
  unfold Kinds.level at hx
  obtain ⟨⟨c, s⟩, F₁, l₁, h1, k1⟩ := hear_bind hx
  obtain ⟨⟨v, g⟩, F₂, l₂, h2, k2⟩ := hear_bind k1
  obtain ⟨e, F₃, l₃, h3, k3⟩ := hear_bind k2
  have q := hear_pure k3
  obtain ⟨rfl, rfl⟩ : a = _ ∧ F₃ = G := ⟨congrArg (·.1) q, (congrArg (·.2.1) q).symm⟩
  obtain rfl : F₃ = F₂ := congrArg (·.1) (hear_need h3).2
  have e2 := HearSh.round 0 1 F₁ l₁ (v, g) F₃ l₂ _ h2 rfl
  have eF : ledSh F₁ = ledSh F₃ := congrArg (·.2) e2
  obtain ⟨y₁, hy, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain rfl := HearSh.heardBy 0 (fun _ => start) (fun _ => affSh start) (fun _ => rfl) z 2 F rs
    (c, s) F₁ l₁ y₁ h1 hy
  exact Prod.ext rfl eF

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.HearSh.drawPoint
#print axioms VerifiableInference.Desc.First.Shape.hear_bind
#print axioms VerifiableInference.Desc.First.Shape.hear_pure
#print axioms VerifiableInference.Desc.First.Shape.hear_need
#print axioms VerifiableInference.Desc.First.Shape.HearSh.sendThenBatch
#print axioms VerifiableInference.Desc.First.Shape.ownSlots_d
#print axioms VerifiableInference.Desc.First.Shape.zip_degrees
#print axioms VerifiableInference.Desc.First.Shape.leadScalars_length
#print axioms VerifiableInference.Desc.First.Shape.hear_stretch
#print axioms VerifiableInference.Desc.First.Shape.HearSh.heardBy
#print axioms VerifiableInference.Desc.First.Shape.HearSh.sumcheck
#print axioms VerifiableInference.Desc.First.Shape.HearSh.level
#print axioms VerifiableInference.Desc.First.Shape.ownD
#print axioms VerifiableInference.Desc.First.Shape.heardByS
#print axioms VerifiableInference.Desc.First.Shape.sumcheckS
#print axioms VerifiableInference.Desc.First.Shape.levelS
