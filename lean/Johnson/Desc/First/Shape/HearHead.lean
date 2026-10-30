-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HearHead.lean: THE HEARING OF THE OUTPUT HEAD's OWN ROUNDS
(Kinds.Head.hear, Johnson/Desc/Kinds/Head.lean: the normalization's, Norm.lean; the final
normalization's, HeadNorm.lean; the head's one sumcheck) IN THE FRAME OF HearFrame.lean: one step on
the ledger's shape, which returns the shape of all that is heard and of the ledger behind. General
laws; nothing is evaluated.
  1 Forms: `AffSh.nil_append`, `affSh_scale` (a multiple has the form's shape), `sumToSh`,
    `affSh_sumTo`.
  2 `NormSh`, `normSh`; `squaresStartSh`, `getD_hidSh`, `squaresStart_sh`: the shape of the form
    that the sums of squares must equal: of the shapes of the nine sums a norm. `join_point`: a
    point that is drawn only where a test on the plan fails. `normS`, **`HearSh.norm`**: a point on
    the positions; 9 NI scalars; the level of the squares; 7 NI scalars; the sumcheck of the
    products.
  3 `HeardAllSh`, `heardAllSh`; `headS zt`, **`HearSh.head`**: the normalization; a sumcheck at the
    lookup's point on the positions, of zt coordinates; a sumcheck in zt + lPd variables. zt is the
    size of a point that comes in from the lookup.
By HearJoined.lean's HearSh.drawPoint, sendThenBatch, sumcheck, level; Parts.lean's affSh_addMul,
affSh_add.
Limits. THE WEAK FORM, as in HearFrame.lean: under the step's own return. That the hearing returns
where the step does is not said. The drawn elements (the two that batch; the one that a level hands
down) and every shown scalar are left out. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HearJoined
import Johnson.Desc.Kinds.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Kinds (Hear Hid Sum Point)
open scoped VerifiableInference.Desc.Kinds

/-! ## 1 Forms: a multiple; a sum -/

theorem AffSh.nil_append (a : AffSh) : (AffSh.mk [] []).append a = a := rfl

theorem affSh_scale (a : Aff) (k : E) : affSh (a.scale k) = affSh a := by
  unfold Aff.scale
  rw [affSh_addMul]
  rfl

/-- The shapes of n forms, one behind the other. -/
def sumToSh (n : Nat) (g : Nat → AffSh) : AffSh :=
  (List.range n).foldl (fun s i => s.append (g i)) (AffSh.mk [] [])

theorem affSh_sumTo (n : Nat) (f : Nat → Kinds.Form) (g : Nat → AffSh)
    (h : ∀ i, affSh (f i) = g i) : affSh (Kinds.sumTo n f) = sumToSh n g := by
  unfold Kinds.sumTo sumToSh
  have : ∀ (l : List Nat) (a : Kinds.Form) (b : AffSh), affSh a = b →
      affSh (l.foldl (fun s i => s + f i) a) = l.foldl (fun s i => s.append (g i)) b := by
    intro l
    induction l with
    | nil => exact fun _ _ e => e
    | cons i l ih =>
      intro a b e
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (by rw [affSh_add, e, h])
  exact this _ _ _ rfl

/-! ## 2 The normalization's hearing -/

/-- The shape of what the normalization's steps leave; the two batching elements are left out. -/
structure NormSh where
  pV : Nat
  W : List AffSh
  rhoI : Nat
  squares : KSumSh
  P : List AffSh
  products : KSumSh

def normSh (h : Kinds.Norm.Heard) : NormSh :=
  { pV := h.pV.size, W := h.W.toList.map hidSh, rhoI := h.rhoI.size, squares := kSumSh h.squares
    P := h.P.toList.map hidSh, products := kSumSh h.products }

/-- What the sums of squares must equal, on shapes. -/
def squaresStartSh (NI : Nat) (W : List AffSh) : AffSh :=
  sumToSh NI fun i => sumToSh 9 fun s => W.getD (9 * i + s) (AffSh.mk [] [])

theorem getD_hidSh (W : Array Hid) (j : Nat) :
    affSh (W.getD j {}).var = (W.toList.map hidSh).getD j (AffSh.mk [] []) := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases W[j]? <;> rfl

/-- A point that is drawn only where a test on the plan fails; K: what follows. -/
theorem join_point {α : Type} {c : Bool} {n : Nat} {K : Point → Hear α} {F : Fork}
    {rs : List Fmt.RoundView} {r : α × Fork × List Fmt.RoundView}
    (h : (if c = true then (Pure.pure #[] : Hear Point) >>= K else Kinds.drawJoin n >>= K) F rs =
      some r) :
    ∃ rho G l, ((if c then 0 else n) = rho.size ∧ ledSh F = ledSh G) ∧ K rho G l = some r := by
  cases c with
  | true =>
    obtain ⟨rho, G, l, h1, h2⟩ := hear_bind (x := (Pure.pure #[] : Hear Point)) (k := K) h
    have q := hear_pure h1
    obtain ⟨rfl, rfl⟩ : rho = #[] ∧ G = F := ⟨congrArg (·.1) q, congrArg (·.2.1) q⟩
    exact ⟨_, _, l, ⟨rfl, rfl⟩, h2⟩
  | false =>
    obtain ⟨rho, G, l, h1, h2⟩ := hear_bind (x := Kinds.drawJoin n) (k := K) h
    have e := HearSh.drawPoint n F rs rho G l _ h1 rfl
    exact ⟨rho, G, l, ⟨congrArg (·.1) e, congrArg (·.2) e⟩, h2⟩

section
variable [Kinds.Norm.Sizes]
local notation "lt" => Kinds.Norm.lt
local notation "lPd" => Kinds.Norm.lPd
local notation "lNI" => Kinds.Norm.lNI
local notation "NI" => Kinds.Norm.NI

theorem squaresStart_sh (W : Array Hid) (gam : E) (rhoI : Point) :
    affSh (Kinds.Norm.squaresStart W gam rhoI) = squaresStartSh NI (W.toList.map hidSh) := by
  unfold Kinds.Norm.squaresStart squaresStartSh
  show affSh (Aff.scale _ _) = _
  rw [affSh_scale]
  refine affSh_sumTo _ _ _ fun i => affSh_sumTo _ _ _ fun s => ?_
  show affSh (Aff.scale _ _) = _
  rw [affSh_scale, getD_hidSh]

/-- The normalization's hearing on shapes. -/
def normS (L : LedSh) : Option (NormSh × LedSh) :=
  (hideS (9 * NI) L).bind fun W =>
  (levelS (squaresStartSh NI W.1) ((if lNI == 0 then 0 else lNI) + lPd + lt) W.2).bind fun q =>
  (hideS (7 * NI) q.2).bind fun P =>
  (sumcheckS lt (4 * NI) P.2).map fun r =>
    (⟨lt, W.1, if lNI == 0 then 0 else lNI, q.1, P.1, r.1⟩, r.2)

theorem HearSh.norm : HearSh Kinds.Norm.hear normSh normS := by
  intro F rs a G left y hx hf
  unfold Kinds.Norm.hear at hx
  obtain ⟨pV, F₁, l₁, h1, k1⟩ := hear_bind hx
  unfold Kinds.Norm.hearRest at k1
  obtain ⟨⟨W, gam⟩, F₂, l₂, h2, k2⟩ := hear_bind k1
  obtain ⟨rhoI, F₃, l₃, e3, k3⟩ := join_point (n := lNI) (c := lNI == 0) k2
  obtain ⟨sq, F₄, l₄, h4, k4⟩ := hear_bind k3
  obtain ⟨⟨P, om⟩, F₅, l₅, h5, k5⟩ := hear_bind k4
  obtain ⟨pr, F₆, l₆, h6, k6⟩ := hear_bind k5
  clear hx k1 k2 k3 k4 k5
  have q := hear_pure k6
  obtain ⟨rfl, rfl⟩ : a = _ ∧ F₆ = G := ⟨congrArg (·.1) q, (congrArg (·.2.1) q).symm⟩
  have e1 := HearSh.drawPoint lt F rs pV F₁ l₁ _ h1 rfl
  have e1a : lt = pV.size := congrArg (·.1) e1
  have e1b : ledSh F = ledSh F₁ := congrArg (·.2) e1
  unfold normS at hf
  obtain ⟨W', hW, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨q', hq, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨P', hP, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 hf
  rw [e1b] at hW
  obtain rfl := HearSh.sendThenBatch (9 * NI) 9 F₁ l₁ (W, gam) F₂ l₂ W' h2 hW
  have hz : (rhoI ++ Kinds.halves lPd ++ pV).size = (if lNI == 0 then 0 else lNI) + lPd + lt := by
    rw [Array.size_append, Array.size_append, e3.1, e1a]
    show _ + (Array.replicate lPd Kinds.half).size + _ = _
    rw [Array.size_replicate]
  have hq' : levelS (affSh (Kinds.Norm.squaresStart W gam rhoI))
      (rhoI ++ Kinds.halves lPd ++ pV).size (ledSh F₃) = some q' := by
    rw [squaresStart_sh, hz, ← e3.2]
    exact hq
  obtain rfl := HearSh.level _ _ F₃ l₃ sq F₄ l₄ q' h4 hq'
  obtain rfl := HearSh.sendThenBatch (7 * NI) (7 * NI) F₄ l₄ (P, om) F₅ l₅ P' h5 hP
  rw [e1a] at hr
  obtain rfl := HearSh.sumcheck pV (4 * NI) F₅ l₅ pr F₆ l₆ r' h6 hr
  refine Prod.ext ?_ rfl
  show NormSh.mk lt _ (if lNI == 0 then 0 else lNI) _ _ _ = NormSh.mk pV.size _ rhoI.size _ _ _
  rw [e1a, e3.1]
  rfl

end

/-! ## 3 The final normalization's and the head's hearings -/

/-- The shape of all that the output head's own rounds leave. -/
structure HeardAllSh where
  norm : NormSh
  normed : KSumSh
  logits : KSumSh

def heardAllSh (H : Kinds.Head.HeardAll) : HeardAllSh :=
  { norm := normSh H.1, normed := kSumSh H.2.1.normed, logits := kSumSh H.2.2.logits }

section
variable [Kinds.Head.Sizes] [Kinds.FinalNorm.In]

/-- The whole hearing on shapes. zt: the number of coordinates of the lookup's point on the
positions. -/
def headS (zt : Nat) (L : LedSh) : Option (HeardAllSh × LedSh) :=
  (normS L).bind fun n =>
  (sumcheckS zt 2 n.2).bind fun f =>
  (sumcheckS (zt + Kinds.Norm.lPd) 2 f.2).map fun h => (⟨n.1, f.1, h.1⟩, h.2)

theorem HearSh.head :
    HearSh Kinds.Head.hear heardAllSh (headS (Kinds.FinalNorm.zt).size) := by
  intro F rs a G left y hx hf
  unfold Kinds.Head.hear at hx
  obtain ⟨n, F₁, l₁, h1, k1⟩ := hear_bind hx
  obtain ⟨f, F₂, l₂, h2, k2⟩ := hear_bind k1
  obtain ⟨g, F₃, l₃, h3, k3⟩ := hear_bind k2
  clear hx k1 k2
  have q := hear_pure k3
  obtain ⟨rfl, rfl⟩ : a = _ ∧ F₃ = G := ⟨congrArg (·.1) q, (congrArg (·.2.1) q).symm⟩
  unfold Kinds.FinalNorm.hear at h2
  obtain ⟨nm, F₂', l₂', h2a, k2a⟩ := hear_bind h2
  have q2 := hear_pure k2a
  obtain ⟨rfl, rfl⟩ : f = _ ∧ F₂' = F₂ := ⟨congrArg (·.1) q2, (congrArg (·.2.1) q2).symm⟩
  obtain rfl : l₂' = l₂ := (congrArg (·.2.2) q2).symm
  unfold headS at hf
  obtain ⟨n', hn, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨f', hf', hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨g', hg, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain rfl := HearSh.norm F rs n F₁ l₁ n' h1 hn
  obtain rfl := HearSh.sumcheck _ 2 F₁ l₁ nm F₂' l₂' f' h2a hf'
  have hz : (Kinds.FinalNorm.zt ++ Kinds.halves Kinds.Norm.lPd).size =
      (Kinds.FinalNorm.zt).size + Kinds.Norm.lPd := by
    rw [Array.size_append]
    show _ + (Array.replicate Kinds.Norm.lPd Kinds.half).size = _
    rw [Array.size_replicate]
  rw [← hz] at hg
  obtain rfl := HearSh.sumcheck _ 2 F₂' l₂' g F₃ l₃ g' h3 hg
  rfl

end

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.AffSh.nil_append
#print axioms VerifiableInference.Desc.First.Shape.affSh_scale
#print axioms VerifiableInference.Desc.First.Shape.affSh_sumTo
#print axioms VerifiableInference.Desc.First.Shape.getD_hidSh
#print axioms VerifiableInference.Desc.First.Shape.join_point
#print axioms VerifiableInference.Desc.First.Shape.squaresStart_sh
#print axioms VerifiableInference.Desc.First.Shape.HearSh.norm
#print axioms VerifiableInference.Desc.First.Shape.HearSh.head
#print axioms VerifiableInference.Desc.First.Shape.sumToSh
#print axioms VerifiableInference.Desc.First.Shape.NormSh
#print axioms VerifiableInference.Desc.First.Shape.normSh
#print axioms VerifiableInference.Desc.First.Shape.squaresStartSh
#print axioms VerifiableInference.Desc.First.Shape.normS
#print axioms VerifiableInference.Desc.First.Shape.HeardAllSh
#print axioms VerifiableInference.Desc.First.Shape.heardAllSh
#print axioms VerifiableInference.Desc.First.Shape.headS
