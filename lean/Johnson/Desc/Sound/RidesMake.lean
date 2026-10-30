-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/RidesMake.lean: "FOR CERTAIN: WHAT EACH SLOT HAS OF ITS OWN RIDES" (the clause that the rule for the stretch behind "LIN point" asks of every block there: EachRides), PAID BY MAKE. One statement written as def … : Prop, and its
proof.

Behind the point a slot's own items are five: no mark · the index masks' pin · W's pin · (Eval) · (Dot). No block there closes or opens one of them. RidesAt: at one block x of that stretch, with the table's extractor e at it: at every yes from a
to b inside the promise: the slot's own condition holds behind, and for every witness w: the five at (b, w) give the five at (a, e (the acting part's value at a) w): THE CLAUSE OF EachRides, TO THE LETTER. FROM:
  (K) what was handed to the chain stays (the seat's make) · (Oc) the slot's own condition reads the stored table and the trees below lo alone, and the block's stretch begins from lo on (ocRides)
  (P) the slot's pins read the oracles through their tenant's tree alone; W's and the index masks' trees lie below the block's base
  (V) (Eval) reads no oracle · (D1) (Dot) reads no oracle, and the shared record through ONE reader psiOf alone (the point that was drawn) · (D2) the block leaves that reader's value as it was
  (E) the extractor keeps the four that read the witness (it lays messages of this chain; the four read W's, the index masks' and Omega's components: where the block lays Omega's or u's, see Limits).

Limits. A rule under letters. (E) AT (Dot): (Dot) reads Omega's component: it is kept by every extractor BUT THE ONE THAT LAYS OMEGA's: in this table NO BLOCK OF THE SHARED CHAIN LAYS IT (the last chain's test does): a test on the table (laidOnce); so (E) is
payable at all ten blocks: by "the old part is kept" (ExtSSame) and "the item reads these components alone": owed at the fillings.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- **What each slot has of its own rides over a block behind the point.** -/
def RidesAt : Prop :=
  ∀ (P₁ S₂ Cl Wt Ψ : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (lo k : ℕ)
    (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (x : Piece C Fr (P₁ × S₂) Cl Wt) (e : (actQ N p l k).1 → Wt → Wt) (psiOf : S₂ → Ψ),
    (∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1) →
    OcReadsBelow lo Oc → lo ≤ x.base →
    (∀ j t q (y y' : Strs) w, (∀ z, y'.col j z = y.col j z) → Mg.pin₁ j t q y w → Mg.pin₁ j t q y' w) →
    N.w.1 < x.base → N.index.1 < x.base →
    (∀ q (y y' : Strs) w, Mg.ev q y w → Mg.ev q y' w) →
    (∀ q s s' (y y' : Strs) w, psiOf s' = psiOf s → Mg.dot q s y w → Mg.dot q s' y' w) →
    (∀ a τ b, x.ior.red.out a τ = some b → psiOf a.1.2 = psiOf b.1.2) →
    (∀ v q y w, Mg.pin₁ N.w.1 N.w.2 q y w → Mg.pin₁ N.w.1 N.w.2 q y (e v w)) →
    (∀ v q y w, Mg.pin₁ N.index.1 N.index.2 q y w → Mg.pin₁ N.index.1 N.index.2 q y (e v w)) →
    (∀ v q y w, Mg.ev q y w → Mg.ev q y (e v w)) →
    (∀ v q s y w, Mg.dot q s y w → Mg.dot q s y (e v w)) →
    ∀ a τ b, onQ₂ N Pm Oc split p l k a → x.ior.red.out a τ = some b →
      Oc b.1.1 (strsOf Fr b.2) ∧
        ∀ w, relOwn N Mg 2 b w → relOwn N Mg 2 a (e ((actQ N p l k).2 a) w)

theorem ridesAt : RidesAt := by
  intro P₁ S₂ Cl Wt Ψ C Fr N Mg Pm Oc split lo k p l x e psiOf hK hOc hlo hR hw hi hV hD1 hD2 hEw hEi hEv
    hEd a τ b ha hb
  refine ⟨ocRides (P₁ × S₂) P₁ Cl Wt C Fr Prod.fst lo Oc x hOc hlo hK a τ b ha.2 hb, fun w hown => ?_⟩
  have e1 := hK a τ b hb
  have own2 : ∀ i ∈ [ItemS.unmarked1, .pinI, .pinV, .ev, .dot], ownItem N Mg i b w := fun i hi' =>
    hown i hi'
  have three := pointRiders P₁ S₂ Cl Wt C Fr N Mg x (fun a' w' => e ((actQ N p l k).2 a') w') hK hR hw hi
    (fun a' q y w' h => hEw _ q y w' h) (fun a' q y w' h => hEi _ q y w' h) a τ b w
  intro i hi'
  have hi'' : i ∈ [ItemS.unmarked1, .pinI, .pinV, .ev, .dot] := hi'
  rcases List.mem_cons.1 hi'' with rfl | hi''
  · exact three _ (by decide) hb (own2 _ (by decide))
  rcases List.mem_cons.1 hi'' with rfl | hi''
  · exact three _ (by decide) hb (own2 _ (by decide))
  rcases List.mem_cons.1 hi'' with rfl | hi''
  · exact three _ (by decide) hb (own2 _ (by decide))
  rcases List.mem_cons.1 hi'' with rfl | hi''
  · have h : Mg.ev b.1.1 (strsOf Fr b.2) w := own2 .ev (by decide)
    rw [e1] at h
    exact hEv _ _ _ _ (hV _ _ _ _ h)
  · obtain rfl := List.mem_singleton.1 hi''
    have h : Mg.dot b.1.1 b.1.2 (strsOf Fr b.2) w := own2 .dot (by decide)
    rw [e1] at h
    exact hEd _ _ _ _ _ (hD1 _ _ _ _ _ _ (hD2 a τ b hb) h)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ridesAt
