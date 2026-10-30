-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/WtAt24.lean: K01_law's BINDER hwt (the sentence on a segment's claim on the
weights goes back over a later sending's accept), WHOLE, TO THE LETTER of k01_law_whole's head, BY
CALLS of Desc/Kinds/Law/KeptWLegs.lean and WeightAtSame.lean. Two tests with code, seven theorems.

THE FIND THAT MAKES IT SHORT [the kernel]: of the kind's fifty later places an item forms m j
"weights" is open in front of ONE ALONE: (l, d) = (24, true), number 344, the output head's third
sending; there it is forms 24 4 "weights". At the other forty-nine the binder is met emptily.

How, at 344. The binder's YesOf hands the BARE sub-protocol's decision at the state x.2, with the
public part unturned: so "from the seated piece's accept to the decision" and "the lift from the
state to the public part with the state" are paid by the binder's own form. The sub-protocol is
K1.laterAt …: keptW_sending gives KeptW; weightAt_kept carries WeightAt back; hmono
carries wt.

OBJECT   the piece number 344 of the first chain (segment 24, K1's last sending).
USER     k01_law_whole's binder hwt.
FIELD    K01_law (ProofSound).

  wtSegB · wtSeg_24 · hseg_24     an item forms m j "weights" open in front of 344 | 342 has m = 24.
  wtNoneB · wtNone_full · hnone   no such item is open in front of the other forty-nine.
  stand_344 · hhead_344           in front of 344 the state stands in a head's segment: off the
                                  promise's own clause on where the chain stands.
  hwt_whole                       **the binder.**
LEFT, BY NAME: hmono (wt 24 reads the state through WeightAt alone, positively, and no oracle's
string: weaker than an equation for wt; it leans on no term of the composed meaning's parameters)
· hheard (the head's reader answers in front of 344: heard_at_F
(Desc/Kinds/Law/WeightHeardAt.lean) pays it off the table's promise, under its own three premises).
What is not claimed. That either of the two can be met. The like for items formsT. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.K01LawWhole
import Johnson.Desc.Kinds.Law.KeptWLegs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept keptW_sending readsOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (k1Ix)

/-- Every item forms m j "weights" that is open in front of the place (l, d) has m = l. -/
def wtSegB (l : ℕ) (d : Bool) : Bool :=
  (openAt linksFull (flatPlacesOf linksFull true) (noL l d)).all fun i =>
    match i with
    | .forms m _ r => r != "weights" || m == l
    | _ => true

set_option maxRecDepth 1000000 in
theorem wtSeg_24 : wtSegB 24 true = true ∧ wtSegB 24 false = true := by decide +kernel

theorem hseg_24 (d : Bool) (m j : ℕ)
    (h : Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL 24 d)) : m = 24 := by
  have hb : wtSegB 24 d = true := by
    cases d
    · exact wtSeg_24.2
    · exact wtSeg_24.1
  have h1 := List.all_eq_true.1 hb _ h
  simpa using h1

/-- No item forms m j "weights" is open in front of the place (l, d). -/
def wtNoneB (l : ℕ) (d : Bool) : Bool :=
  (openAt linksFull (flatPlacesOf linksFull true) (noL l d)).all fun i =>
    match i with
    | .forms _ _ r => r != "weights"
    | _ => true

set_option maxRecDepth 1000000 in
theorem wtNone_full : ((List.range 25).all fun l => [true, false].all fun d =>
    (l == 24 && d) || wtNoneB l d) = true := by decide +kernel

theorem hnone (l : ℕ) (hl : l < 25) (d : Bool) (m j : ℕ)
    (h : Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d)) :
    l = 24 ∧ d = true := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 wtNone_full l (List.mem_range.2 hl)) d
    (by cases d <;> simp)
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · simpa using h2
  · have h3 := List.all_eq_true.1 h2 _ h
    simp at h3

theorem stand_344 : First.standAt linksFull (IM.k1PlaceL 24 true) = .link .head := by
  decide +kernel

/-- **In front of 344 the state stands in a head's segment**: off the promise's clause on where the
chain stands. -/
theorem hhead_344 {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (x : Pp × S) (y : Strs)
    (h : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 true) x y) : ∃ o, x.2.here = .head o := by
  obtain ⟨h, hm⟩ := h
  rcases h.2 with hx | ⟨h1, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    have hs : First.shapeAt linksFull (flatPlacesOf linksFull true)[noL 24 true]? x.2 = true := h1.1.1.1.1.1
    have hp : (flatPlacesOf linksFull true)[noL 24 true]? = some (IM.k1PlaceL 24 true) :=
      place_fifty 24 (by omega) true
    rw [hp] at hs
    unfold First.shapeAt at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    have h2 : First.standOf x.2 = .link .head := hs.1.1.trans stand_344
    unfold First.standOf at h2
    cases hh : x.2.here with
    | head o => exact ⟨o, rfl⟩
    | _ => simp [hh] at h2

/-- **hwt, whole.** -/
theorem hwt_whole {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {Tok : Type} {rows cols : ℕ} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (wt : ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (Wp : OnBytes.Model.Verify.Public)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → wt 24 a' y' w → wt 24 a y w)
    (hheard : ∀ x y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 true) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y y' w m j, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow (baseL aN R₁ R₂ R₃ c l d) y y' →
      Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) → wt m x' y' w → wt m x y w := by
  intro l hl d X arrs _ x x' y y' w m j hy hIn _ hi h0
  obtain ⟨rfl, rfl⟩ := hnone l hl d m j hi
  obtain rfl := hseg_24 true m j hi
  obtain ⟨o, ho⟩ := hhead_344 N Mg x y hIn
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  exact hmono x x' y y' w
    (fun cc mm => (weightAt_kept Wp (keptW_sending ho hd) (hheard x y hIn) cc mm).1) h0

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.wtSeg_24
#print axioms VerifiableInference.Desc.K1.hseg_24
#print axioms VerifiableInference.Desc.K1.wtNone_full
#print axioms VerifiableInference.Desc.K1.hnone
#print axioms VerifiableInference.Desc.K1.stand_344
#print axioms VerifiableInference.Desc.K1.hhead_344
#print axioms VerifiableInference.Desc.K1.hwt_whole
