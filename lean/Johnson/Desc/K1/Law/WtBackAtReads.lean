-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/WtBackAtReads.lean: K01's TOPS' BINDER
hwtR (the sentence "weights" of segment l goes back over the accept of the segment's sending of
the reads, at every l < 25), TO THE LETTER of k01_fifty_at9's head but for the letters N | Mg |
wt, BY CALLS into Johnson/Desc/Kinds/Law/ (KeptWLegs.lean · WeightAtSame.lean). Three theorems.

How. At l ≠ 24 the sentence says nothing (hidle: so it is at the closed constant's wt: "m = 24 →
…"). At l = 24 (number 342): the binder's YesOf hands the bare sub-protocol's decision: K1.laterAt
… with the quiet step joined: where that step is the head's (hquiet), keptW_reads_laid
gives KeptW; weightAt_kept carries WeightAt back; hmono carries wt.

  stand_342 · hhead_342  in front of 342 the state stands in a head's segment: off the promise's own
                         clause on where the chain stands (the kernel).
  hwtR_of                **the binder.**
LEFT, BY NAME: hidle (wt l holds of everything at l ≠ 24) · hmono (as in WtAt24.lean) · hheard
(the head's reader answers in front of 342: heard_at_T) · hquiet (segment 24's quiet step
behind the reads is the head's).
What is not claimed. That any of the four can be met. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.WtAt24

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
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept keptW_reads_laid
  readsOf)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (k1Ix k1Reads k1Quiet)

theorem stand_342 : First.standAt linksFull (IM.k1PlaceL 24 false) = .link .head := by
  decide +kernel

/-- In front of 342 the state stands in a head's segment. -/
theorem hhead_342 {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (x : Pp × S) (y : Strs)
    (h : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∃ o, x.2.here = .head o := by
  obtain ⟨h, hm⟩ := h
  rcases h.2 with hx | ⟨h1, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    have hs : First.shapeAt linksFull (flatPlacesOf linksFull true)[noL 24 false]? x.2 = true :=
      h1.1.1.1.1.1
    have hp : (flatPlacesOf linksFull true)[noL 24 false]? = some (IM.k1PlaceL 24 false) :=
      place_fifty 24 (by omega) false
    rw [hp] at hs
    unfold First.shapeAt at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    have h2 : First.standOf x.2 = .link .head := hs.1.1.trans stand_342
    unfold First.standOf at h2
    cases hh : x.2.here with
    | head o => exact ⟨o, rfl⟩
    | _ => simp [hh] at h2

/-- **hwtR.** -/
theorem hwtR_of {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {Tok : Type} {rows cols : ℕ} (N : Numbers)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (wt : ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (Wp : OnBytes.Model.Verify.Public)
    (hidle : ∀ l, l ≠ 24 → ∀ a y w, wt l a y w)
    (hmono : ∀ (a a' : ProofFile.InstPub × S) y y' w,
      (∀ cc mm, WeightAt Wp a'.2 cc mm → WeightAt Wp a.2 cc mm) → wt 24 a' y' w → wt 24 a y w)
    (hheard : ∀ x y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 false) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H)
    (hquiet : ∀ X, Bs.G₀.built[24]? = some X → ∃ P, k1Quiet Bs.G₀ 24 X = ReadsQuiet.head P) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y' w,
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → wt l x' y' w → wt l x y w := by
  intro l _ X arrs hX x x' y y' w hy hIn _ h0
  by_cases hl : l = 24
  · subst hl
    obtain ⟨o, ho⟩ := hhead_342 N Mg x y hIn
    obtain ⟨_, rs, gs, _, hd⟩ := hy
    obtain ⟨P, hP⟩ := hquiet X hX
    unfold blkL k1Reads at hd
    dsimp only at hd
    rw [hP] at hd
    exact hmono x x' y y' w
      (fun cc mm => (weightAt_kept Wp (keptW_reads_laid ho hd) (hheard x y hIn) cc mm).1) h0
  · exact hidle l hl x y w

end VerifiableInference.Desc.K1
