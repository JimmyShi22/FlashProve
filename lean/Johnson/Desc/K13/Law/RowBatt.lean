-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RowBatt.lean: THE KIND K13's FILES' LAW goodIn_any (GoodAny.lean) AT OTHER FILES' RELATIONS: general in the state, the block and the frame.
  pieceAt_is   that law's piece IS the maker's pieceOf at the stretch dZ :: d0 :: ds, nothing put back, the extractor that hands the witness on, the law's own errors: by rfl
  batt_good    goodIn_any's premises, and two more: behind: the caller's relation gives «the pin, and all of rowB's rows are true»; in front: «the pin, and all rows of the part's pile are true» gives the caller's: GoodIn at the caller's relations
hback has the promise in front. Nothing is paid here. Nothing on soundness.
-/
import Johnson.Desc.K13.Law.GoodAny
import Johnson.Top.Fire.Code.RowGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {T Cl W : Type} {nR : ℕ}

theorem pieceAt_is (F : Frame) (b : Block T Cl) (rows base : ℕ) (dZ d0 : RDT) (ds : List RDT) :
    pieceAt (W := W) F b rows base dZ d0 ds =
      Sound.pieceOf b base (dZ :: d0 :: ds) [] ⟨fun _ _ w => w, (mapsOf dZ d0 ds).err (errK rows ds.length)⟩ := rfl

theorem batt_good (F : Frame) (P : Where) (b : Block T Cl) (base : ℕ) (dZ d0 : RDT)
    (ds : List RDT) (hD : Declared P dZ d0 ds) (k : ℕ) (hk : ds.length = k)
    (partF : T → Option Part) (rowB : T → List TensorRow) (hb : ByBatt b P partF rowB)
    (rw : W → Wit GE nR k) (Pin : T × F.E.Str → W → Prop) (on on' : T × F.E.Str → Prop)
    (hdet : ∀ a p w w', on a → partF a.1 = some p → Pin a w → Pin a w' → AgreeAt p.indexMasks (rw w) (rw w'))
    (hback : ∀ a τ b' w, on a → (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → Pin b' w → Pin a w)
    (hon : ∀ a τ b', on a → (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → on' b')
    (Rn Rn' : T × F.E.Str → W → Prop)
    (hbehind : ∀ a τ b' w, on a → (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → on' b' → Rn' b' w →
      Pin b' w ∧ ∀ r ∈ rowB b'.1, Holds ρg (rw w) r)
    (hfront : ∀ a τ b' w, on a → (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → on' b' → Rn' b' w →
      (Pin a w ∧ ∀ p, partF a.1 = some p → ∀ r ∈ p.pile, Holds ρg (rw w) r) → Rn a w) :
    (pieceAt (W := W) F b P.rows base dZ d0 ds).GoodIn on on' Rn Rn' :=
  LPFD.GoodIn.change (goodIn_any F P b base dZ d0 ds hD k hk partF rowB hb rw Pin on on' hdet hback hon)
    (fun _ _ _ => rfl) hbehind hfront

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.pieceAt_is
#print axioms VerifiableInference.Desc.K13.Law.batt_good
