-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySApp.lean: tools for making the maps from a chain's written rounds to its typed
rounds (`CarryS`, OnBytes/Flat/CarrySkip.lean) out of the maps of the chain's parts.

A typed chain is a list of blocks, each with a few rounds; the written chain has these rounds, and
some that the typed chain lacks. Here are the pieces from which a chain's maps are put together,
each with what `CarryS.tr` and `CarryS.Fits` say of it. No new kind of map: definitions over
`CarryS` and lemmas.

Main names:
  `CarryS.app F G`: the maps of two stretches behind each other; the second stretch's maps may read
    the first stretch's written transcript. `tr_app`, `Fits.app`.
  `CarryS.skips s`: all rounds of s are skipped. `tr_skips`, `fits_skips`.
  `CarryS.same s`: each round is read as itself. `tr_same`, `fits_same`.
  `CarryS.one fm fc`: one round. `tr_one`, `fits_one`: from a bound w on the written verifier
    messages that go to one typed message, and e · w ≤ e'.

Limits: those of CarrySkip.lean. No protocol occurs here.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CarrySkip

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob OnBytes.Slice

namespace CarryS

/-- Two stretches behind each other. The second stretch's maps may read the first stretch's written
transcript. -/
def app : {s s' t t' : Shape} → CarryS s s' → (Tr s → CarryS t t') → CarryS (s ++ t) (s' ++ t')
  | _, _, _, _, .nil, G => G ()
  | _, _, _, _, .step fm fc k, G => .step fm fc fun m c => (k m c).app fun τ => G (m, c, τ)
  | _, _, _, _, .skip k, G => .skip fun m c => (k m c).app fun τ => G (m, c, τ)

/-- The image of a transcript of two stretches: the two images behind each other. -/
theorem tr_app : ∀ {s s' t t' : Shape} (F : CarryS s s') (G : Tr s → CarryS t t') (τ : Tr s)
    (σ : Tr t), (F.app G).tr (Tr.app τ σ) =
      (F.tr τ).bind fun τ' => ((G τ).tr σ).map fun σ' => Tr.app τ' σ'
  | _, _, _, _, .nil, G, (), σ => by
      show (G ()).tr σ = ((G ()).tr σ).map fun σ' => σ'
      exact Option.map_id'.symm
  | _, _, _, _, .step fm fc k, G, (m, c, τ), σ => by
      show (fc m c).bind (fun c' => (((k m c).app fun τ => G (m, c, τ)).tr (Tr.app τ σ)).map
        fun x => (fm m, c', x)) = _
      rw [tr_app (k m c) (fun τ => G (m, c, τ)) τ σ]
      show _ = ((fc m c).bind fun c' => ((k m c).tr τ).map fun τ' => (fm m, c', τ')).bind _
      cases fc m c with
      | none => rfl
      | some c' =>
        cases (k m c).tr τ with
        | none => rfl
        | some τ' =>
          cases (G (m, c, τ)).tr σ with
          | none => rfl
          | some σ' => rfl
  | _, _, _, _, .skip k, G, (m, c, τ), σ => tr_app (k m c) (fun τ => G (m, c, τ)) τ σ

/-- The counts of two stretches behind each other. -/
theorem Fits.app : ∀ {s s' t t' : Shape} {F : CarryS s s'} {G : Tr s → CarryS t t'} {ε : Err s'}
    {ε' : Err s} {δ : Err t'} {δ' : Err t}, F.Fits ε ε' → (∀ τ, (G τ).Fits δ δ') →
    (F.app G).Fits (Err.app ε δ) (Err.app ε' δ')
  | _, _, _, _, .nil, _, _, _, _, _, _, hG => hG ()
  | _, _, _, _, .step _ _ k, _, (_, _), (_, _), _, _, hF, hG =>
      ⟨hF.1, fun m c => Fits.app (F := k m c) (hF.2 m c) fun τ => hG (m, c, τ)⟩
  | _, _, _, _, .skip k, _, _, (_, _), _, _, hF, hG =>
      fun m c => Fits.app (F := k m c) (hF m c) fun τ => hG (m, c, τ)

/-- All rounds are skipped. -/
def skips : (s : Shape) → CarryS s []
  | [] => .nil
  | _ :: s => .skip fun _ _ => skips s

theorem tr_skips : ∀ (s : Shape) (τ : Tr s), (skips s).tr τ = some ()
  | [], _ => rfl
  | _ :: s, (_, _, τ) => tr_skips s τ

theorem fits_skips : ∀ (s : Shape) (ε' : Err s), (skips s).Fits () ε'
  | [], _ => trivial
  | _ :: s, (_, ε') => fun _ _ => fits_skips s ε'

/-- Each round is read as itself. -/
def same : (s : Shape) → CarryS s s
  | [] => .nil
  | _ :: s => .step id (fun _ c => some c) fun _ _ => same s

theorem tr_same : ∀ (s : Shape) (τ : Tr s), (same s).tr τ = some τ
  | [], () => rfl
  | _ :: s, (m, c, τ) => by
      show ((same s).tr τ).map (fun τ' => (m, c, τ')) = some (m, c, τ)
      rw [tr_same s τ]
      rfl

theorem fits_same : ∀ (s : Shape) (ε : Err s), (same s).Fits ε ε
  | [], _ => trivial
  | _ :: s, (e, ε) =>
      ⟨⟨1, fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
        le_of_eq (Nat.mul_one e)⟩, fun _ _ => fits_same s ε⟩

/-- One round. -/
def one {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Msg → r.Chal → Option r'.Chal) :
    CarryS [r] [r'] :=
  .step fm fc fun _ _ => .nil

theorem tr_one {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Msg → r.Chal → Option r'.Chal)
    (m : r.Msg) (c : r.Chal) :
    (one fm fc).tr (m, c, ()) = (fc m c).map fun c' => (fm m, c', ()) := by
  show (fc m c).bind (fun c' => (some ()).map fun τ' => (fm m, c', τ')) = _
  cases fc m c <;> rfl

theorem fits_one {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Msg → r.Chal → Option r'.Chal)
    (w e e' : ℕ) (hw : ∀ (m : r.Msg) (c' : r'.Chal), cnt (fun c => fc m c = some c') ≤ w)
    (he : e * w ≤ e') : (one fm fc).Fits (s' := [r']) (e, ()) (e', ()) :=
  ⟨⟨w, hw, he⟩, fun _ _ => trivial⟩

end CarryS

end OnBytes.Flat

#print axioms OnBytes.Flat.CarryS.tr_app
#print axioms OnBytes.Flat.CarryS.Fits.app
#print axioms OnBytes.Flat.CarryS.fits_same
#print axioms OnBytes.Flat.CarryS.fits_one
