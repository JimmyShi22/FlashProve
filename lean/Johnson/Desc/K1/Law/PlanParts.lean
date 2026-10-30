-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/PlanParts.lean: K01_law: PlanAt (Johnson/Desc/K1/Law/NewAtSending.lean: the plan's side of a sending: ten fields) OUT OF ITS PARTS: three fields are theorems of Johnson/Desc/K1/Law/PlanAtData.lean: tree (tree_at_data: at the written data's own round) · part (part_of_own: by the
make of the layout) · listed (listed_at_cut: under ChainFit, at the maker's cut's piece); told stays a premise on the data's two rounds; the other six read neither d₁ nor d₂: PlanRest.
  PlanRest · own_of_ownL · planAt_of_parts
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.NewAtSending
import Johnson.Desc.K1.Law.PlanAtData
import Johnson.Desc.K1.Law.CallsO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker OnBytes.Flat Cb Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (Mem)
open OnBytes.Params (Rounds)

/-- **What of PlanAt reads neither of the two rounds' data, and is no theorem yet.** Each field to PlanAt's letter. -/
structure PlanRest {Xi : Type} (cs : Codes) (G : FileDescription Xi) (ms : List Mem) (P : Par) (rad : ℕ → ℕ)
    (base : ℕ) (seats : List (ℕ × ℕ)) : Prop where
  mems : MemsAt cs ms P rad base
  seats : ∀ u ∈ seats, ∃ j : Fin (shapesOf P).length, sampledAt P j ∧ u = seatOfMsg P base j.val
  one : ∀ j : Fin (shapesOf P).length, sampledAt P j → (shapeAt P j).answers = 1
  pad : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    (OnBytes.Send.pad P.codes (shapeAt P j)).isSome = true
  row : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    0 < (shapeAt P j).mainRows ∨ 0 < (shapeAt P j).maskRows
  fits : ∀ x ∈ ms, SeatFits G cs x.1.l x.1.seat

/-- K1's own sub-protocol's test on the plan holds the kind's own. -/
theorem own_of_ownL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (arrs : Option (List ℕ))
    (h : (ownL Z G l d arrs).planOk = true) : planOkOwn (parL Z G l d) = true := by
  cases d with
  | true =>
    have h' : (planOkOwn (parL Z G l true) && arrs.isSome) = true := h
    exact (Bool.and_eq_true _ _ ▸ h').1
  | false =>
    have h' : (planOkOwn (parL Z G l false) && arrs.isSome) = true := h
    exact (Bool.and_eq_true _ _ ▸ h').1

theorem planAt_of_parts {Xi : Type} {F : Frame} {cs : Codes} {G : FileDescription Xi} {ms : List Mem}
    {P : Par} {rad : ℕ → ℕ} {base : ℕ} {seats : List (ℕ × ℕ)}
    (h : PlanRest cs G ms P rad base seats) (hB : planOkOwn P = true) (a : ℕ) (R₁ R₂ R₃ : Rounds)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) (n : ℕ) (d₁ d₂ : RDT)
    (hd : ((dataOf a R₁ R₂ R₃).ds₁.drop n).take 2 = [d₁, d₂]) (he : d₁.entry = seedEntry P)
    (hlist : ListedAt F base [d₁, d₂])
    (htold : ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (base + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) : PlanAt F cs G ms P rad base d₁ d₂ seats :=
  { mems := h.mems, seats := h.seats, one := h.one, pad := h.pad, row := h.row
    part := part_of_own hB
    tree := tree_at_data a R₁ R₂ R₃ hRoots n d₁ d₂ hd P he hB
    fits := h.fits, listed := hlist, told := htold }

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.own_of_ownL
#print axioms VerifiableInference.Desc.K1.planAt_of_parts
