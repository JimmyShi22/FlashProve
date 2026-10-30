-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which a ledger is open and the item in
the premise holds. (At s' := s the laws say "H gives H".)
Johnson/Desc/First/Look/K3WorthStep.lean: the kind "lookup" (K3): THE ITEMS worth "planes" AND worth
"keys" (K3WorthPlanes, K3WorthKeys: Johnson/Top/H/K3Worth.lean) GO BACK OVER ANY STEP OF THE
VERIFIER's STATE THAT LEAVES WHAT WAS HEARD AND LEADS TO A LATER LEDGER: from the state behind the
step to the state in front: free of any kind of sub-protocol. Statements and proofs. Ties: no error
term. NO SOUNDNESS IS CLAIMED.

Why. These items stay open behind a lookup across other kinds' sub-protocols. A tie that goes
backward has the item behind a step and owes it in front. Each item reads the ledger through the
library's HeardIs alone, and asks its sentence at all rounds for which what was heard stands AT THE
LEDGER NAMED. HeardIs passes to later ledgers (heardIsLater, Johnson/Top/H/K3LeftLater.lean): so at
a later ledger the item is asked of more rounds and says more.

OBJECT: K3OutRows | K3OutPlanes | K3OutKeys (Johnson/Top/H/K3RowOut.lean); K3Objects | K3WorthPlanes
  | K3WorthKeys; Meaning.worth at the digits' piece under K3At (Johnson/Desc/First/Look/K3At.lean).
Used by WorthAtMerge.lean (Johnson/Top/H0/MergeLaw/).
LETTERS: fork, heard, h, lm, first, nu, Kv, s (in front), s' (behind), w, F, G free; at the item: X,
  D, L, Mg, claim, m, x, tl, z, z', y, y'.
Compiled with the whole library.

Main names:
  k3OutRows_back, k3OutPlanes_back, k3OutKeys_back: the three parts of k3OutBack (K3LeftLater.lean),
    one by one.
  k3Objects_step, k3WorthPlanes_step, k3WorthKeys_step: THE STEP's FORM.
  worth_planes_step, worth_keys_step: at the item, under K3At: the first component and the strings
    may differ at the two states.

THE PREMISES, AND WHO PAYS. hh: what was heard at the seat is one at both states · hF, hG: both hold
a ledger · hL: the ledger behind is later (Fo.Later: next does not fall; the number of slots stays;
what lies under a filled slot stays): ALL FOUR ARE THE STEP's AUTHORS'. No sizes are asked.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Worth
import Johnson.Top.H.K3LeftLater
import Johnson.Desc.First.Look.K3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)

/-! ## The parts of the row out, one by one -/

section
variable {K : Type} [CommRing K] {ρ : OnBytes.Model.Reading K} {h : FoNums.Sh} {lm first : ℕ}
  {ν : _root_.Fo.Pl → K} {Kv : ℕ → ℕ → K} {g : Forest.Heard} {F G : Fork}

theorem k3OutRows_back (hL : _root_.Fo.Later F G) (H : K3OutRows h lm first ν ρ g G) :
    K3OutRows h lm first ν ρ g F := fun rs hI => H rs (heardIsLater K ρ g F G _ hL hI)

theorem k3OutPlanes_back (hL : _root_.Fo.Later F G) (H : K3OutPlanes h lm first ν ρ g G) :
    K3OutPlanes h lm first ν ρ g F := fun rs hI => H rs (heardIsLater K ρ g F G _ hL hI)

theorem k3OutKeys_back (hL : _root_.Fo.Later F G) (H : K3OutKeys h lm first ν Kv ρ g G) :
    K3OutKeys h lm first ν Kv ρ g F := fun rs hI => H rs (heardIsLater K ρ g F G _ hL hI)

end

/-! ## The step's form -/

section
variable {S W : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
  (h : FoNums.Sh) (lm first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) (Kv : W → ℕ → ℕ → Cb.Gl.E)
  {s s' : S} {w : W} {F G : Fork}

theorem k3Objects_step (hh : heard s' = heard s) (hF : fork s = some F) (hG : fork s' = some G)
    (hL : _root_.Fo.Later F G) (H : K3Objects fork heard h lm first nu s' w) :
    K3Objects fork heard h lm first nu s w := by
  intro g F₁ a b
  obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans a)
  exact k3OutRows_back hL (H g G hG (hh.trans b))

/-- **worth "planes" goes back over a step.** -/
theorem k3WorthPlanes_step (hh : heard s' = heard s) (hF : fork s = some F)
    (hG : fork s' = some G) (hL : _root_.Fo.Later F G)
    (H : K3WorthPlanes fork heard h lm first nu s' w) :
    K3WorthPlanes fork heard h lm first nu s w := by
  intro g F₁ a b
  obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans a)
  exact k3OutPlanes_back hL (H g G hG (hh.trans b))

/-- **worth "keys" goes back over a step.** -/
theorem k3WorthKeys_step (hh : heard s' = heard s) (hF : fork s = some F)
    (hG : fork s' = some G) (hL : _root_.Fo.Later F G)
    (H : K3WorthKeys fork heard h lm first nu Kv s' w) :
    K3WorthKeys fork heard h lm first nu Kv s w := by
  intro g F₁ a b
  obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans a)
  exact k3OutKeys_back hL (H g G hG (hh.trans b))

end

/-! ## At the item -/

section
variable {P Cells Tok : Type} {X : Verify.Public} {D : Desc.First.Look.Sent}
  {L : K3Letters Cells Tok} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} (hK : K3At X D L Mg)
include hK

/-- **The item worth m ‹the digits' piece› "planes" goes back over a step.** -/
theorem worth_planes_step {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X m = some (x, tl)) (z z' : P) (s s' : Desc.First.S)
    (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) {F G : Fork}
    (hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s)
    (hF : (Desc.K3.seatDigits claim).fork s = some F)
    (hG : (Desc.K3.seatDigits claim).fork s' = some G) (hL : _root_.Fo.Later F G)
    (H : Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z', s') y' w) :
    Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w :=
  fPl_back hK claim m hx z s y w fun g F₁ a b => by
    obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans a)
    exact k3OutPlanes_back hL (fPl_at hK claim m hx z' s' y' w H g G hG (hh.trans b))

/-- **And "keys".** -/
theorem worth_keys_step {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X m = some (x, tl)) (z z' : P) (s s' : Desc.First.S)
    (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) {F G : Fork}
    (hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s)
    (hF : (Desc.K3.seatDigits claim).fork s = some F)
    (hG : (Desc.K3.seatDigits claim).fork s' = some G) (hL : _root_.Fo.Later F G)
    (H : Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z', s') y' w) :
    Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w :=
  fKe_back hK claim m hx z s y w fun g F₁ a b => by
    obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans a)
    exact k3OutKeys_back hL (fKe_at hK claim m hx z' s' y' w H g G hG (hh.trans b))

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3OutPlanes_back
#print axioms VerifiableInference.OnPublicFiles.k3OutKeys_back
#print axioms VerifiableInference.OnPublicFiles.k3Objects_step
#print axioms VerifiableInference.OnPublicFiles.k3WorthPlanes_step
#print axioms VerifiableInference.OnPublicFiles.k3WorthKeys_step
#print axioms VerifiableInference.OnPublicFiles.worth_planes_step
#print axioms VerifiableInference.OnPublicFiles.worth_keys_step
