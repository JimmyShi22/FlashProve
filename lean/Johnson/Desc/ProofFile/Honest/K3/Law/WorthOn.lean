-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/WorthOn.lean: the kind "lookup" (K3): the items worth "planes"
and worth "keys" (`K3WorthPlanes`, `K3WorthKeys`: Johnson/Top/H/K3Worth.lean) go on over any step of
the verifier's state that leaves what was heard and leads to a later ledger, where the four families
of forms in what was heard are filled at the ledger in front: from the state in front of the step to
the state behind. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md; the heads of Johnson/Desc/First/Look/K3WorthStep.lean and of
Honest/K3/Law/Earlier.lean.

What is shown. The mirrors of four theorems of the library's K3WorthStep.lean, which go back over
such a step.
  `k3WorthPlanes_on`, `k3WorthKeys_on`: the step's form: free of any kind of sub-protocol.
  `worth_planes_on`, `worth_keys_on`: at the item, under `K3At` (Johnson/Desc/First/Look/K3At.lean):
    the first component and the strings may differ at the two states.

Follows. Each statement is that of the library's `k3WorthPlanes_step`, `k3WorthKeys_step`,
`worth_planes_step`, `worth_keys_step`, with the hypothesis `N` behind `hL`, and with `H` and the
conclusion in each other's place. Each proof is that theorem's, line for line, mirrored: with
`k3OutPlanes_later` and `k3OutKeys_later` (Earlier.lean) in the place of `k3OutPlanes_back` and
`k3OutKeys_back`; in the two theorems at the item the last line of the library's proof is two lines
here. K3WorthStep.lean is imported. That these mirrors were wanted, and their form, comes from
the files under Honest/Thread/.

Hypotheses that remain. `hh`: what was heard at the seat is one at both states. `hF`, `hG`: both
hold a ledger. `hL`: the ledger behind is later (`Fo.Later`). `N`: whatever was heard in front, its
four families of forms are named at the ledger in front (`Fo.Tp.PadNames`,
Johnson/Top/H/Keep/PadNamed.lean). `H`: the item holds at the state in front. In the last two: `hK`:
the table's filling says at the lookups' own pieces what the lookups' layer says (`K3At`); `hx`: the
public data hold the digits' place of link m (`digAt`).

Limits. `N` is shown, under the hypotheses that their heads list (the second: under `P5J.AtMgA`
alone), in Honest/K3/Law/NamedDigits.lean behind the seated lookup on the digits, and in
Honest/K3/Law/NamedAt346.lean at a state reached at border 346. `hh`, `hF`, `hG` and `hL` are for
the files on the step in question to show. No state of the verifier is shown at which a ledger is
open and the item in the hypothesis `H` holds.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3WorthStep
import Johnson.Desc.ProofFile.Honest.K3.Law.Earlier

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K3.Law
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)
open VerifiableInference VerifiableInference.OnPublicFiles

/-! ## The step's form -/

section
variable {S W : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
  (h : FoNums.Sh) (lm first : ℕ) (nu : W → _root_.Fo.Pl → Cb.Gl.E) (Kv : W → ℕ → ℕ → Cb.Gl.E)
  {s s' : S} {w : W} {F G : Fork}

/-- **worth "planes" goes on over a step.** Conditional on the hypotheses that the head of this file
lists, `N` among them. -/
theorem k3WorthPlanes_on (hh : heard s' = heard s) (hF : fork s = some F)
    (hG : fork s' = some G) (hL : _root_.Fo.Later F G)
    (N : ∀ g, heard s = some g → _root_.Fo.Tp.PadNames g F)
    (H : K3WorthPlanes fork heard h lm first nu s w) :
    K3WorthPlanes fork heard h lm first nu s' w := by
  intro g G₁ a b
  obtain rfl : G = G₁ := Option.some.inj (hG.symm.trans a)
  exact k3OutPlanes_later _ hL (N g (hh.symm.trans b)) (H g F hF (hh.symm.trans b))

/-- **worth "keys" goes on over a step.** Conditional on the hypotheses that the head of this file
lists, `N` among them. -/
theorem k3WorthKeys_on (hh : heard s' = heard s) (hF : fork s = some F)
    (hG : fork s' = some G) (hL : _root_.Fo.Later F G)
    (N : ∀ g, heard s = some g → _root_.Fo.Tp.PadNames g F)
    (H : K3WorthKeys fork heard h lm first nu Kv s w) :
    K3WorthKeys fork heard h lm first nu Kv s' w := by
  intro g G₁ a b
  obtain rfl : G = G₁ := Option.some.inj (hG.symm.trans a)
  exact k3OutKeys_later _ hL (N g (hh.symm.trans b)) (H g F hF (hh.symm.trans b))

end

/-! ## At the item -/

section
variable {P Cells Tok : Type} {X : Verify.Public} {D : Desc.First.Look.Sent}
  {L : K3Letters Cells Tok} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} (hK : K3At X D L Mg)
include hK

/-- **The item worth m ‹the digits' piece› "planes" goes on over a step.** Conditional on the
hypotheses that the head of this file lists, `N` among them. -/
theorem worth_planes_on {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X m = some (x, tl)) (z z' : P) (s s' : Desc.First.S)
    (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) {F G : Fork}
    (hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s)
    (hF : (Desc.K3.seatDigits claim).fork s = some F)
    (hG : (Desc.K3.seatDigits claim).fork s' = some G) (hL : _root_.Fo.Later F G)
    (N : ∀ g, (Desc.K3.seatDigits claim).heard s = some g → _root_.Fo.Tp.PadNames g F)
    (H : Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z, s) y w) :
    Mg.worth m (Desc.K3.pieceAt X m true) "planes" (z', s') y' w :=
  fPl_back hK claim m hx z' s' y' w fun g G₁ a b => by
    obtain rfl : G = G₁ := Option.some.inj (hG.symm.trans a)
    exact k3OutPlanes_later _ hL (N g (hh.symm.trans b))
      (fPl_at hK claim m hx z s y w H g F hF (hh.symm.trans b))

/-- **And "keys".** Conditional on the same hypotheses. -/
theorem worth_keys_on {Cl : Type} (claim : Aff → Cl) (m : ℕ) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X m = some (x, tl)) (z z' : P) (s s' : Desc.First.S)
    (y y' : Strs) (w : Desc.Wit Cells Tok MsgT) {F G : Fork}
    (hh : (Desc.K3.seatDigits claim).heard s' = (Desc.K3.seatDigits claim).heard s)
    (hF : (Desc.K3.seatDigits claim).fork s = some F)
    (hG : (Desc.K3.seatDigits claim).fork s' = some G) (hL : _root_.Fo.Later F G)
    (N : ∀ g, (Desc.K3.seatDigits claim).heard s = some g → _root_.Fo.Tp.PadNames g F)
    (H : Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z, s) y w) :
    Mg.worth m (Desc.K3.pieceAt X m true) "keys" (z', s') y' w :=
  fKe_back hK claim m hx z' s' y' w fun g G₁ a b => by
    obtain rfl : G = G₁ := Option.some.inj (hG.symm.trans a)
    exact k3OutKeys_later _ hL (N g (hh.symm.trans b))
      (fKe_at hK claim m hx z s y w H g F hF (hh.symm.trans b))

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.k3WorthPlanes_on
#print axioms ProofFile.Honest.K3.Law.k3WorthKeys_on
#print axioms ProofFile.Honest.K3.Law.worth_planes_on
#print axioms ProofFile.Honest.K3.Law.worth_keys_on
