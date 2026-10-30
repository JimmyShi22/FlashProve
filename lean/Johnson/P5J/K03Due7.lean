-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due7.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, SEVENTH COUNT: `k03_cond_due7` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due6`
(Johnson/P5J/K03Due6.lean, which does not turn). FROM the head, the filling 𝔏, its three equations
q₁ q₂ q₃ and SIX BINDERS, ALL WHERE THE DIGITS' PIECE ACCEPTS:
  OF THE FORMS BEHIND THE ACCEPT (`DigItemR`: a public test at the state behind):
    Io: at formsIn l (3 + shift sub) "own" (25) · Ij: at formsIn l (joinAt sub) "join" (13) ·
    IpH: at formsIn 24 (2 + shift .head) "planes" (1: the output head's link);
  OF rides (`DigFwdR`: the calling kind's own runs go forward across the accept):
    Fl: "front", "back" at the 12 layers' segments;
    Fa: "first", "keys", "second" at attention's 12;
    RdH: rides itself at the output head's digits (1).
s₀ and z₀ are idle letters of the condition's own text.

PAID HERE BEYOND `k03_cond_due6`: "planes" at attention's 12 (Johnson/P5J/K03DigPlanesAt.lean, over
`hPlanesIt_dig_free`) · rides at the 24 digits' places in front of the head's, from
Fl
and Fa (Johnson/P5J/K03RidesDigLeft.lean, over `ridesAtR_digits_layers` and
`ridesAtR_digits_att`).

WHY THE HEAD's TWO ARE LEFT WHOLE. As this count was typed, both files split them further only
under a premise "the run planes itself answers at the state in front" (`k03_rides_dig_head_three`
bears it still; Johnson/P5J/K03DigPlanesAt.lean bears it no more). By two readings of ours that
premise may be false at a state under the promise (there the link's second hole may answer in the
run's stead): a count that rested on it might be empty at the head's link. So it is not spent here;
the eighth count (Johnson/P5J/K03Due8.lean) goes round it.

Limits: the six are premises; no member is known; RdH is a share of a conjunct of the kind's own
conclusion. "From the head" moves tests into the head; whether there is a head is not said here. At
secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due6
import Johnson.P5J.K03DigPlanesAt
import Johnson.P5J.K03RidesDigLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift joinAt)
open VerifiableInference.Reads.Pass (Fwd)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **The runs ps of segment l go forward across an accept of the lookup on the digits**: the
premise hOwn (Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean, K3RidesDigFwd2.lean) at the closed
constant, general in the list of runs. -/
abbrev DigFwdR (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S
      VerifiableInference.Desc.Claim) (ps : List (ℕ × String)) : Prop :=
  ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
    onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l true) u →
    h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
    onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l true + 1) v →
    StepRel b' u.1 v.1 →
    ∀ p ∈ ps, Fwd ((h.toAtMg.𝔇 h.𝔇).Rd l) p.1 p.2 u.1 v.1

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, SEVENTH COUNT.** -/
theorem k03_cond_due7 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (Io : ∀ l < 25, ∀ sub, linksFull[l]? = some sub →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
          (.formsIn l (3 + shift sub) "own"))
    (Ij : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → sub ≠ .layers →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
          (.formsIn l (joinAt sub) "join"))
    (IpH : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch 24 q b'
          (.formsIn 24 (2 + shift ModelPart.head) "planes"))
    (Fl : ∀ g < 12, ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
      DigFwdR h (2 * g) b' [(2, "front"), (2, "back")])
    (Fa : ∀ g < 12,
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
      DigFwdR h (2 * g + 1) b' [(2, "first"), (2, "keys"), (2, "second")])
    (RdH : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
        RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
          (k3K 24 true) q b') :
    h.K3Cond 𝔏 := by
  refine k03_cond_due6 h 𝔏 q₁ q₂ q₃ s₀ z₀ Io ?_ Ij ?_
  · intro l hl sub hsub hs q hq b' hb
    cases sub with
    | layers => exact absurd rfl hs
    | attention =>
      obtain ⟨y, tl, hy⟩ := k03_digAt_some h hl
      exact k03_planesIt_att h 𝔏 q₁ q₂ q₃ hl hsub hy q hq b' hb
    | head =>
      obtain rfl : l = 24 := (k03_sorts_full l hl).2 hsub
      exact IpH q hq b' hb
  · intro l hl q hq b' hb
    by_cases h24 : l = 24
    · subst h24
      exact RdH q hq b' hb
    · rcases Nat.mod_two_eq_zero_or_one l with he | he
      · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
        exact k03_rides_dig_lay_own h 𝔏 q₁ q₂ q₃ g (by omega) q hq b' hb (Fl g (by omega) b' hb)
      · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
        exact k03_rides_dig_att_own h 𝔏 q₁ q₂ q₃ g (by omega) q hq b' hb (Fa g (by omega) b' hb)

end P5J

#print axioms P5J.k03_cond_due7
-- The bridge that spends the condition, asked here by name.
#print axioms P5J.k03_kind_all
