-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due8.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, EIGHTH COUNT: `k03_cond_due8` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due7`
(Johnson/P5J/K03Due7.lean, which does not turn). FROM the head, the filling 𝔏, its three equations
q₁ q₂ q₃ and FIVE BINDERS, ALL WHERE THE DIGITS' PIECE ACCEPTS:
  OF THE FORMS BEHIND THE ACCEPT (`DigItemR`: a public test at the state behind):
    Io: at formsIn l (3 + shift sub) "own" (25) · Ij: at formsIn l (joinAt sub) "join" (13);
  OF rides AT THE OUTPUT HEAD's DIGITS ALONE (1 place of 25), another file's three premises there:
    Ob: what the ledger behind still owes, the ledger in front owed;
    Jh: the run "join" goes forward (`DigFwdR` at [(3, "join")]);
    Oh: "norm", "policy", "logits" go forward (`DigFwdR`).
s₀ and z₀ are idle letters of the condition's own text.

PAID HERE BEYOND `k03_cond_due7`: "planes" at the head's link (Johnson/P5J/K03DigPlanesAt.lean,
over `hPlanesIt_dig_free`) · "front", "back" go
forward at the 12 layers' segments (Johnson/P5J/K03OwnFwdLayAt.lean, over `hOwn_of_below` and
`wins_reached`) · "first", "keys", "second" at attention's 12 (Johnson/P5J/K03OwnFwdAttAt.lean) ·
rides at the head's digits down to the three above (Johnson/P5J/K03RidesDigHeadHole.lean, over
`ridesAtR_digits_head_hole`, which does not ask that the run "planes" itself
answers in front: the premise that the seventh count would not spend).

SO rides IS A THEOREM AT 49 OF ITS 50 PLACES, AND "planes" AT ALL 13.

Limits: the five are premises, shown nowhere at the constant; we know no reason to doubt them.
(Where this and lean/THEOREM.md differ, the page
holds.)
No
member is known. "From the head" moves tests into the head; whether there is a head is not said
here. At secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due7
import Johnson.P5J.K03OwnFwdLayAt
import Johnson.P5J.K03OwnFwdAttAt
import Johnson.P5J.K03RidesDigHeadHole

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

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, EIGHTH COUNT.** -/
theorem k03_cond_due8 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
    (Ob : ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F G, K3Pass u.1 v.1 F G → ∀ i, VerifiableInference.Desc.K3.unpaid G i = true →
        VerifiableInference.Desc.K3.unpaid F i = true)
    (Jh : ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      DigFwdR h 24 b' [(3, "join")])
    (Oh : ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      DigFwdR h 24 b' [(3, "norm"), (3, "policy"), (3, "logits")]) :
    h.K3Cond 𝔏 := by
  refine k03_cond_due7 h 𝔏 q₁ q₂ q₃ s₀ z₀ Io Ij ?_ (k03_fwd_lay h 𝔏 q₁ q₂ q₃)
    (k03_fwd_att h 𝔏 q₁ q₂ q₃) ?_
  · intro q hq b' hb
    obtain ⟨y, tl, hy⟩ := k03_digAt_some h (l := 24) (by omega)
    exact k03_planesIt_head h 𝔏 q₁ q₂ q₃ (by omega) (by decide) hy q hq b' hb
  · intro q hq b' hb
    exact k03_rides_dig_head_hole h 𝔏 q₁ q₂ q₃ q hq b' hb (Ob b' hb)
      (fun z u v a b c d e => Jh b' hb z u v a b c d e (3, "join") (by simp)) (Oh b' hb)

end P5J

#print axioms P5J.k03_cond_due8
#print axioms P5J.k03_kind_all
