-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due9.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, NINTH COUNT: `k03_cond_due9` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due8`
(Johnson/P5J/K03Due8.lean, which does not turn). FROM the head, the filling 𝔏, its three equations
q₁ q₂ q₃ and FIVE BINDERS, ALL WHERE THE DIGITS' PIECE ACCEPTS:
  OF THE FORMS BEHIND THE ACCEPT (`DigItemR`: a public test at the state behind):
    IoH: at formsIn 24 (3 + shift .head) "own" (1: the output head's link);
    Ij: at formsIn l (joinAt sub) "join" (13: attention's 12 and the head's);
  OF rides AT THE OUTPUT HEAD's DIGITS ALONE, another file's three premises there:
    Ob: what the ledger behind still owes, the ledger in front owed;
    Jh: the run "join" goes forward · Oh: "norm", "policy", "logits" go forward (`DigFwdR`).
Ob, Jh and Oh bind the stated sub-protocol b' and no piece q: wider than what is spent by that guard
alone. s₀ and z₀ are idle letters of the condition's own text.

PAID HERE BEYOND `k03_cond_due8`: "own" at the 12 layers' segments
(Johnson/P5J/K03OwnItLayPaid.lean, over K03OwnItLayAt.lean and K03OwnFwdLayFront.lean, and three
other groups' laws) and at attention's 12 (Johnson/P5J/K03OwnItAttAt.lean). Each takes "the calling
kind's runs go forward" OFF THE PROMISE IN FRONT ALONE: the forms behind the accept are a part of
what shows the promise behind, so that promise may not be among their hands.

SO FOUR OF THE FIVE STAND AT THE OUTPUT HEAD's LINK ALONE; IN FRONT OF IT ONE ITEM IS LEFT: "join"
AT ATTENTION's 12.

Limits: the five are premises, shown nowhere at the constant; we know no reason to doubt them.
(Where this and lean/THEOREM.md differ, the page
holds.)
No
member is known. "From the head" moves tests into the head; whether there is a head is not said
here. At secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due8
import Johnson.P5J.K03OwnItLayPaid
import Johnson.P5J.K03OwnItAttAt

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

/-- On the written list a layers' segment has an even number below 24. -/
theorem k03_sorts_lay : ∀ l < 25, linksFull[l]? = some ModelPart.layers → l % 2 = 0 ∧ l < 24 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, NINTH COUNT.** -/
theorem k03_cond_due9 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (IoH : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch 24 q b'
          (.formsIn 24 (3 + shift ModelPart.head) "own"))
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
  refine k03_cond_due8 h 𝔏 q₁ q₂ q₃ s₀ z₀ ?_ Ij Ob Jh Oh
  intro l hl sub hsub q hq b' hb
  cases sub with
  | layers =>
    obtain ⟨he, h24⟩ := k03_sorts_lay l hl hsub
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    exact k03_ownIt_lay_paid h 𝔏 q₁ q₂ q₃ (by omega) q hq b' hb
  | attention =>
    obtain ⟨he, h24⟩ := (k03_sorts_full l hl).1 hsub
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    exact k03_ownIt_att h 𝔏 q₁ q₂ q₃ g (by omega) q hq b' hb
  | head =>
    obtain rfl : l = 24 := (k03_sorts_full l hl).2 hsub
    exact IoH q hq b' hb

end P5J

#print axioms P5J.k03_sorts_lay
#print axioms P5J.k03_cond_due9
#print axioms P5J.k03_kind_all
