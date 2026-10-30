-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortFour.lean: THE FIELD h4 OF THE ONE REST OF A SORT's OWN FIELDS
(`SortRest`, SortRest.lean: "the smallness test's first four claims' weighted sum is the four
values' terms"), PAID AT EVERY PROMISE THAT GIVES THE CORE; AND SO THE REST COMES DOWN TO THE
LOOKUP ARGUMENT's SEVEN. A structure of sentences, and theorems: calls.

By: k8_four (Johnson/Desc/First/Batch/Law/K8Four.lean), whose end is the field at π := pi8, ent :=
ent4 pi8 (tmFour, LinkRestAtSort2.lean, is by definition "the four values, numbered"). Its
premises: hπ: by definition at phiAll · hkeep: phi_k8_keep, from hψ · hOk4: the core's clause four
· hFu4: hFu4_full (FullFour.lean), under okCoef (the core's clause static, its field
coef) and okEnts (the core's clause ents4).

What is said.
  `h4_of_core`: **the field h4, in its own text**, at φ := phiAll u ψ, Fu := FullAt nU and ANY
    promise Ok with hc : Ok q gives OkCore nU tlD q; from hψ : Rests u ψ.
  `LookRest L u ψ Ok nU ents t3 l3`: SortRest less h4: the seven fields on the lookup's runs (k3,
    k3d, k3g, k3f, k3p, k3s, k3sL), in the same texts.
  `sortRest_of_look`: **SortRest from LookRest**, hψ and hc.
  `hc_layers`, `hc_att`, `hc_head`: hc at the three sorts' promises fun q => (‹the named Ok› q ∧ Kx
    q) ∧ C q.

Limits. A PAYMENT OF ONE FIELD UNDER THE PROMISE: it says what follows from Ok; that Ok holds at
what is fixed in front of the batching is the field Aready's. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortRest
import Johnson.Desc.First.Link.Law.FullFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (Where atS segAt?)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf formsOf shift openSets
  rowsDue FoldFacts FoldData)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)
open Johnson.Desc.First.Walk.Tied (Reach MeantAt)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)

open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {β : Type}

/-- **h4 FROM THE CORE.** -/
theorem h4_of_core (u : HTailF2) {ψ : S → β} (hψ : Rests u ψ) {Ok : Q β → Prop} {nU : Array ℕ}
    {tlD : HTailF2} (hc : ∀ q, Ok q → OkCore nU tlD q) :
    ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a → k8Run.2 front e
      = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt
      nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
      termsAt GE8 (tmFour (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta) :=
  k8_four (phiAll u ψ) Ok (FullAt nU) u pi8 (fun _ => rfl)
    (fun s tl tl' F1 h hb => phi_k8_keep u ψ hψ s tl tl' F1 h hb) (ent4 pi8)
    (fun q v tlb g hq hv ht hg => (hc q hq).four v tlb g hv ht hg)
    (hFu4_full pi8 (phiAll u ψ) Ok nU u (fun _ => rfl)
      (fun q tlb v hq ht hv => ((hc q hq).static tlb v ht hv).coef)
      (fun q tlb g hq ht hg => (hc q hq).ents4 tlb g ht hg))

/-- **THE LOOKUP ARGUMENT's SEVEN.** -/
structure LookRest (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (ents : List (ℕ × String)) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) : Prop where
  k3 : ∀ o ∈ ents, ∀ run, At L o run → RunOk Reading.gl atS (O9 (phiAll u ψ) Ok (FullAt nU)) (Fx9
    (phiAll u ψ) Ok) run (t3 o) (l3 o)
  k3d : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁
  k3f : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → numOf u e₁ = numOf u e
  k3p : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G
  k3s : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork Sized e →
    HasFork Sized e₁
  k3sL : ∀ o ∈ ents, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork (fun F => Sized
    F ∧ F.LS.size = F.ns) e → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁

/-- **SortRest FROM THE SEVEN.** -/
theorem sortRest_of_look {L : Link S Claim} {u : HTailF2} {ψ : S → β} (hψ : Rests u ψ)
    {Ok : Q β → Prop} {nU : Array ℕ} {tlD : HTailF2} (hc : ∀ q, Ok q → OkCore nU tlD q)
    {ents : List (ℕ × String)} {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {l3 : ℕ × String → Q β → ℕ} (R : LookRest L u ψ Ok nU ents t3 l3) :
    SortRest L u ψ Ok nU ents t3 l3 where
  h4 := h4_of_core u hψ hc
  k3 := R.k3
  k3d := R.k3d
  k3g := R.k3g
  k3f := R.k3f
  k3p := R.k3p
  k3s := R.k3s
  k3sL := R.k3sL

/-- hc at a layers' link's promise. -/
theorem hc_layers {p4 : OnBytes.Desc.First.K4.Par} {nU : Array ℕ} {tlD : HTailF2}
    {Kx C : Q β → Prop} :
    ∀ q, (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ C q) q → OkCore nU tlD q :=
  fun _ h => h.1.1.core

/-- hc at an attention link's promise. -/
theorem hc_att {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {tlD : HTailF2} {Kx C : Q β → Prop} :
    ∀ q, (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ C q) q → OkCore nU tlD q :=
  fun _ h => h.1.1.core

/-- hc at the head's link's promise. -/
theorem hc_head {hS : OnBytes.Model.Head.Shape} {iU3 : ℕ} {p6 : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ} {tlD : HTailF2}
    {Kx C : Q β → Prop} :
    ∀ q, (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧ C q) q →
      OkCore nU tlD q :=
  fun _ h => h.1.1.core

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.h4_of_core
#print axioms VerifiableInference.Desc.LinkJoin.sortRest_of_look
#print axioms VerifiableInference.Desc.LinkJoin.hc_layers
#print axioms VerifiableInference.Desc.LinkJoin.hc_att
#print axioms VerifiableInference.Desc.LinkJoin.hc_head
