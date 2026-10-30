-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortRestC.lean: ON THE SECOND ROAD: THE SORTS' OWN FIELDS
(`LayersOwesC`, `AttOwesC`, `HeadOwesC`, LinkRestAtSort4C.lean) FROM THE FIELDS THAT HAVE PAYERS AT
THE CONSTANT, THE ONE NAMED REST `SortRest` (SortRest.lean: general in the promise: IT IS REUSED AS
IT IS, AT THE BARE PROMISE) AND THE NEW FIELD k3k. Theorems: assemblies, cut by program out of
SortRest.lean's three.

What is said. `layersOwesC_of_rest`, `attOwesC_of_rest`, `headOwesC_of_rest`: from seg, ties, hψ
(hrd; hkap), drawB, rows, k3k and SortRest L u ψ (fun q => ‹the named Ok› q ∧ Kx q) nU ‹the sort's
entries› t3 l3.

Limits. BOOK-KEEPING. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort4C
import Johnson.Desc.First.Link.Law.SortRest

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

/-- **`LayersOwesC` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem layersOwesC_of_rest {m : ℕ} (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .layers L) (ties : LayersTies L p4 nU)
    (hψ : Rests u ψ) 
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (k3k : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok
      (c, e₁) → kapOf e₁ = kapOf e)
    (R : SortRest L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q)
      nU [(1, "objects"), (6, "objects")] t3 l3) :
    LayersOwesC m p4 Kx t3 l3 L u ψ nU p tlD where
  seg := seg
  ties := ties
  hψ := hψ
  h4 := R.h4
  k3 := R.k3
  k3d := R.k3d
  k3g := R.k3g
  k3f := R.k3f
  k3p := R.k3p
  k3s := R.k3s
  k3sL := R.k3sL
  k3k := k3k
  drawB := drawB
  rows := rows

/-- **`AttOwesC` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem attOwesC_of_rest {m : ℕ} (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .attention L) (ties : AttTies L c nU)
    (hψ : Rests u ψ) (hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (k3k : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c' e₁, run n e = .ok (c', e₁) → kapOf e₁ = kapOf e)
    (R : SortRest L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q)
      nU [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")] t3 l3) :
    AttOwesC m rd c Kx t3 l3 L u ψ nU p tlD where
  seg := seg
  ties := ties
  hψ := hψ
  hrd := hrd
  h4 := R.h4
  k3 := R.k3
  k3d := R.k3d
  k3g := R.k3g
  k3f := R.k3f
  k3p := R.k3p
  k3s := R.k3s
  k3sL := R.k3sL
  k3k := k3k
  drawB := drawB
  rows := rows

/-- **`HeadOwesC` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem headOwesC_of_rest {m : ℕ} (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 :
  Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .head L) (ties : HeadTies L hS iU3 l' piece p6 nU)
    (hψ : Rests u ψ) (hkap : ∀ e, kap (phiAll u ψ e) = Kinds.Head.Law.seenOf e)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (k3k : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁,
      run n e = .ok (c, e₁) → kapOf e₁ = kapOf e)
    (R : SortRest L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU [(2, "objects"), (2,
      "planes"), (7, "objects")] t3 l3) :
    HeadOwesC m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD where
  seg := seg
  ties := ties
  hψ := hψ
  hkap := hkap
  h4 := R.h4
  k3 := R.k3
  k3d := R.k3d
  k3g := R.k3g
  k3f := R.k3f
  k3p := R.k3p
  k3s := R.k3s
  k3sL := R.k3sL
  k3k := k3k
  drawB := drawB
  rows := rows

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layersOwesC_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.attOwesC_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.headOwesC_of_rest
