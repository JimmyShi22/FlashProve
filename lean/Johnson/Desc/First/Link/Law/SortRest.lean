-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortRest.lean: WHAT IS LEFT OF A SORT's OWN FIELDS (`LayersOwes`,
`AttOwes`, `HeadOwes`, LinkRestAtSort4.lean) ONCE THE FIELDS THAT HAVE PAYERS AT THE CONSTANT ARE
TAKEN OUT: ONE STRUCTURE FOR ALL THREE SORTS. A structure of sentences, and theorems: assemblies.
For joining the sorts at the constant.

Why one structure. The eight fields that have no payer here (h4: the smallness test's first four
claims; k3, k3d, k3g, k3f, k3p, k3s, k3sL: the lookup argument's runs) have one text at the three
sorts but for two letters: the promise Ok, and the list of the lookup's entries (HELD BY PROGRAM
over the three Takes' own texts; at the attention one BOUND letter bears another name, c' for c,
since c is that sort's own letter: the same sentence). With these two as letters the three rests
are one. THEIR PAYERS, ELSEWHERE: h4: h4_of_core
(SortFour.lean), at phiAll u ψ and FullAt nU, under hψ and hc. The seven, at psiAll · t3All · l3All,
at secondHashFunction alone, at the links of the closed constant: lookRest_layers_at, lookRest_att_at,
lookRest_head_at (Johnson/LPFK9R/LookLayersAtMg.lean, LookAttAtMg.lean, LookHeadAtMg.lean): from the
standing hypotheses (P5J.AtMgA), the opening O, hlk and hK; at a layers' link also hm, h24; at an
attention link also h4, hg, ha, hm, k3pl, k3jn; at the head's also k3pl.

What is said.
  `SortRest L u ψ Ok nU ents t3 l3`: the eight fields, in the texts of LinkRestAtSort4.lean (cut by
    the same program), Ok and ents letters.
  `layersOwes_of_rest`, `attOwes_of_rest`, `headOwes_of_rest`: **the sort's own fields whole**,
    from seg, ties, hψ (hrd; hkap), drawB, rows and SortRest at Ok := fun q => (‹the named Ok› q ∧
    Kx q) ∧ rowsFit p.rows pi8 q and the sort's own list of entries.

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE OR RUN. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort4

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

/-- **THE ONE REST OF A SORT's OWN FIELDS.** -/
structure SortRest (L : Link S Claim) (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (ents : List (ℕ × String)) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) : Prop where
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) Ok q e → good9 e → atS.get? e = some a → k8Run.2 front e
    = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) Ok (FullAt nU)) e₁ t → (FullAt nU)
    t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
    termsAt GE8 (tmFour (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
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

/-- **`LayersOwes` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem layersOwes_of_rest {m : ℕ} (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .layers L) (ties : LayersTies L p4 nU)
    (hψ : Rests u ψ) 
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (R : SortRest L u ψ (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q)
      nU [(1, "objects"), (6, "objects")] t3 l3) :
    LayersOwes m p4 Kx t3 l3 L u ψ nU p tlD where
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
  drawB := drawB
  rows := rows

/-- **`AttOwes` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem attOwes_of_rest {m : ℕ} (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .attention L) (ties : AttTies L c nU)
    (hψ : Rests u ψ) (hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (R : SortRest L u ψ (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q)
      nU [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")] t3 l3) :
    AttOwes m rd c Kx t3 l3 L u ψ nU p tlD where
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
  drawB := drawB
  rows := rows

/-- **`HeadOwes` FROM THE PAID FIELDS AND THE ONE REST.** -/
theorem headOwes_of_rest {m : ℕ} (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 :
  Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Q β → Prop) (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) {L : Link S Claim} (u : HTailF2) {ψ : S → β} {nU : Array ℕ}
    {p : Where} (tlD : HTailF2) (seg : SegAt m .head L) (ties : HeadTies L hS iU3 l' piece p6 nU)
    (hψ : Rests u ψ) (hkap : ∀ e, kap (phiAll u ψ e) = Kinds.Head.Law.seenOf e)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0)
    (R : SortRest L u ψ (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧ (rowsFit
      p.rows pi8) q) nU [(2, "objects"), (2, "planes"), (7, "objects")] t3 l3) :
    HeadOwes m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD where
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
  drawB := drawB
  rows := rows

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layersOwes_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.attOwes_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.headOwes_of_rest
