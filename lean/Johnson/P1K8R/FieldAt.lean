-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FieldAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
KIND'S LAW IN THE LETTERS OF THE JOIN AT THE TOP. NO SOUNDNESS.

The join at the top takes one law for each kind of sub-protocol as a hypothesis: at every piece of
the first chain whose place is of the kind: `TiedAtR` at the closed constant's numbers, meaning,
list of segments, places and reader of the statement, at the join's own condition beside the
promise, and at the piece WITH THE TABLE's OWN EXTRACTOR. `k08_at_const` ends in
that but for three letters (the condition beside the promise is a letter of `k08_at_const`
itself). Here they are turned:
  `laysNoneK8_full`, `ext_id_k8`: the table's row at each of the kind's 25 places lays nothing (by
    the kernel, on the written list): so the table's own extractor `extQAt` is the identity there,
    whatever its letters.
  `k08_field`: **`k08_at_const`'s premises give the join's field for the kind K8**, at
    `P5J.At.links`, `P5J.At.ps`, `P5J.At.get`, at every condition Rch' that gives `RchAt`, at
    `extQAt` at whatever decoder, first cells and tokens.
Limits. As `k08_at_const`'s: `K8LeftC` is shown nowhere
(Where this and lean/THEOREM.md differ, the page holds.): NOT TO BE TOLD AS
"TIED". General in T. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.ConstAt

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf rowOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- A test with code on the written list: the table's row at the draw's place lays nothing. -/
def laysNoneK8B : Bool :=
  (List.range 25).all fun l =>
    match (flatPlacesOf linksFull true)[drawAt l]? with
    | some p => !(rowOf linksFull p).lays
    | none => false

set_option maxRecDepth 1000000 in
theorem laysNoneK8_full : laysNoneK8B = true := by decide +kernel

open Cb in
/-- **The table's own extractor is the identity at the kind's 25 places.** -/
theorem ext_id_k8 {Xi Pp Cells Tok A : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
    (tokOf : Pp × S → Tok) (N : Numbers) (get : A → Pp × S) (l : ℕ) (hl : l ≤ 24)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get (drawAt l)
      a b w = w := by
  have h := List.all_eq_true.1 laysNoneK8_full l (List.mem_range.2 (by omega))
  unfold extQAt
  cases hp : (flatPlacesOf linksFull true)[drawAt l]? with
  | none => rfl
  | some p =>
    rw [hp] at h
    exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull p (by simpa using h) _ _ _ w

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE JOIN's FIELD FOR THE KIND K8.** -/
theorem k08_field (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hDoor : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true)
    (hW : planFitsAllB Zp.p.X = true) (hGt : Second.K08.gtSizesAllB Zp.p.X = true)
    (hFit : ∀ y ∈ P5J.At.ms Zp Z.lay,
      SeatFits (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (P5J.At.cs Zp) y.1.l y.1.seat)
    {D : WholeD} (hD : (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF).data "proof file" = .ok D)
    {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (Run.ckP .two) D all (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) X₁ X₂
      (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)}
    (hT : OfDesc _ T) (hf : Three.Fits T)
    (Rch' : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (hR' : ∀ k a, Rch' k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (H : ∀ (G : ProofFile.Ground) l Xl q, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
      G.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8LeftC h (P5J.At.rad3At Zp Z.lay) G.W l q (ProofFile.k8ParW Zp G Xl l) Rch')
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S →
      Option (P5J.CellsM OnBytes.Flat.numsFull))
    (c₀ : P5J.CellsM OnBytes.Flat.numsFull) (tokOf : ProofFile.InstPub × S → P5J.At.Tok) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → P5J.At.ps[i]? = some p → p.kind = KindName.K8 →
      TiedAtR (P5J.At.N Zp cF) (mgAll h.𝔇 mgBase) P5J.At.links P5J.At.ps P5J.At.get Rch' i
        (q.withMap (extQAt (P5J.At.cs Zp) (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
          (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) decT c₀ tokOf (P5J.At.N Zp cF)
          P5J.At.links P5J.At.ps P5J.At.get i)) := by
  intro i q p hq hp hk
  exact k08_at_const h hDoor hW hGt hFit hD hT hf
      (fun i => extQAt (P5J.At.cs Zp) (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (P5J.At.arr Zp)
        (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) decT c₀ tokOf (P5J.At.N Zp cF) linksFull
        (flatPlacesOf linksFull true) (fun a => a) i)
      (fun l hl a b w => ext_id_k8 _ _ _ _ _ _ _ _ _ _ l hl a b w) Rch' hR' H i q p hq hp hk

end

end P1K8T

#print axioms P1K8T.ext_id_k8
#print axioms P1K8T.k08_field
