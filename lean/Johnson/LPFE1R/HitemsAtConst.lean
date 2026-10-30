-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HitemsAtConst.lean: e₁'s ROW 170: CoreLeft's FIELD hitems
(Link/Law/CoreLeft.lean) AT THE CLOSED CONSTANT, AT ALL THREE SORTS OF LINK, AT items := sortItems
sub (Link/Law/SortItems.lean): THE JOIN OF ITS THREE PAYERS
(hitems_layers | hitems_attention; hitems_head) WITH WHAT LIES FOR THEIR
PREMISES; WHAT IS NOT PAID HERE STANDS IN ONE NAMED REST. Definitions, statements and proofs.

  HitemsLeft      THE REST: three fields: ok (Ok of what is fixed, at every state of the condition
                  in front of the batching) · in8 (the public test formsIn at the entry
                  "K8.equations": the promise holds only the weaker formsInA there) · k3i (the
                  items' clauses at the lookups' entries)
  on0At           the condition in front of link m's batching at the constant's letters (K9Left's
                  o0)
  readers_at24    the constant's readers are K9.readersAt at the head's link's number 24
                  (headLink_in_scope)
  part_at         a part is there at every state of on0At: part_at_batch_all
  hin_all         hin at every entry of the sort's list: LPFE1R/HinAtConst.lean's hin_at, and in8 at
                  "K8.equations"
  hitems_layers_at · hitems_att_at · hitems_head_at: the field's text (ItemIn is its body:
                  Link/Law/HitemsStill.lean), from the sort's Take, hAt, h4 and the rest; at the
                  head besides hrun (the run's own reader answers at six entries: shown of no state
                  by a theorem; evaluated true at the honest state at both sizes)

PAID HERE, AGAINST THE THREE PAYERS' LISTS OF PREMISES: hlk · hm (the link is not the head's) · hit
(SortItems) · hon's first half (a part is there) · hin at all entries but one. LEFT AS PREMISES: the
sort's Take (a field of the sort's own list) · hAt · h4 · HitemsLeft's three · hrun at the head.
Limits. IMPLICATIONS. tm4, t3, l3, u, ψ, Ok, Fu, nU and the sorts' numbers are letters. The head
AtMgA is a premise. The full size alone. No soundness statement.

-/
import Johnson.LPFE1R.HinAtConst
import Johnson.LPFE1R.PartAtBatch
import Johnson.Desc.First.Link.Law.HitemsHead
import Johnson.Desc.First.Link.Law.SortItems
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart orderOf)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open K5Law
open IM (subAt)

/-- **WHAT IS LEFT OF hitems.** -/
structure HitemsLeft {α W : Type} {F : Frame} (on0 : S × F.E.Str → Prop) (L : Link S Claim)
    (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (o8 : ℕ × String) (k3s : List (ℕ × String)) : Prop where
  /-- Ok of what is fixed -/
  ok : ∀ a, on0 a → Ok (fixed9 φ a.1)
  /-- the public test at "K8.equations" -/
  in8 : ∀ a, on0 a → K9.formsIn Rd own o8.1 o8.2 a.1 = true
  /-- the clauses at the lookups' entries -/
  k3i : ∀ a w, on0 a → ∀ e ∈ k3s, ItemIn L φ tmOf lenOf Rd own rdW a w e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- The condition in front of link m's batching, at the constant's letters. -/
def on0At (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) (m : ℕ) :
    S × (Frame.E FrK).Str → Prop :=
  onTR h.𝔇.N (mgAll h.𝔇 mgBase) P5J.fullLinks P5J.At.ps (fun s : S => (z, s))
    (RchAt (F := FrK) h.toAtMg.rch z) (batchAt P5J.fullLinks P5J.At.ps m)

/-- The constant's readers, with the head's link's number written out. -/
theorem readers_at24 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) :
    h.𝔇.Rd m = K9.readersAt h.𝔇.lk (P5J.At.X Zp) 24 m := by
  unfold MgData.Rd
  rw [P5J.headLink_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne]

/-- A part is there. -/
theorem part_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (a) (ha : on0At h z m a) : (atS.get? a.1).isSome = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : IM.linksW = P5J.fullLinks := LPFK9.linksW_full
  have ep : IM.placesW = P5J.At.ps := by
    unfold IM.placesW P5J.At.ps
    rw [e]
  have H := part_at_batch_all (N := h.𝔇.N) (Mg := mgAll h.𝔇 mgBase) (z := z)
    (Rz := RchAt (F := FrK) h.toAtMg.rch z) h.scope h.reads O
    (fun j b hb => P5J.list_rchIs h z j b hb) hm (a := a)
  rw [ep, e] at H
  exact H ha

/-- hin at every entry of the sort's list. -/
theorem hin_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) {o8 : ℕ × String}
    (h8 : ∀ e ∈ sortItems (subAt m), (e.2 == "K8.equations") = true → e = o8)
    (in8 : ∀ a, on0At h z m a → K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) o8.1 o8.2 a.1 = true) :
    ∀ a, on0At h z m a → ∀ e ∈ sortItems (subAt m),
      K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) e.1 e.2 a.1 = true := by
  intro a ha e he
  cases hb : (e.2 == "K8.equations") with
  | true =>
    rw [h8 e he hb]
    exact in8 a ha
  | false => exact hin_at h hm z (RchAt (F := FrK) h.toAtMg.rch z) a ha he hb

section
variable {β W : Type} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **hitems AT A LAYERS' LINK, AT THE CONSTANT.** -/
theorem hitems_layers_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .layers) (hlk : h.𝔇.lk m = some L) (hL : SegAt m .layers L)
    {p : OnBytes.Desc.First.K4.Par} (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (4, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (rdW : W → ℕ × ℕ → MsgQ)
    (R : HitemsLeft (on0At h z m) L (phiAll u ψ) Ok (tmL p entUnit tm4 t3) (lenL p l3) (h.𝔇.Rd m)
      (h.𝔇.N.group m) rdW (4, "K8.equations") [(1, "objects"), (6, "objects")]) :
    ∀ a w, on0At h z m a → ∀ e ∈ sortItems .layers, ItemIn L (phiAll u ψ) (tmL p entUnit tm4 t3)
      (lenL p l3) (h.𝔇.Rd m) (h.𝔇.N.group m) rdW a w e := by
  have h24 : (m == 24) = false := by
    cases e : (m == 24) with
    | false => rfl
    | true =>
      obtain rfl : m = 24 := by simpa using e
      exact absurd hs (by decide)
  have hin := hin_all h z hm (o8 := (4, "K8.equations")) (by rw [hs]; decide) R.in8
  rw [hs] at hin
  have k3 := R.k3i
  rw [readers_at24 h m] at hin k3 ⊢
  exact hitems_layers h.𝔇.lk (P5J.At.X Zp) 24 m hlk h24 hL A run hAt v4 h4 (h.𝔇.N.group m) rdW
    (on0At h z m) (sortItems .layers) hit_layers
    (fun a ha => ⟨part_at h z hm a ha, R.ok a ha⟩) hin k3

/-- **hitems AT AN ATTENTION LINK, AT THE CONSTANT.** -/
theorem hitems_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .attention) (hlk : h.𝔇.lk m = some L)
    (hL : SegAt m .attention L) {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} (A : AttTake L u ψ Ok Fu rd c nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (4, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (rdW : W → ℕ × ℕ → MsgQ)
    (R : HitemsLeft (on0At h z m) L (phiAll u ψ) Ok (tmA rd c entUnit tm4 t3) (lenA rd c l3)
      (h.𝔇.Rd m) (h.𝔇.N.group m) rdW (4, "K8.equations")
      [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")]) :
    ∀ a w, on0At h z m a → ∀ e ∈ sortItems .attention, ItemIn L (phiAll u ψ)
      (tmA rd c entUnit tm4 t3) (lenA rd c l3) (h.𝔇.Rd m) (h.𝔇.N.group m) rdW a w e := by
  have h24 : (m == 24) = false := by
    cases e : (m == 24) with
    | false => rfl
    | true =>
      obtain rfl : m = 24 := by simpa using e
      exact absurd hs (by decide)
  have hin := hin_all h z hm (o8 := (4, "K8.equations")) (by rw [hs]; decide) R.in8
  rw [hs] at hin
  have k3 := R.k3i
  rw [readers_at24 h m] at hin k3 ⊢
  exact hitems_attention h.𝔇.lk (P5J.At.X Zp) 24 m hlk h24 hL A run hAt v4 h4 (h.𝔇.N.group m) rdW
    (on0At h z m) (sortItems .attention) hit_attention
    (fun a ha => ⟨part_at h z hm a ha, R.ok a ha⟩) hin k3

/-- **hitems AT THE HEAD's LINK, AT THE CONSTANT.** -/
theorem hitems_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (hlk : h.𝔇.lk 24 = some L) (hL : SegAt 24 .head L) {hS : OnBytes.Model.Head.Shape}
    {iU3 l' piece : ℕ} {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu hS iU3 l' piece p kap nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (5, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (rdW : W → ℕ × ℕ → MsgQ)
    (R : HitemsLeft (on0At h z 24) L (phiAll u ψ) Ok (tmH hS iU3 p kap entUnit tm4 t3)
      (lenH hS iU3 p kap l3) (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW (5, "K8.equations")
      [(2, "objects"), (3, "join"), (2, "planes"), (7, "objects")])
    (hrun : ∀ a, on0At h z 24 a → ∀ e ∈ sortItems .head, e ∈ [(2, "guests"), (3, "norm"),
      (3, "policy"), (3, "logits"), (7, "guests"), (8, "the merge")] →
      (K9.readerOf (K9.statesOfLink L) e.1 e.2 a.1).isSome = true) :
    ∀ a w, on0At h z 24 a → ∀ e ∈ sortItems .head, ItemIn L (phiAll u ψ)
      (tmH hS iU3 p kap entUnit tm4 t3) (lenH hS iU3 p kap l3) (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW
      a w e := by
  have hs : subAt 24 = .head := by decide
  have hin := hin_all h z (m := 24) (by omega) (o8 := (5, "K8.equations")) (by rw [hs]; decide)
    R.in8
  rw [hs] at hin
  have k3 := R.k3i
  rw [readers_at24 h 24] at hin k3 ⊢
  exact hitems_head h.𝔇.lk (P5J.At.X Zp) 24 hlk hL A run hAt v4 h4 (h.𝔇.N.group 24) rdW
    (on0At h z 24) (sortItems .head) hit_head
    (fun a ha => ⟨part_at h z (by omega) a ha, R.ok a ha⟩) hin hrun k3

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.readers_at24
#print axioms VerifiableInference.Desc.LinkJoin.part_at
#print axioms VerifiableInference.Desc.LinkJoin.hin_all
#print axioms VerifiableInference.Desc.LinkJoin.hitems_layers_at
#print axioms VerifiableInference.Desc.LinkJoin.hitems_att_at
#print axioms VerifiableInference.Desc.LinkJoin.hitems_head_at
