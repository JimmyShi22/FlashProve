-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MaskSeatAt.lean: THE KIND "LOOKUP" (K3): THE NAMED PREMISE K03MaskAt
(Johnson/P5J/K03ObjInAt.lean) PAID AT THE COMPOSED MEANING's OWN PARAMETERS: BEHIND AN ACCEPT OF THE
LOOKUP ON A SEGMENT's CALLS THE MASK ROW's MESSAGE IS SENT AND SEATED AMONG THE SEGMENT's OWN. One
definition with code; theorems. AN APPLICATION: the general lemma is the lookup's
files' `hmask_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsPaid.lean).

  `maskTests_move`: the lookups' test `maskTestsB` reads its place p through `N.msgsAt p` alone: at
    two places with one number it is one test.
  `k03_msgs_calls`: the numbers of messages by place in front of and behind the calls' lookup are
    one: `bookFit_at` and `told_succ_nil` (Johnson/Desc/First/BookFit.lean): the lookup
    tells no tree.
  `AtMgA.maskC h L y l`: the closed test, by name: the field hTests of ObjShortR
    (Johnson/P5J/K03ObjAt.lean), to the letter: `maskTestsB` at the border BEHIND.
  `k03_maskAt`: the head · the filling · FoldFacts at the closed public numbers · l < 25 · the
    place y of lookAt
    with its shape, its number of slots and 0 < y.ns · maskC · ObjShortR's hB and h6 · "every member
    of the calls' list has an alike member" give `K03MaskAt h l q b'`.
NO PROMISE BEHIND THE ACCEPT IS SPENT (the lemma spends none). NO NEW TEST: its premise hTestsF (the
test at the border IN FRONT) comes from maskC by the first two lemmas.
Limits. FoldFacts, maskC, hB, h6, hsome, hns and 0 < y.ns are premises here. At OnBytes.secondHashFunction. The
full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03ObjInAt
import Johnson.P5J.K03OthersPubAt
import Johnson.P5J.K03FoldAt
import Johnson.P5J.K03BookAt
import Johnson.Desc.Sound.MgAt.K3CallsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (FoldFacts Numbers)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

/-- The test reads its place through the number of messages alone. -/
theorem maskTests_move {kM? : Option ℕ} {kept : ℕ} {nos : Array ℕ} {N : Numbers}
    {p p' : Option VerifiableInference.Desc.Place} {Ld : Laid} {M : List OracleShape}
    {own : List (ℕ × ℕ)} {seatN : ℕ → ℕ × ℕ} (e : N.msgsAt p' = N.msgsAt p)
    (h : maskTestsB kM? kept nos N p Ld M own seatN = true) :
    maskTestsB kM? kept nos N p' Ld M own seatN = true := by
  unfold maskTestsB bookedB at h ⊢
  rw [e]
  exact h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {L : Laid}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- In front of and behind the calls' lookup the number of messages by place is one. -/
theorem k03_msgs_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) :
    (At.N Zp cF).msgsAt PS[k3K l false]? = (At.N Zp cF).msgsAt PS[k3K l false + 1]? := by
  have hk : k3K l false < (PS).length :=
    (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl false)).1
  have a := VerifiableInference.Desc.First.bookFit_at (At.N Zp cF) PS (At.told cF)
    (k03_book_at Zp cF) (k3K l false) (Nat.le_of_lt hk)
  have b := VerifiableInference.Desc.First.bookFit_at (At.N Zp cF) PS (At.told cF)
    (k03_book_at Zp cF) (k3K l false + 1) hk
  have c := VerifiableInference.Desc.First.told_succ_nil (At.told cF) (k3K l false)
    (k03_tells_at h.toAtMg l hl false)
  rw [a.2, b.2, c.2]

/-- **The closed test, by name**: ObjShortR's field hTests. -/
def AtMgA.maskC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (L : Laid)
    (y : VerifiableInference.Desc.First.Look.Place) (l : ℕ) : Bool :=
  maskTestsB (maskMsg (h.toAtMg.𝔇 h.𝔇).sent y.link)
    (VerifiableInference.Desc.First.Look.keptAt (h.toAtMg.𝔇 h.𝔇).sent y.link).length
    ((h.toAtMg.𝔇 h.𝔇).pubD.dS.own y.link) (h.toAtMg.𝔇 h.𝔇).N PS[k3K l false + 1]? L
    (msgsOfChain Zp.made.proof.1) ((h.toAtMg.𝔇 h.𝔇).N.sent l 0)
    ((h.toAtMg.𝔇 h.𝔇).seat3 y.link false)

set_option maxHeartbeats 4000000 in
/-- **K03MaskAt, PAID.** -/
theorem k03_maskAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
    {l : ℕ} (hl : l < 25) {y : VerifiableInference.Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l false = some y)
    (hsP : (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame)
      false y).shape = some y.fs)
    (hns : ((h.toAtMg.𝔇 h.𝔇).built[l]?).map (·.ns) = some y.ns) (hns0 : 0 < y.ns)
    (hT : h.maskC L y l = true)
    (hB : maskCallsB (h.toAtMg.𝔇 h.𝔇).sent
      (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 y.link) y.link y.ns = true)
    (hsome : ∀ i, ∃ m ∈ (h.toAtMg.𝔇 h.𝔇).ms, Alike m
      ⟨⟨sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 y.link,
        fun j => (h.toAtMg.𝔇 h.𝔇).seat3 y.link false j.1⟩, i⟩)
    (h6 : oneShapeB (h.toAtMg.𝔇 h.𝔇).ms = true) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    K03MaskAt h l q b' := by
  intro q hq b' hb'
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have hTF := maskTests_move (k03_msgs_calls h hl) hT
  unfold K03MaskAt
  rw [ek] at hTF ⊢
  exact hmask_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
    (K.planOk l hl false b' hb') (K.back l hl false q hq) rfl hpcX hpc hl hs'
    (ek ▸ K3Lot.k03_at_full l hl false) hlook hsP rfl
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) hns hns0
    (k03_hLive h F (kOfCalls l)) (k03_hGroups h F (kOfCalls l)) (k03_hSeats h F (kOfCalls l))
    (k03_hShapes h F (kOfCalls l)) hTF hB hsome h6

end P5J

#print axioms P5J.maskTests_move
#print axioms P5J.k03_msgs_calls
#print axioms P5J.k03_maskAt
