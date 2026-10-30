-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09ListC.lean: ON THE SECOND ROAD: THE BATCHING KIND's LAWS AT THE 25 LINKS OF THE
CLOSED CONSTANT (`AtMgA.K9Laws`, K09Seat.lean) FROM A SECOND NAMED LIST, BESIDE `AtMgA.K9List`
(K09List.lean, which does not turn): at a link's three pieces `LinkListC`
(Johnson/Desc/First/Link/Law/LinkListC.lean: the law's letter C at «the rows fit, and the runs'
claims are at most the plan's number») in `LinkList`'s place; at the shutting's piece `ShutList`, as
there. The elder file's text with these names turned. A definition and theorems.

What is said.
  `AtMgA.K9ListC h 𝔏`: as `K9List`, with `LinkListC`. `k9Laws_of_listC`: **`h.K9Laws 𝔏` from it.**
    `k09_kind_of_listC`: **so `h.Kind 𝔏 .K9`**, under the tower's own three equations on the flat
    lists' heads and «no fewer pieces than places».

Limits. BOOK-KEEPING. `K9ListC` IS THE DEBT; no member is known. It ends in the same `K9Laws`, and
so in the same named condition (`K9Cond`), as the elder list. AT THE SECOND HASH FUNCTION ALONE.
Nothing on soundness.

-/
import Johnson.P5J.K09List
import Johnson.Desc.First.Link.Law.LinkListC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link claimsInBy)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L (DrawMoves IsMoves Move)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt atRec LinkListC threeAsksR_of_listC ShutList
  shutOwesR_of_list rows9Fit_links rowOpenFit_links placesFit_links moreFit_links SegAt batchIx
  linkFit pubFit9 reach_hand_rec)
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT AT THE 25 LINKS, AT THE CLOSED CONSTANT, ON THE SECOND ROAD.** -/
def AtMgA.K9ListC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧
    (∀ qb qq qe, (h.toAtMg.row 𝔏)[kAt m]? = some qb →
      (h.toAtMg.row 𝔏)[kAt m + 1]? = some qq → (h.toAtMg.row 𝔏)[kAt m + 1 + 1]? = some qe →
      ∃ (α : Type) (φ : _) (Ok : _) (nU : _) (tmOf : _) (lenOf : _) (d N : ℕ) (items : _) (u : _)
        (π : _) (oo : _) (run : _) (xx : _) (tlD : _) (set : _) (pp : ℕ) (fd : _) (reqW : _), ∀ z,
        LinkListC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m α (subAt m) L φ Ok nU p
          p tmOf lenOf d N b₃ (atRec qb (below L.batchB)) (atRec qq (below L.behindB))
          (atRec qe (below b₃)) items u π oo run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) 0 (FD).first.blocksInOrder (FD).start₁ fd reqW) ∧
    ∀ qs, (h.toAtMg.row 𝔏)[kAt m + 4]? = some qs → ∃ Zc layF Dw, ∀ z,
      ShutList (F := FrK) h.𝔇 fullLinks At.ps z
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m + 4) (atRec qs (below b₅))
        Zc layF Dw

/-- **THE LAWS FROM THE LISTS.** -/
theorem k9Laws_of_listC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (H : h.K9ListC 𝔏) : h.K9Laws 𝔏 := by
  intro m hm
  have hm' : m < 25 := hm
  obtain ⟨L, p, Q, b₃, b₅, St, G⟩ := H m hm'
  have hx : kAt m = batchIx m :=
    of_decide_eq_true (List.all_eq_true.1 batchIx_links m (List.mem_range.2 hm'))
  refine ⟨fun qb qq qe B₁ B₂ B₃ hb hq he h1 h2 h3 => ?_, fun qs B₅ hs h5 => ?_⟩
  · obtain rfl : L.batchB = B₁ := Option.some.inj (St.atK.symm.trans h1)
    obtain rfl : L.behindB = B₂ := Option.some.inj (St.atK1.symm.trans h2)
    obtain rfl : b₃ = B₃ := Option.some.inj (St.atK2.symm.trans h3)
    obtain ⟨α, φ, Ok, nU, tmOf, lenOf, d, N, items, u, π, oo, run, xx, tlD, set, pp, fd, reqW, K⟩ :=
      G.1 qb qq qe hb hq he
    exact ⟨_, _, _, _, _, fun z => threeAsksR_of_listC h.𝔇 fullLinks At.ps z _ _ m rfl
      rows9Fit_links rowOpenFit_links placesFit_links hm' rfl rfl hx linkFit_links pubFit9_links
      moreFit_links α (subAt m) L φ Ok nU p p tmOf lenOf d N b₃ _ _ _ items u π oo run xx tlD set pp
      0 _ _ fd reqW St.sort (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) rfl rfl rfl
      St.seg St.lk St.atK St.atK1 St.drawB St.movesQ St.hb₃ (list_hand h z _ _ St.atK qb)
      (list_rchIs h z) (list_hd h z) (K z)⟩
  · obtain rfl : b₅ = B₅ := Option.some.inj (St.atK4.symm.trans h5)
    obtain ⟨Zc, layF, Dw, K⟩ := G.2 qs hs
    exact ⟨p, Q.piece + 1, fun z => shutOwesR_of_list h.𝔇 fullLinks At.ps z _ _ m hm' rfl rfl
      (by rw [hx]) rfl linkFit_links pubFit9_links moreFit_links p (Q.piece + 1) b₅ St.hb₅ _ rfl
      (fun _ _ _ => rfl) (list_hand h z _ _ St.atK4 qs) (list_hd h z) Zc layF Dw (K z)⟩

/-- **SO THE FIELD.** -/
theorem k09_kind_of_listC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hlen : At.ps.length ≤ (h.toAtMg.row 𝔏).length) (H : h.K9ListC 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_laws h 𝔏 q₁ q₂ q₃ hlen (k9Laws_of_listC h 𝔏 H)

end P5J

#print axioms P5J.k9Laws_of_listC
#print axioms P5J.k09_kind_of_listC
