-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09List.lean: THE BATCHING KIND's FIELD OF THE KINDS' LAWS AT THE CLOSED CONSTANT
(`h.Kind 𝔏 .K9`), AT THE SECOND HASH FUNCTION, FROM THE TWO NAMED LISTS OF WHAT IS LEFT AT EACH OF
ITS 25 LINKS: `LinkList` at the link's three pieces (Johnson/Desc/First/Link/Law/LinkList.lean) and
`ShutList` at its shutting's piece (ShutList.lean), WITH THE FACTS ON THE SEAT PAID: by
`fields_at_constant` (Johnson/LPFK9R/SitsAtConstant.lean), and here. Definitions and theorems.

What is said.
  `AtMgA.Sits h m L p Q b₃ b₅`: the facts on the seat at link m, by name: the composed meaning's
    link of that number is L, with its ties; L's two own sub-protocols, b₃ and b₅ stand at the
    link's four numbers of the seated description's flat list; the first two are rows of moves; a
    yes of b₃ is the one equation's, a yes of b₅ the shutting's. `sits_at`: **there are such letters
    at every link** (a call). `AtMgA.K9List h 𝔏`: at every link THERE ARE letters that sit there
    (the payer's choice; `sits_at` shows that some do) with: at the three pieces at its numbers:
    there are the law's letters with `LinkList` at every public part; at the shutting's piece: there
    are three letters with `ShutList` at every public part. `k9Laws_of_list`: **`h.K9Laws 𝔏`
    (K09Seat.lean) from it.** `k09_kind_of_list`: **so `h.Kind 𝔏 .K9`**, under the tower's own
    three equations on the flat lists' heads and «no fewer pieces than places». PAID HERE, AT THE
    CONSTANT: `list_hd` (the committed table's decoder answers alike at any two states: by
    definition), `list_rchIs` («reached» is reached along the flat list:
    `rchAt_raw`), `list_hand` («reached» is handed on over a carriage's piece: kind-free),
    `batchIx_links`, `linkFit_links`, `pubFit9_links` (the kernel).

Limits. BOOK-KEEPING. `K9List` IS THE DEBT: 45 named fields at a link's three pieces and ten at its
shutting's, the letters under «there are»; NO FIELD IS A TIE, A PIECE's LAW OR A HAND-ON OF THE
PROMISE; no member is known; that the fields can be met together is shown nowhere; the count of
fields is no measure. AT THE SECOND HASH FUNCTION ALONE (as the top). Nothing on soundness.

-/
import Johnson.P5J.K09Seat
import Johnson.Desc.First.Link.Law.LinkList
import Johnson.LPFK9R.SitsAtConstant
import Johnson.Desc.First.Link.Law.HandsOnRec

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
open VerifiableInference.Desc.LinkJoin (batchAt atRec LinkList threeAsksR_of_list ShutList
  shutOwesR_of_list rows9Fit_links rowOpenFit_links placesFit_links moreFit_links SegAt batchIx
  linkFit pubFit9 reach_hand_rec)
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open IM (subAt)

set_option maxRecDepth 1000000 in
/-- **THE BATCHINGS' NUMBERS, BY THE KERNEL.** -/
theorem batchIx_links : ((List.range 25).all fun m =>
    decide (batchAt fullLinks (flatPlacesOf fullLinks true) m = batchIx m)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Two elder Bools on the written list, at the term `fullLinks` (MeansQ.lean), by the kernel. -/
theorem linkFit_links : linkFit fullLinks (flatPlacesOf fullLinks true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pubFit9_links :
    pubFit9 true moreAll fullLinks (flatPlacesOf fullLinks true) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- Two fields of the list hold outright at the closed constant. -/
theorem list_hd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) :
    ∀ c (s s' : S), h.𝔇.decT c (z, s') = h.𝔇.decT c (z, s) := fun _ _ _ => rfl

theorem list_rchIs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) :
    ∀ j a, VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z j a →
      Reach 0 (FD).first.blocksInOrder (FD).start₁ j (z, a.1) :=
  fun _ _ ha => rchAt_raw ha.1

/-- **«REACHED» IS HANDED ON OVER THE CARRIAGE's PIECE THAT HOLDS THE SUB-PROTOCOL AT ITS NUMBER.**
Kind-free. -/
theorem list_hand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) (k : ℕ)
    (B : Block S ProofFile.Cl) (hB : (FD).first.blocksInOrder[k]? = some B)
    (q : Piece (ckP .two) FrK (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsM numsFull) At.Tok MsgT)) :
    HandsOn (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z) k
      (atRec q (below B)) :=
  fun a τ b hr hout =>
    ⟨reach_hand_rec z (atRec q (below B))
      (List.getElem?_map.trans (congrArg (Option.map below) hB)) a b τ hout hr.1, hr.2⟩

/-- **THE FACTS ON THE SEAT AT LINK m, BY NAME.** -/
structure AtMgA.Sits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (L : Link S ProofFile.Cl)
    (p : Where) (Q : VerifiableInference.Desc.First.Close.Par) (b₃ b₅ : Block S ProofFile.Cl) :
    Prop where
  sort : fullLinks[m]? = some (subAt m)
  lk : h.𝔇.lk m = some L
  seg : SegAt m (subAt m) L
  atK : (FD).first.blocksInOrder[kAt m]? = some L.batchB
  atK1 : (FD).first.blocksInOrder[kAt m + 1]? = some L.behindB
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  movesQ : IsMoves atS [.quiet L.runBehind] L.behindB
  atK2 : (FD).first.blocksInOrder[kAt m + 1 + 1]? = some b₃
  hb₃ : ∀ ft s rs cols y, b₃.step ft s rs cols = .ok y →
    (VerifiableInference.Desc.K9.oneEquation (Cl := ProofFile.Cl) atS p).step ft s rs cols = .ok y
  atK4 : (FD).first.blocksInOrder[kAt m + 4]? = some b₅
  hb₅ : ∀ ft s rs cols y, b₅.step ft s rs cols = .ok y →
    (VerifiableInference.Desc.K9.shut (Cl := ProofFile.Cl) p (Q.piece + 1)).step ft s rs cols = .ok y

/-- **THERE ARE SUCH LETTERS AT EVERY LINK.** -/
theorem sits_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ := by
  obtain ⟨L, p, Q, a1, a2, a3, a4, a5, a6, a7, ⟨b₃, a8, a9⟩, b₅, a10, a11⟩ :=
    LPFK9.fields_at_constant h m hm
  exact ⟨L, p, Q, b₃, b₅, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

/-- **WHAT IS LEFT AT THE 25 LINKS, AT THE CLOSED CONSTANT.** -/
def AtMgA.K9List (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧
    (∀ qb qq qe, (h.toAtMg.row 𝔏)[kAt m]? = some qb →
      (h.toAtMg.row 𝔏)[kAt m + 1]? = some qq → (h.toAtMg.row 𝔏)[kAt m + 1 + 1]? = some qe →
      ∃ (α : Type) (φ : _) (Ok : _) (nU : _) (tmOf : _) (lenOf : _) (d N : ℕ) (items : _) (u : _)
        (π : _) (oo : _) (run : _) (xx : _) (tlD : _) (set : _) (pp : ℕ) (fd : _) (reqW : _), ∀ z,
        LinkList (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m α (subAt m) L φ Ok nU p
          p tmOf lenOf d N b₃ (atRec qb (below L.batchB)) (atRec qq (below L.behindB))
          (atRec qe (below b₃)) items u π oo run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) 0 (FD).first.blocksInOrder (FD).start₁ fd reqW) ∧
    ∀ qs, (h.toAtMg.row 𝔏)[kAt m + 4]? = some qs → ∃ Zc layF Dw, ∀ z,
      ShutList (F := FrK) h.𝔇 fullLinks At.ps z
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m + 4) (atRec qs (below b₅))
        Zc layF Dw

/-- **THE LAWS FROM THE LISTS.** -/
theorem k9Laws_of_list (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (H : h.K9List 𝔏) : h.K9Laws 𝔏 := by
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
    exact ⟨_, _, _, _, _, fun z => threeAsksR_of_list h.𝔇 fullLinks At.ps z _ _ m rfl
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
theorem k09_kind_of_list (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hlen : At.ps.length ≤ (h.toAtMg.row 𝔏).length) (H : h.K9List 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_laws h 𝔏 q₁ q₂ q₃ hlen (k9Laws_of_list h 𝔏 H)

end P5J

#print axioms P5J.batchIx_links
#print axioms P5J.linkFit_links
#print axioms P5J.pubFit9_links
#print axioms P5J.list_rchIs
#print axioms P5J.list_hand
#print axioms P5J.sits_at
#print axioms P5J.k9Laws_of_list
#print axioms P5J.k09_kind_of_list
