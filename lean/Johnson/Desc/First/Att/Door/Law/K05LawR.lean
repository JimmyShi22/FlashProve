-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05LawR.lean: kind K5 (an attention segment's own rounds): **THE KIND's LAW, AS A STATEMENT, IN THE COUNTED FORM.** "reached" IS A TERM, NOT A LETTER: the one picked condition for all
kinds: RchPub (Johnson/Top/H0/Walk/ReachPub.lean) at the seated description (reached by the description's own sub-protocols, and the public part is a typed instance's); the numbers, the filling, the lists, the extractor and the pieces are those of the
definition P5J.AtMg.Kind (Johnson/P5J/RowsAtMg.lean) at the closed constant; the facts that the kind's road spends "from reached" are SEVEN NAMED PREMISES, each a sentence along that one "reached".

Typed by reading Johnson/P5J/RowsAtMg.lean · TowerEnd.lean · TowerFree.lean · MgAtAll.lean · AtMgR.lean ·
LettersAt2.lean · Johnson/Desc/First/FoldFacts.lean · Johnson/Desc/Sound/TiedR.lean · TiedRMono.lean · Johnson/Top/H0/Walk/ReachAt.lean · ReachPub.lean.
DEFINITIONS OF SENTENCES: NOT PROVED HERE. For a theorem that takes each kind's law as a hypothesis.

Main names:
  `typedPub`: "the public part is a typed instance's". `R1 F` := RchPub F typedPub: the picked condition.
  **`K05LawR`**: ∀ the head's letters, AtMgA … → the three flat lists' heads → the listed seats are there → K5Along (K5Along.lean) at R1 ‹the seated description› → KindTiedR ‹AtMg.Kind's letters› at R1 … .K5.
  `K05LawRBare`: the like at bare RchAt: its end IS h.Kind h.𝔇 𝔏 .K5. (Neither sentence gives the other: the premise turns with the condition. A proof that is general in the condition gives both.)
  `k05_of_places`, `k05_to_places`: the end is twelve ties (K05KindR.lean). `ex_k5`: at the twelve numbers the table's extractor lays nothing. `hands_R1`: at R1 an accepting run of any piece hands the condition on
    (rchPub_hand, Johnson/Top/H0/Walk/ReachPub.lean; P5J.AtMg.ofDesc, Johnson/P5J/RowsAtMg.lean): so HandsOn is no premise. (The lemma k5Along_of_fold stands in Door/Law/K5AlongAt.lean; the import and the opened name are for the files above that open it.)
Can it be met at all? (1) A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/) (its named tests have been evaluated true at the release's own three public files). (2) Of K5Along at R1: bare · left are typed over theorems along the fold in other files;
the five are "statements alone" in their own files.
(Where this and lean/THEOREM.md differ, the page holds.)

(3) R1 admits only what an accepting fold of the description's own sub-protocols reaches from a typed instance's start.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.RowsAtMg
import Johnson.P5J.MgAtAll
import Johnson.P5J.AtMgR
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Desc.First.Att.Door.Law.K05KindR
import Johnson.Desc.First.Att.Door.Law.K5Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub rchPub_hand)
open P5J (AtMg AtMgA AtMgR mgAtAll F0T TS Free fullLinks)

/-- The public part is a typed instance's. -/
def typedPub (p : ProofFile.InstPub) : Prop := ∃ z, p = (LPFD.Full.instanceAsPlainRecord z).pub

/-- **THE KIND's LAW IN THE COUNTED FORM, AT THE PICKED CONDITION.** -/
def K05LawR : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (_ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (L : Laid) (_ : P5J.At.laid? Zp = some L)
    (_ : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent),
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) KindName.K5

/-- The like at bare "reached": its end is P5J.AtMg.Kind (Johnson/P5J/RowsAtMg.lean). -/
def K05LawRBare : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (_ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (L : Laid) (_ : P5J.At.laid? Zp = some L)
    (_ : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) L
      (P5J.At.d12 Zp L).M h.𝔇.sent),
    h.toAtMg.Kind h.𝔇 𝔏 KindName.K5

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (Rch : ℕ → (ProofFile.InstPub × TS) × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str → Prop)

/-- **The end is twelve ties**: at any condition. -/
theorem k05_of_places
    (H : ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q →
      TiedAtR (P5J.At.N Zp cF) (mgAtAll h) LFullK PFullK (fun a => a) Rch (14 * (2 * g + 1) + 4)
        (q.withMap (h.toAtMg.ex 𝔏 (14 * (2 * g + 1) + 4)))) :
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps Rch (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) KindName.K5 :=
  kindTiedR_of_places _ _ Rch _ _ H

theorem k05_to_places
    (H : KindTiedR (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps Rch (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) KindName.K5) :
    ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q →
      TiedAtR (P5J.At.N Zp cF) (mgAtAll h) LFullK PFullK (fun a => a) Rch (14 * (2 * g + 1) + 4)
        (q.withMap (h.toAtMg.ex 𝔏 (14 * (2 * g + 1) + 4))) :=
  kindTiedR_to_places _ _ Rch _ _ H

omit Rch in
/-- At the kind's twelve numbers the table's extractor lays nothing. -/
theorem ex_k5 {g : ℕ} (hg : g < 12) (u v) (w : Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT) :
    h.toAtMg.ex 𝔏 (14 * (2 * g + 1) + 4) u v w = w := by
  have hp : P5J.At.ps[14 * (2 * g + 1) + 4]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := k5_at_full g hg
  unfold P5J.AtMg.ex P5J.exF
  exact extQAt_k5 _ _ _ _ _ _ _ _ _ _ _ _ _ hp rfl u v w

omit Rch in
/-- **At the picked condition every piece hands it on.** -/
theorem hands_R1 (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ) (q) (hq : (h.toAtMg.row 𝔏)[k]? = some q) :
    HandsOn (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) k q :=
  fun _ _ _ hr hb => rchPub_hand (h.toAtMg.ofDesc 𝔏 q₁ q₂ q₃) hq hb hr

end

end H2K5.Door

#print axioms H2K5.Door.k05_of_places
#print axioms H2K5.Door.k05_to_places
#print axioms H2K5.Door.ex_k5
#print axioms H2K5.Door.hands_R1
