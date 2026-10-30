-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/ShapesAtCut.lean: AT THE CUTS OF THE REAL CHAIN's FOLD IN FRONT OF THE CLOSING OF A LINK l, 1 ≤ l < 24: THE LINK's GROUP HAS THE JOINERS' FLAGS; AND, WITH THE MESSAGES' SHAPES, ShapesAre: SO THE THIRD AND THE FOURTH PREMISE OF k10_public_full (Johnson/Desc/First/Close/Law/PublicFull.lean [not in this library]), IN THAT THEOREM's OWN FORM. Statements and proofs.
  flags_at_cut       InScope P · readFiles P = .ok pp · IM.Open … · hsh : Z.first.shape = shapeFull · 1 ≤ l < 24 · n ≤ 4 · a fold of the first 14 l + 8 + n sub-protocols from ProofFile.startS Z p returns t: there are L, G: t.link? = some L · L.link = l · L.check.frame.group = l · t.st.groups[l]? = some G · G's members: no number twice ·
                     G.kept.toList = (joinersAt shapeFull l).map (·.2). (n = 4: in front of K10.)
  shapesAre_at_cut   the same, with hs: "the shapes of G's members, in order, are the joiners'": ShapesAre t.st G ‹the l-th written list› ‹the flags› (noOf ‹the list› G.members.toList), and that numbering parts the list's members.
  public_premises_at_cut   the same: there is a numbering no with: (∀ G, t.st.groups[l]? = some G → ShapesAre t.st G ‹the list› ‹the flags› no) and "no parts the list's members": k10_public_full's third and fourth premise at T := t.st, g := l, to the letter. (Its first two, InOrder T and T.codes = codesFull2, are not treated here.)
BY: flags_at (Johnson/IMR/FlagsAt.lean) · flags_join_full (Johnson/Desc/First/Close/Law/FlagsJoin.lean): THAT flags_at's RIGHT SIDE IS flagsBy AT THE PLAN's TARGET AND FRAME IS LEAN's WORD (rfl · rfl) · shapesAre_full (Johnson/Desc/First/Close/Law/ShapesOfIds.lean).
LIMITS. **hsh AND hs ARE PREMISES.** hsh: what the pin (P1) compares; not laid. hs: the fourth sentence: the field FoldFacts.msgShapes (not paid) with a closed fact on the written sendings (not typed). Link 0, the head's link and the last group: not treated. That a fold returns is shown of no proof here.
Nothing on the witness's side of K10's law. No soundness statement.

-/
import Johnson.IMR.FlagsAt
import Johnson.Desc.First.Close.Law.FlagsJoin
import Johnson.Desc.First.Close.Law.ShapesOfIds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK10

open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (ShapesAre joinersAt kbAt noOf membersOf flagsBy
  flags_join_full shapesAre_full)
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE GROUP's FLAGS AT THE CUTS IN FRONT OF THE CLOSING ARE THE JOINERS'**, where the first chain's shape is the written one. -/
theorem flags_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : ℕ} (hn : n ≤ 4) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : OnBytes.Model.LinkCtx) (G : Group), t.link? = some L ∧ L.link = l ∧
      L.check.frame.group = l ∧ t.st.groups[l]? = some G ∧ G.members.toList.Nodup ∧
      G.kept.toList = (joinersAt shapeFull l).map (·.2) := by
  obtain ⟨L, G, n₀, a1, a2, a3, a4, -, a6, a7⟩ := Meaning.K2.flags_at hS hR O h1 h24 hn g
  refine ⟨L, G, a1, a2, a3, a4, a6, ?_⟩
  rw [a7, hsh]
  exact flags_join_full (f := VerifiableInference.Desc.First.K2.frameAtLink shapeFull l) h1
    (by omega) rfl rfl

/-- **ShapesAre AT A REACHED CUT IN FRONT OF THE CLOSING**, from the written shape and the messages' shapes. -/
theorem shapesAre_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : ℕ} (hn : n ≤ 4) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (hs : ∀ G, t.st.groups[l]? = some G →
      G.members.toList.map (fun o => (t.st.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) =
        (joinersAt shapeFull l).map fun x => some x.1) :
    ∃ (L : OnBytes.Model.LinkCtx) (G : Group), t.link? = some L ∧ L.check.frame.group = l ∧
      t.st.groups[l]? = some G ∧
      ShapesAre t.st G (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))
        (noOf (linksFullLit.getD l []) G.members.toList) ∧
      ∀ i ∈ membersOf (linksFullLit.getD l []), ∀ j ∈ membersOf (linksFullLit.getD l []),
        noOf (linksFullLit.getD l []) G.members.toList i =
          noOf (linksFullLit.getD l []) G.members.toList j → i = j := by
  obtain ⟨L, G, a1, -, a3, a4, a5, a6⟩ := flags_at_cut hS hR O hsh h1 h24 hn g
  obtain ⟨b1, b2⟩ := shapesAre_full (T := t.st) (G := G) (l := l) (by omega) rfl a5 a6 (hs G a4)
  exact ⟨L, G, a1, a3, a4, b1, b2⟩

/-- **k10_public_full's THIRD AND FOURTH PREMISE, IN ITS OWN FORM, AT SUCH A CUT.** -/
theorem public_premises_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : ℕ} (hn : n ≤ 4) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (hs : ∀ G, t.st.groups[l]? = some G →
      G.members.toList.map (fun o => (t.st.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) =
        (joinersAt shapeFull l).map fun x => some x.1) :
    ∃ no : Fin (linksFullLit.getD l []).length → ℕ,
      (∀ G, t.st.groups[l]? = some G → ShapesAre t.st G (linksFullLit.getD l [])
        (kbAt shapeFull l (linksFullLit.getD l [])) no) ∧
      ∀ i ∈ membersOf (linksFullLit.getD l []), ∀ j ∈ membersOf (linksFullLit.getD l []),
        no i = no j → i = j := by
  obtain ⟨-, G, -, -, a3, a4, a5⟩ := shapesAre_at_cut hS hR O hsh h1 h24 hn g hs
  refine ⟨_, fun G' hG' => ?_, a5⟩
  obtain rfl : G = G' := Option.some.inj (a3.symm.trans hG')
  exact a4

end LPFK10

#print axioms LPFK10.public_premises_at_cut
#print axioms LPFK10.flags_at_cut
#print axioms LPFK10.shapesAre_at_cut
