-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/HtinAtConstant.lean: THE FIELD htin OF THE LINK's LIST (`TableOwes.htin`'s type) AT
THE CLOSED CONSTANT's LETTERS, AT EACH OF THE 25 LINKS, AT THE SECOND HASH FUNCTION: `htin_paid`
(Johnson/Desc/First/Link/Law/HtinPaid.lean) called once, its premise on the condition paid off the
table's own promise. Theorems; three by the kernel. No text already in the library turns.

  `links_written`, `places_written`: the constant's list of sorts and of places are the
    written ones IM.linksW, IM.placesW. `batch_nAt`: the table's number of link m's batching is
    14 m + nAt m + 2. `behindPlaceB_W`: the place behind it bears the link m and the piece
    «hearing + 2». By the kernel.
  `planB_blank`: the test `linkPlanB` reads nothing of a built link's routine.
  `htin_at_const`: **h : AtMgA secondHashFunction Z D r Zp Np cF x · m < 25 · h.𝔇.lk m = some L · linkPlanB Zp
    m X = true at the built link X · «reached» gives Reach at the border behind the batching · the
    open ledger of a state reached there has a coefficient for each slot ⊢ ∀ a t, onTR h.𝔇.N
    (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s => (z, s)) Rz (k + 1) a → MovesYes atS
    ((moves₂ L).map (·.move)) a.1 t [] → K9.totalIn (h.𝔇.N.group m) t = true**, k := batchAt
    fullLinks At.ps m; general in α, the frame and Rz. PAID INSIDE: ledgerB
    (`ledger_of_promise`) · membersHeld (`onT_bools`) · N.groupAt m = m (by definition) · the opened
    seat (`h.laid.opened`) · the link (`sits_at_constant`).
Limits. LEFT BY NAME: linkPlanB at the 25 built links (true at the full-size files by an evaluation:
no theorem) · hRz (at the constant: list_rchIs) · hLS (lsSize_of_slots
with slots_at_reached, under its HeadSpots). No member. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HtinPaid
import Johnson.Desc.First.Link.Law.LedgerAsked
import Johnson.LPFK9R.SitsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Link Place)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.JoinAtBlocks
open VerifiableInference.Desc.LinkJoin
open Meaning.K2 (blank_built)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (linksW placesW nAt openAt)
open P5J (AtMg AtMgA F0T fullLinks)
open ProofFile (Cl)

theorem links_written : fullLinks = linksW := by decide

theorem places_written : P5J.At.ps = placesW := by
  unfold P5J.At.ps IM.placesW
  rw [links_written]

set_option maxRecDepth 1000000 in
theorem batch_nAt : ∀ m < 25, batchAt fullLinks P5J.At.ps m = 14 * m + nAt m + 2 := by
  decide +kernel

/-- The place behind the batching's bears the link and the piece «hearing + 2». -/
def behindPlaceB : Bool :=
  (List.range 25).all fun m =>
    match P5J.At.ps[14 * m + nAt m + 3]? with
    | some p => p.link == some m && p.piece == hearN fullLinks m + 2
    | none => false

set_option maxRecDepth 1000000 in
theorem behindPlaceB_W : behindPlaceB = true := by decide +kernel

theorem behind_place {m : ℕ} (hm : m < 25) : ∃ p, P5J.At.ps[14 * m + nAt m + 3]? = some p ∧
    p.link = some m ∧ p.piece = hearN fullLinks m + 2 := by
  have h := List.all_eq_true.1 behindPlaceB_W m (List.mem_range.2 hm)
  cases e : P5J.At.ps[14 * m + nAt m + 3]? with
  | none =>
    rw [e] at h
    exact nomatch h
  | some p =>
    rw [e] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨p, rfl, h.1, h.2⟩

/-- The test reads nothing of a built link's routine. -/
theorem planB_blank {Zp : ProofFile.Pub} {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Zp = some G) {m : ℕ} {Xl : LinkH} (e3 : G.built[m]? = some Xl)
    (hP : ∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) :
    linkPlanB Zp m Xl = true := by
  obtain ⟨links, e⟩ := blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : m < Zp.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact hP (Zp.p.built.links[m]'hl1) (Array.getElem?_eq_getElem hl1)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **htin AT THE CLOSED CONSTANT's LETTERS.** -/
theorem htin_at_const {α : Type} {Fr : Frame} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ}
    (hm : m < 25) {L : Link S Cl} (hlk : h.𝔇.lk m = some L)
    (hP : ∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) (z : ProofFile.InstPub)
    (Rz : ℕ → S × Fr.E.Str → Prop)
    (hRz : ∀ a, Rz (batchAt fullLinks P5J.At.ps m + 1) a →
      Reach 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder (F0T OnBytes.secondHashFunction Zp Np cF).start₁
        (batchAt fullLinks P5J.At.ps m + 1) (z, a.1))
    (hLS : ∀ s, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m + 1) (z, s) →
      ∀ G, s.fork? = some G → G.LS.size = G.ns) :
    ∀ a t, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks P5J.At.ps (fun s : S => (z, s)) Rz
        (batchAt fullLinks P5J.At.ps m + 1) a →
      MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      VerifiableInference.Desc.K9.totalIn (h.𝔇.N.group m) t = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L', p, Q, hlk', _, _, hs⟩ := sits_at_constant h.toAtMg m hm
  obtain rfl : L = L' := Option.some.inj (hlk.symm.trans hlk')
  obtain ⟨_, Xl, _, e3, _⟩ := TocK8.k08_scope h.scope h.reads O m hm
  have hx : (m, (if m = 24 then 5 else 4), (if m = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩
  have hb := border_eq hx
  have hk := batch_nAt m hm
  obtain ⟨p', hp', hl', hpc'⟩ := behind_place hm
  refine htin_paid h.scope h.reads O hx hs.link e3
    (linkPlanFits_of_B (planB_blank O.blank e3 hP)) h.𝔇.N rfl z _ fun a ha => ?_
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (batchAt fullLinks P5J.At.ps m + 1) (z, a.1) :=
    hRz a ha.2
  refine ⟨by rw [hb, ← show batchAt fullLinks P5J.At.ps m + 1 = 14 * m + nAt m + 3 by omega]
             exact hr, ?_, hLS a.1 hr, ?_⟩
  · exact ledger_of_promise h.𝔇 h.𝔇.N fullLinks P5J.At.ps z _ m 2 p' ledFit_full
      (by rw [show batchAt fullLinks P5J.At.ps m + 1 = 14 * m + nAt m + 3 by omega]; exact hp')
      hl' hpc' (Or.inr rfl) a ha.1
  · have hmem := (onT_bools h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks P5J.At.ps z _ a ha.1).2.2.1
    rw [show batchAt fullLinks P5J.At.ps m + 1 = 14 * m + nAt m + 3 by omega, links_written,
      places_written] at hmem
    exact hmem

end LPFK9

#print axioms LPFK9.links_written
#print axioms LPFK9.batch_nAt
#print axioms LPFK9.behindPlaceB_W
#print axioms LPFK9.planB_blank
#print axioms LPFK9.htin_at_const
