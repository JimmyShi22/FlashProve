-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AlongAt.lean: kind K5 (an attention segment's own rounds): TWO OF THE SEVEN FACTS THAT THE KIND's ROAD SPENDS "FROM REACHED" (K5Along.lean: bare · left), PAID AT THE SEATED DESCRIPTION's OWN TERM, UNDER THE ONE HEAD.
So K5Along at the picked condition hangs on the facts at the fold (Johnson/Desc/First/FoldFacts.lean, through Johnson/P5J/AtMgR.lean) alone.
Over AtMgR (Johnson/P5J/AtMgR.lean) (the public numbers of the facts at the fold are a closed term, At.foldD Zp cF L, Johnson/P5J/FoldAt.lean; no letter d, no equations): the lemma k5Along_of_fold stands here; k5Along_bare | k5Along_R1 take L inside AtMgR.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

Typed by reading Look/K03ReachedAt.lean · Door/Law/K05LawR.lean · K5Along.lean · P5J/AtMg.lean ·
LaidOpens.lean · AtMgR.lean · FoldAt.lean · First/FoldFacts.lean · AtTerm.lean · Desc/Sound/AtDescPure.lean · AtSeat.lean · Top/H0/Walk/ReachAt.lean · ReachPub.lean.

Why. The payers (reached_rowsBare · reached_leftAt) stand at the description WRITTEN OUT (ProofFile.fileDescBy … Z A B (fun s => s) (ProofFile.startS Z) c) under: in scope · the files are read · an opening of the maker at that term · the description's own test on the plan.
The kind's law (K05LawR) stands at another file's name for the same term, F0T o Zp Np cF (Johnson/P5J/AtTerm.lean: three abbreviations over ProofFile.fileDescBy), under the head AtMgA. The head holds all four: scope · reads · laid.opened · laid.planOk.

Main names:
  `bare_at`, `left_at`: K5Along's fields bare | left, in their own texts, at RchAt ‹F0T …›, under the smaller head AtMg.
  `k5Along_of_fold`: five of the seven are the fold's own fields at At.foldD Zp cF L, whose L · M · sent are K5Along's letters by unfolding; general in the condition.
  `k5Along_bare`: K5Along at RchAt ‹F0T …› from AtMgR at that condition.
  **`k5Along_R1`**: K05LawR's one premise, to the letter (at RchPub ‹F0T …› typedPub, at AtMgR's own L; K05LawR's "the listed seats are there" is AtMgR's field listed), from AtMgR at that condition.
NOT HERE: the five facts at the fold (seatsCarried · msgShapes · liveShape · liveLayout · codes): they stay fields of FoldFacts inside the premise AtMgR: statements alone in their own files.
Is it empty here? Implications. No state is shown to be reached; a member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). "Reached" is a term in bare_at · left_at · k5Along_bare · k5Along_R1; the public numbers are a closed term. The premise AtMgR holds FoldFacts whole; five of its fields are spent.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawR
import Johnson.Desc.First.Look.K03ReachedAt
import Johnson.P5J.AtMgR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open P5J (AtMg AtMgA AtMgR F0T TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The rows that the lookup on the calls has heard are bare**, at every state reached in front of an attention segment's own sub-protocol, at the seated description. -/
theorem bare_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Str : Type} (g : ℕ) (hg : g < 12) (a : (ProofFile.InstPub × TS) × Str)
    (hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) (14 * (2 * g + 1) + 4) a) :
    ∃ g₁, a.1.2.lookHeard? = some g₁ ∧ ∀ f ∈ g₁.rows.toList, f.ents = #[] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact VerifiableInference.OnPublicFiles.reached_rowsBare (Pf := Z) (lay := Z.lay) (Z := Zp) (Bs := Bs) (base := base) (c := cF)
    (A := _root_.Desc.K14.Law.seatZ Zp Np) (B := _root_.Desc.K14.Law.secondAt Zp Np) h.scope h.reads O h.laid.planOk g hg a hr

/-- **What the lookup on the calls has left fits the fork**, at the same states. -/
theorem left_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Str : Type} (g : ℕ) (hg : g < 12) (a : (ProofFile.InstPub × TS) × Str)
    (hr : RchAt (F0T OnBytes.secondHashFunction Zp Np cF) (14 * (2 * g + 1) + 4) a) :
    ∃ g₁ G, a.1.2.lookHeard? = some g₁ ∧ a.1.2.fork? = some G ∧ FillBare.leftAtB g₁ G = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact VerifiableInference.OnPublicFiles.reached_leftAt (Pf := Z) (lay := Z.lay) (Z := Zp) (Bs := Bs) (base := base) (c := cF)
    (A := _root_.Desc.K14.Law.seatZ Zp Np) (B := _root_.Desc.K14.Law.secondAt Zp Np) h.scope h.reads O h.laid.planOk g hg a hr

variable {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **Five of the seven are the fold's own fields**, under the head with the facts on every reached state: at the closed public numbers At.foldD Zp cF L, whose L · M · sent are K5Along's letters by unfolding. General in the condition. -/
theorem k5Along_of_fold
    (Rch : ℕ → (ProofFile.InstPub × TS) × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str → Prop) {L : Laid}
    (hR : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L)
    (hB : ∀ g, g < 12 → ∀ a, Rch (14 * (2 * g + 1) + 4) a → ∃ g₁, a.1.2.lookHeard? = some g₁ ∧ ∀ f ∈ g₁.rows.toList, f.ents = #[])
    (hL : ∀ g, g < 12 → ∀ a, Rch (14 * (2 * g + 1) + 4) a →
      ∃ g₁ G, a.1.2.lookHeard? = some g₁ ∧ a.1.2.fork? = some G ∧ FillBare.leftAtB g₁ G = true) :
    K5Along Rch L (P5J.At.d12 Zp L).M h.𝔇.sent where
  seats := hR.fold.seatsCarried
  shapes := hR.fold.msgShapes
  liveShape := fun k a hr hm => (hR.fold.liveShape k a hr hm).trans rfl
  liveLayout := fun k a hr hm => (hR.fold.liveLayout k a hr hm).trans rfl
  codes := fun k a hr hm => (hR.fold.codes k a hr hm).trans rfl
  bare := hB
  left := hL

/-- The seven at bare "reached", from the facts at the fold alone. -/
theorem k5Along_bare {L : Laid}
    (hR : AtMgR (X := (ProofFile.InstPub × TS) × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) OnBytes.secondHashFunction Z D r Zp Np cF
      (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) (fun a => a.1) L) :
    K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) L
      (P5J.At.d12 Zp L).M h.𝔇.sent :=
  k5Along_of_fold h _ hR (fun g hg a hr => bare_at h.toAtMg g hg a hr) (fun g hg a hr => left_at h.toAtMg g hg a hr)

/-- **THE KIND's LAW's ONE PREMISE, FROM THE FACTS AT THE FOLD ALONE**, at the picked condition. (The law's "the listed seats are there" at this L is hR.listed.) -/
theorem k5Along_R1 {L : Laid}
    (hR : AtMgR (X := (ProofFile.InstPub × TS) × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str) OnBytes.secondHashFunction Z D r Zp Np cF
      (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) (fun a => a.1) L) :
    K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent :=
  k5Along_of_fold h _ hR (fun g hg a hr => bare_at h.toAtMg g hg a hr.1) (fun g hg a hr => left_at h.toAtMg g hg a hr.1)

end

end H2K5.Door

#print axioms H2K5.Door.bare_at
#print axioms H2K5.Door.left_at
#print axioms H2K5.Door.k5Along_of_fold
#print axioms H2K5.Door.k5Along_bare
#print axioms H2K5.Door.k5Along_R1
