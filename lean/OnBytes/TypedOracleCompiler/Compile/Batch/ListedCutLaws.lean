-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedCutLaws.lean: the verifier along lists on the string cut to the
lists (OnBytes/TypedOracleCompiler/Compile/Batch/ListedCut.lean, verifyBSC) is the compiled verifier of one slot
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol) at the cut string, as a tree of queries, FOR
EVERY ARGUMENT STRING AND EVERY TWO LISTS.

No soundness: a test. This module states nothing on soundness.

verifyBSL_eq (OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifierLaws.lean) has five premises. Two of them
speak of the argument string and the two lists: an opening stands at listed places alone (hO, hE).
At the cut string they hold by the cut. The other three (hA, hR, hRE) speak of the wiring and of
the two functions that say what is read; they name neither the string nor the lists, and stay.

The premises.
  hW: in every round, a position that the wiring lays at a leaf of a tree of a component has that
    component, tree and leaf by the annotation's map own and the wiring's maps tree, place
    (PlacesOK): two of the laws of a
    round's wiring (WireRB.OKG, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean: place_posAt0, place_posAtJ).
  hA, hR, hRE: those of verifyBSL_eq, to the letter.

Main names.
  PlacesOK; placesOK_of_okg: a well-formed wiring has it.
  keptR_shared, keptR_own, cutS_inl, cutS_inr: the definitions, unfolded.
  listedOK_cutS: under PlacesOK the cut openings stand at listed leaves alone (ListedOK).
  cutTo_ext_listed: the cut string's external openings stand at listed positions alone.
  verifyBSC_eq: the equation.
  verifyBSL_cut: the same with verifyBSC unfolded, under the whole law of the rounds' wire records
    (RoundsQueryLayout.OKG) in the place of PlacesOK: a weaker statement, for a caller that has that law at
    hand.

Limits. WHAT IS EQUAL TO verifyOneProtocol IS THE RUN ON THE CUT STRING, NOT ON π. The cut strikes openings:
so a string with an opening at a place that is not read, which verifyOneProtocol refuses by its strict
format, can pass after a cut by lists that leave that place out. A statement on all strings covers
the cut string too; a statement that the verifier refuses just what another program's strict format
refuses does not follow. hW, hA, hR and hRE are shown of no wiring and no functions here. No oracle
functions come in: the two sides are one tree of queries. Nothing on time or memory. Nothing on
soundness. The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedCut
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifierLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A position that the wiring lays at a leaf has that leaf's component, tree and number by the
annotation's map own and the wiring's maps tree and place. -/
def PlacesOK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | r :: s, (a, A), (w, W) =>
    (∀ (k j : ℕ) (p : r.Pos), w.posAt0 k j = some p →
      a.own p = false ∧ w.tree p = k ∧ w.place p = j) ∧
    (∀ (k j : ℕ) (p : r.Pos), w.posAtJ k j = some p →
      a.own p = true ∧ w.tree p = k ∧ w.place p = j) ∧
    PlacesOK s A W

/-- A well-formed wiring has it. -/
theorem placesOK_of_okg :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W → PlacesOK s A W
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), h =>
    ⟨h.1.place_posAt0, h.1.place_posAtJ, placesOK_of_okg s A W h.2⟩

theorem keptR_shared {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (own : List (List ℕ) × List (List ℕ)) (p : r.Pos) (h : a.own p = false) :
    keptR w own p = (own.1.getD (w.tree p) []).contains (w.place p) := by
  unfold keptR
  rw [h, cond_false]

theorem keptR_own {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (own : List (List ℕ) × List (List ℕ)) (p : r.Pos) (h : a.own p = true) :
    keptR w own p = (own.2.getD (w.tree p) []).contains (w.place p) := by
  unfold keptR
  rw [h, cond_true]

theorem cutS_inl {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (own : Leaves)
    (f : (p : OPos (r :: s)) → Option (Opening lam (OSym (r :: s) p))) (p : r.Pos) :
    cutS (r :: s) (a, A) (w, W) own f (.inl p) =
      if keptR w (own.headD ([], [])) p then f (.inl p) else none := rfl

theorem cutS_inr {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (own : Leaves)
    (f : (p : OPos (r :: s)) → Option (Opening lam (OSym (r :: s) p))) (p : OPos s) :
    cutS (r :: s) (a, A) (w, W) own f (.inr p) =
      cutS s A W own.tail (fun q => f (.inr q)) p := rfl

/-- Where the cut leaves an opening, the position's leaf is listed. -/
theorem keptR_of_cutS {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (own : Leaves)
    (f : (p : OPos (r :: s)) → Option (Opening lam (OSym (r :: s) p))) (p : r.Pos)
    (h : cutS (r :: s) (a, A) (w, W) own f (.inl p) ≠ none) :
    keptR w (own.headD ([], [])) p = true := by
  cases hc : keptR w (own.headD ([], [])) p with
  | true => rfl
  | false =>
    refine absurd ?_ h
    rw [cutS_inl, if_neg (by rw [hc]; exact Bool.false_ne_true)]

/-- **The cut openings stand at listed leaves alone.** -/
theorem listedOK_cutS :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))) (own : Leaves),
      PlacesOK s A W → ListedOK s A W (cutS s A W own f) own
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, W), f, own, h => by
    refine ⟨fun k _ j p hp hne => ?_, fun k _ j p hp hne => ?_,
      listedOK_cutS s A W (fun q => f (.inr q)) own.tail h.2.2⟩
    · obtain ⟨ho, ht, hj⟩ := h.1 k j p hp
      have hk := keptR_of_cutS a A w W own f p hne
      rw [keptR_shared w _ p ho, ht, hj] at hk
      exact List.mem_of_elem_eq_true hk
    · obtain ⟨ho, ht, hj⟩ := h.2.1 k j p hp
      have hk := keptR_of_cutS a A w W own f p hne
      rw [keptR_own w _ p ho, ht, hj] at hk
      exact List.mem_of_elem_eq_true hk

section
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- The cut string's field opens. -/
theorem cutTo_opens (π : OneProtocolProof lam Q) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E)
    (own : Leaves) (listed : List E.Pos) :
    (π.cutTo sh wl own listed).opens = cutS Q.loc.shape Q.ann sh own π.opens := rfl

/-- **The cut string's external openings stand at listed positions alone.** -/
theorem cutTo_ext_listed (π : OneProtocolProof lam Q) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann)
    (wl : WireELess E) (own : Leaves) (listed : List E.Pos) :
    ∀ p, (π.cutTo sh wl own listed).ext p ≠ none → p ∈ listed := by
  letI := wl.dec
  intro p hne
  cases hc : listed.contains p with
  | true => exact List.mem_of_elem_eq_true hc
  | false =>
    refine absurd ?_ hne
    show (if listed.contains p = true then π.ext p else none) = none
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]

end

/-- **The verifier along the lists on the cut string is the compiled verifier at the cut string**,
as a tree of queries: for every argument string and every two lists. -/
theorem verifyBSC_eq {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (sMT sFS : ℕ) (depthReq : ℕ) (x : Y)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (t : Tag)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos)
    (hW : PlacesOK Q.loc.shape Q.ann wq.sh) (hA : ∀ p, p ∈ wq.ext.all)
    (hR : ∀ ρ pl, LeavesOK Q.loc.shape Q.ann wq.sh (isReadOf Q wq x ρ pl) (mkRd x ρ pl))
    (hRE : ∀ ρ, mkRdE x ρ = wq.ext.all.filter (isReadEOf Q wq x ρ))
    (π : OneProtocolProof lam Q) (own : Leaves) (listed : List E.Pos) :
    verifyBSC sMT sFS t Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embP xin embE depthReq cms
        x π own listed mkRd mkRdE =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x
        (π.cutTo wq.sh wq.ext.less own listed) :=
  verifyBSL_eq Q wq sMT sFS depthReq x (π.cutTo wq.sh wq.ext.less own listed) own listed embS embE
    cms t embP xin mkRd mkRdE (listedOK_cutS Q.loc.shape Q.ann wq.sh π.opens own hW)
    (cutTo_ext_listed π wq.sh wq.ext.less own listed) hA hR hRE

/-- The same with verifyBSC unfolded, under the whole law of the rounds' wire records. -/
theorem verifyBSL_cut {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (sMT sFS depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves) (listed : List E.Pos)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (t : Tag)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos) (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hA : ∀ p, p ∈ wq.ext.all)
    (hR : ∀ ρ pl, LeavesOK Q.loc.shape Q.ann wq.sh (isReadOf Q wq x ρ pl) (mkRd x ρ pl))
    (hRE : ∀ ρ, mkRdE x ρ = wq.ext.all.filter (isReadEOf Q wq x ρ)) :
    verifyBSL sMT sFS t Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embP xin embE depthReq cms
        x (π.cutTo wq.sh wq.ext.less own listed) own listed mkRd mkRdE =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x
        (π.cutTo wq.sh wq.ext.less own listed) :=
  verifyBSC_eq Q wq sMT sFS depthReq x embS embE cms t embP xin mkRd mkRdE
    (placesOK_of_okg Q.loc.shape Q.ann wq.sh hW) hA hR hRE π own listed

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.verifyBSL_cut
#print axioms TypedOracleCompiler.Compile.Batch.placesOK_of_okg
#print axioms TypedOracleCompiler.Compile.Batch.listedOK_cutS
#print axioms TypedOracleCompiler.Compile.Batch.cutTo_ext_listed
#print axioms TypedOracleCompiler.Compile.Batch.verifyBSC_eq
