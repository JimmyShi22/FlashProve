-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedCutKeeps.lean: an argument string whose openings stand at listed
places alone is not changed by the cut to the lists (OnBytes/TypedOracleCompiler/Compile/Batch/ListedCut.lean): so
there the verifier on the cut string is the compiled verifier at the string itself.

No soundness: a test. This module states nothing on soundness.

Why. verifyBSC_eq (OnBytes/TypedOracleCompiler/Compile/Batch/ListedCutLaws.lean) says of every string π and all
lists that verifyBSC judges π.cutTo. Whoever lays a string and makes the lists of the same tables
wants to know that the string judged is the one laid: the honest string loses nothing.

Main names.
  SeatsOK: in every round, every position has a tree of its component within the list of depths, and
    stands at its own tree and leaf. seatsOK_of_okg: a well-formed wiring has it (WireRB.OKG,
    OnBytes/TypedOracleCompiler/Iop/BatchWire.lean: place_lt0, place_ltJ, posAt0_place, posAtJ_place): for a
    wiring at a letter; at a whole file's rounds SeatsOK is shown outright
    (OnBytes/Maker/ListedWholePlaces.lean).
  cutS_of_listedOK: under SeatsOK and ListedOK, cutS s A W own f = f.
  cutTo_ext_of_listed, cutTo_of_listed: under these and hE (an external opening stands at listed
    positions alone), π.cutTo sh wl own listed = π.
  verifyBSC_eq_self: under PlacesOK, SeatsOK and the five premises of verifyBSL_eq, verifyBSC at π
    is verifyOneProtocol at π.

Why SeatsOK. ListedOK speaks of positions through posAt0 and posAtJ alone, at trees within the list
of depths: of a position that stood at no such leaf it would say nothing, and the cut could strike
an opening there.

Limits. The premises are shown of no wiring, no string and no lists here. verifyBSC_eq_self says of
verifyBSC no more than verifyBSL_eq says of verifyBSL: it is here so that one function serves both
uses. Nothing on time or memory. Nothing on soundness. The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedCutLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Every position has a tree of its component within the list of depths, and stands at its own tree
and leaf. -/
def SeatsOK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | r :: s, (a, A), (w, W) =>
    (∀ p : r.Pos, a.own p = false →
      w.tree p < w.depth0.length ∧ w.posAt0 (w.tree p) (w.place p) = some p) ∧
    (∀ p : r.Pos, a.own p = true →
      w.tree p < w.depthJ.length ∧ w.posAtJ (w.tree p) (w.place p) = some p) ∧
    SeatsOK s A W

/-- A number at which a list has a member is below the list's length. -/
theorem seat_lt {l : List ℕ} {k : ℕ} {P : ℕ → Prop} (h : ∃ d, l[k]? = some d ∧ P d) :
    k < l.length := by
  obtain ⟨d, hd, _⟩ := h
  obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.1 hd
  exact hk

/-- A well-formed wiring has it. -/
theorem seatsOK_of_okg :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W → SeatsOK s A W
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), h =>
    ⟨fun p ho => ⟨seat_lt (h.1.place_lt0 p ho), h.1.posAt0_place p ho⟩,
      fun p ho => ⟨seat_lt (h.1.place_ltJ p ho), h.1.posAtJ_place p ho⟩,
      seatsOK_of_okg s A W h.2⟩

/-- **Openings that stand at listed leaves alone are not changed by the cut.** -/
theorem cutS_of_listedOK :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))) (own : Leaves),
      SeatsOK s A W → ListedOK s A W f own → cutS s A W own f = f
  | [], _, _, _, _, _, _ => funext fun p => nomatch p
  | r :: s, (a, A), (w, W), f, own, hW, h => by
    funext p
    rcases p with q | q
    · rw [cutS_inl]
      by_cases hf : f (.inl q) = none
      · rw [hf]
        exact ite_self _
      · refine if_pos ?_
        cases ho : a.own q with
        | false =>
          rw [keptR_shared w _ q ho]
          exact List.elem_eq_true_of_mem
            (h.1 (w.tree q) (hW.1 q ho).1 (w.place q) q (hW.1 q ho).2 hf)
        | true =>
          rw [keptR_own w _ q ho]
          exact List.elem_eq_true_of_mem
            (h.2.1 (w.tree q) (hW.2.1 q ho).1 (w.place q) q (hW.2.1 q ho).2 hf)
    · rw [cutS_inr]
      exact congrFun (cutS_of_listedOK s A W (fun z => f (.inr z)) own.tail hW.2.2 h.2.2) q

section
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- The cut string's field ext, where the string's external openings stand at listed positions
alone. -/
theorem cutTo_ext_of_listed (π : OneProtocolProof lam Q) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann)
    (wl : WireELess E) (own : Leaves) (listed : List E.Pos)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) : (π.cutTo sh wl own listed).ext = π.ext := by
  letI := wl.dec
  funext p
  show (if listed.contains p = true then π.ext p else none) = π.ext p
  by_cases hg : π.ext p = none
  · rw [hg]
    exact ite_self _
  · exact if_pos (List.elem_eq_true_of_mem (hE p hg))

/-- **A string whose openings stand at listed places alone is not changed by the cut.** -/
theorem cutTo_of_listed (π : OneProtocolProof lam Q) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E)
    (own : Leaves) (listed : List E.Pos) (hS : SeatsOK Q.loc.shape Q.ann sh)
    (hO : ListedOK Q.loc.shape Q.ann sh π.opens own) (hE : ∀ p, π.ext p ≠ none → p ∈ listed) :
    π.cutTo sh wl own listed = π := by
  have e1 : (π.cutTo sh wl own listed).opens = π.opens :=
    (cutTo_opens π sh wl own listed).trans (cutS_of_listedOK Q.loc.shape Q.ann sh π.opens own hS hO)
  have e2 := cutTo_ext_of_listed π sh wl own listed hE
  cases π with
  | mk salt roots plains opens ext rtreq slot path rsalt =>
    exact congrArg₂
      (fun o e => (⟨salt, roots, plains, o, e, rtreq, slot, path, rsalt⟩ : OneProtocolProof lam Q)) e1 e2

end

/-- **There the verifier on the cut string is the compiled verifier at the string itself.** -/
theorem verifyBSC_eq_self {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (sMT sFS : ℕ) (depthReq : ℕ) (x : Y)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (t : Tag)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos)
    (hW : PlacesOK Q.loc.shape Q.ann wq.sh) (hS : SeatsOK Q.loc.shape Q.ann wq.sh)
    (hA : ∀ p, p ∈ wq.ext.all)
    (hR : ∀ ρ pl, LeavesOK Q.loc.shape Q.ann wq.sh (isReadOf Q wq x ρ pl) (mkRd x ρ pl))
    (hRE : ∀ ρ, mkRdE x ρ = wq.ext.all.filter (isReadEOf Q wq x ρ))
    (π : OneProtocolProof lam Q) (own : Leaves) (listed : List E.Pos)
    (hO : ListedOK Q.loc.shape Q.ann wq.sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) :
    verifyBSC sMT sFS t Q wq.sh wq.ext.less wq.nOpen wq.maxDepth embS embP xin embE depthReq cms
        x π own listed mkRd mkRdE =
      verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  rw [verifyBSC_eq Q wq sMT sFS depthReq x embS embE cms t embP xin mkRd mkRdE hW hA hR hRE π own
    listed, cutTo_of_listed π wq.sh wq.ext.less own listed hS hO hE]

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.seatsOK_of_okg
#print axioms TypedOracleCompiler.Compile.Batch.cutS_of_listedOK
#print axioms TypedOracleCompiler.Compile.Batch.cutTo_ext_of_listed
#print axioms TypedOracleCompiler.Compile.Batch.cutTo_of_listed
#print axioms TypedOracleCompiler.Compile.Batch.verifyBSC_eq_self
