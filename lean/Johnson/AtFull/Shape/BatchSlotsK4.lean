-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlotsK4.lean: THE SLOTS OF K4's TWO RUNS OF CLAIMS, "front" AND "back", AT
THE TWELVE LAYERS' LINKS OF THE PROOF FILE's OWN FIRST CHAIN (Slot,
Johnson/Desc/First/Batch/Shape/BatchBuild.lean), under the head at which the library's laws on that
chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). A joining of laws; nothing is evaluated.

  `seatRun_same`, `seatRun_still`: a run of K4's at the state keeps the reply, and leaves the
    statement, where it returns (it lays the link's own part and the count of rows alone).
  **`k4_slots`** (g < 12): Bs by baseOf's value · Lk by cF.links[2 g]?: there are slots for the
    pairs (2, "front") and (2, "back") of Lk.hear whose laws' runG ARE
    fun _ a => k4RunG (frontG Bs.G₀.W.layers g) a and
    fun _ a => k4RunG (backG Bs.G₀.W.layers.y Bs.G₀.W.layers.sc) a, and whose pre IS, at both,
    fun _ s => PlanEnv Bs.G₀.W.layers s (Johnson/Desc/First/K4/Returns/RunShape.lean). Each slot's
    bare run is named too.

Limits. TWO OF THE FIFTEEN RUNS BY KIND AND NAME (24 of the 215 runs). A slot pays nothing of its
law's pre. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchBuild
import Johnson.Desc.First.K4.Returns.RunShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open OnBytes.Desc.First.K4 (blockAtC setPart part? formsBack)
open OnBytes.Desc.First.K4.Rt (seatRun k4RunG frontG backG PlanEnv frontRunLaw backRunLaw
  claims_are)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem seatRun_same (name : String) (f : Layer.Own → Fork → Option (Array Aff × Fork))
    (s s' : S) (cs : List Claim) (h : seatRun name f s = .ok (cs, s')) :
    ProofFile.sameReply s s' = true := by
  unfold seatRun at h
  cases hq : VerifiableInference.Desc.named "the part is not there" (part? s) with
  | error e => rw [hq] at h; exact nomatch h
  | ok q =>
    rw [hq] at h
    cases hr : OnBytes.Desc.First.K4.runOf OnBytes.Desc.First.K4.seatOwn name f q with
    | error e =>
      have h' : (((Except.error e : Except String (List Aff × OnBytes.Desc.First.K4.Part)).map
        fun y => (y.1, setPart s y.2)).map fun y =>
          (y.1.map OnBytes.Desc.First.K4.claimOf, y.2)) = .ok (cs, s') := by
        rw [← hr]
        exact h
      exact nomatch h'
    | ok y =>
      have h' : (((Except.ok y : Except String (List Aff × OnBytes.Desc.First.K4.Part)).map
        fun y => (y.1, setPart s y.2)).map fun y =>
          (y.1.map OnBytes.Desc.First.K4.claimOf, y.2)) = .ok (cs, s') := by
        rw [← hr]
        exact h
      have e : (y.1.map OnBytes.Desc.First.K4.claimOf, setPart s y.2) = (cs, s') :=
        Except.ok.inj h'
      rw [← (Prod.mk.inj e).2]
      unfold ProofFile.sameReply
      exact beq_self_eq_true _

theorem seatRun_still (name : String) (f : Layer.Own → Fork → Option (Array Aff × Fork))
    (s s' : S) (cs : List Claim) (h : seatRun name f s = .ok (cs, s')) : s'.st = s.st := by
  unfold seatRun at h
  cases hq : VerifiableInference.Desc.named "the part is not there" (part? s) with
  | error e => rw [hq] at h; exact nomatch h
  | ok q =>
    rw [hq] at h
    cases hr : OnBytes.Desc.First.K4.runOf OnBytes.Desc.First.K4.seatOwn name f q with
    | error e =>
      have h' : (((Except.error e : Except String (List Aff × OnBytes.Desc.First.K4.Part)).map
        fun y => (y.1, setPart s y.2)).map fun y =>
          (y.1.map OnBytes.Desc.First.K4.claimOf, y.2)) = .ok (cs, s') := by
        rw [← hr]
        exact h
      exact nomatch h'
    | ok y =>
      have h' : (((Except.ok y : Except String (List Aff × OnBytes.Desc.First.K4.Part)).map
        fun y => (y.1, setPart s y.2)).map fun y =>
          (y.1.map OnBytes.Desc.First.K4.claimOf, y.2)) = .ok (cs, s') := by
        rw [← hr]
        exact h
      have e : (y.1.map OnBytes.Desc.First.K4.claimOf, setPart s y.2) = (cs, s') :=
        Except.ok.inj h'
      rw [← (Prod.mk.inj e).2]
      rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k4_slots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[2 * g]? = some Lk ∧
      (∃ T : Slot ProofFile.sameReply Lk.hear (2, "front"),
        T.bare = (fun _ s => seatRun "K4.claims-front"
          (OnBytes.Desc.First.K4.formsFrontNoRows Bs.G₀.W.layers g) s) ∧
        T.law.runG = (fun _ a => k4RunG (frontG Bs.G₀.W.layers g) a) ∧
        T.law.pre = fun _ s => PlanEnv Bs.G₀.W.layers s) ∧
      ∃ T : Slot ProofFile.sameReply Lk.hear (2, "back"),
        T.bare = (fun _ s => seatRun "K4.claims-back" formsBack s) ∧
        T.law.runG = (fun _ a => k4RunG (backG Bs.G₀.W.layers.y Bs.G₀.W.layers.sc) a) ∧
        T.law.pre = fun _ s => PlanEnv Bs.G₀.W.layers s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, -, hla, -, hgg, hP, -, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have h4 : Lk.hear[2]? = some (IM.seatedAs ProofFile.sameReply (ProofFile.k4Block y) b.name (IM.k4Place g)) :=
    e2.trans (congrArg some hla)
  have hc : (ProofFile.k4Block y).claims = (blockAtC { y.2 with k3Runs := true }).claims := rfl
  refine ⟨Bs, Lk, O.made, e1, ⟨
    { lot := ProofFile.k4Block y, name := b.name, place := IM.k4Place g, seated := h4
      bare := fun _ s => seatRun "K4.claims-front"
        (OnBytes.Desc.First.K4.formsFrontNoRows y.2.P y.2.g) s
      states := rfl
      law := frontRunLaw { y.2 with k3Runs := true } _ rfl (by
        rw [claims_are]
        exact List.mem_cons_self)
      keeps := fun n s s' cs hr => seatRun_same _ _ s s' cs hr
      still := fun n s s' cs hr => seatRun_still _ _ s s' cs hr }, ?_, ?_, ?_⟩, ⟨
    { lot := ProofFile.k4Block y, name := b.name, place := IM.k4Place g, seated := h4
      bare := fun _ s => seatRun "K4.claims-back" formsBack s
      states := rfl
      law := backRunLaw { y.2 with k3Runs := true } _ (by
        rw [claims_are]
        exact List.mem_cons_of_mem _ List.mem_cons_self)
      keeps := fun n s s' cs hr => seatRun_same _ _ s s' cs hr
      still := fun n s s' cs hr => seatRun_still _ _ s s' cs hr }, ?_, ?_, ?_⟩⟩
  · show (fun _ s => seatRun "K4.claims-front"
      (OnBytes.Desc.First.K4.formsFrontNoRows y.2.P y.2.g) s) = _
    rw [hP, hgg]
  · show (fun _ a => k4RunG (frontG y.2.P y.2.g) a) = _
    rw [hP, hgg]
  · show (fun _ s => PlanEnv y.2.P s) = _
    rw [hP]
  · rfl
  · show (fun _ a => k4RunG (backG y.2.P.y y.2.P.sc) a) = _
    rw [hP]
  · show (fun _ s => PlanEnv y.2.P s) = _
    rw [hP]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.seatRun_same
#print axioms Johnson.AtFull.Shape.seatRun_still
#print axioms Johnson.AtFull.Shape.k4_slots
