-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlots.lean: THE SLOTS OF THE LINKS' RUNS OF CLAIMS AT THE SEAT (Slot,
Johnson/Desc/First/Batch/Shape/BatchBuild.lean), under the head at which the library's laws on the
proof file's own first chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): ONE KIND's HERE: the
smallness test's run "K8.equations", at all 25 links (the other kinds': BatchSlotsK3 … K11.lean). A
joining of laws; nothing is evaluated.

  `atRecord_same`, `atRecord_still`: a run of the smallness test at the record keeps the reply, and
    leaves the statement, where it returns.
  `eqBare`: the bare run that K8.whole p states under "K8.equations", at every p.
  **`k8_slot`** (l < 25): Bs by baseOf's value · Xl by Bs.G₀.built[l]? · Lk by cF.links[l]?: there
    is a slot for the pair (k8No (subAt l), "K8.equations") of Lk.hear whose law's runG IS eqRunG
    and whose pre IS fun _ s => EqPre s (Johnson/Desc/K8/Honest/EqAllRun.lean).

Limits. ONE OF THE FIFTEEN RUNS BY KIND AND NAME (25 of the 215 runs). A slot pays nothing of its
law's pre. The slot's name and place are tied to nothing (as in SeatsNamed.lean's link_named). UNDER
THE HEAD: that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchBuild
import Johnson.Desc.K8.Honest.EqAllRun
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.K8.Honest (eqRunG EqPre eqRunLaw)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)

theorem atRecord_same {α : Type} (f : K8Part → Except String (α × K8Part)) (s s' : S) (a : α)
    (h : VerifiableInference.Desc.First.K8.atRecord f s = .ok (a, s')) :
    ProofFile.sameReply s s' = true := by
  unfold VerifiableInference.Desc.First.K8.atRecord at h
  cases hq : k8PartP.get? s with
  | none => rw [hq] at h; exact nomatch h
  | some q =>
    rw [hq] at h
    dsimp only at h
    cases hf : f q with
    | error e => rw [hf] at h; exact nomatch h
    | ok y =>
      rw [hf] at h
      have e : (y.1, k8PartP.set s y.2) = (a, s') := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      exact sameReply_k8set s y.2

theorem atRecord_still {α : Type} (f : K8Part → Except String (α × K8Part)) (s s' : S) (a : α)
    (h : VerifiableInference.Desc.First.K8.atRecord f s = .ok (a, s')) : s'.st = s.st := by
  unfold VerifiableInference.Desc.First.K8.atRecord at h
  cases hq : k8PartP.get? s with
  | none => rw [hq] at h; exact nomatch h
  | some q =>
    rw [hq] at h
    dsimp only at h
    cases hf : f q with
    | error e => rw [hf] at h; exact nomatch h
    | ok y =>
      rw [hf] at h
      have e : (y.1, k8PartP.set s y.2) = (a, s') := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      have e2 : k8PartP.set s y.2 = (s.putTl y.2.tl).putFork y.2.F := rfl
      rw [e2, VerifiableInference.Desc.First.Shape.putFork_st]
      unfold S.putTl
      split
      · rfl
      · rfl
      · split <;> rfl
      · rfl

/-- The bare run that the smallness test's sub-protocol states under "K8.equations". -/
def eqBare : VerifiableInference.Desc.K9.Shape.Run := fun front =>
  VerifiableInference.Desc.First.K8.atRecord fun p =>
    (equations (p.F.nClaim + front) p.tl p.funs p.F).map fun x =>
      (x.2.2, { p with tl := x.1, F := x.2.1 })

theorem eqBare_states (p : VerifiableInference.Desc.First.K8.ParW) :
    (VerifiableInference.Desc.First.K8.whole p).claims.lookup "K8.equations" = some eqBare := rfl

theorem eqBare_mem (p : VerifiableInference.Desc.First.K8.ParW) :
    ("K8.equations", eqBare) ∈ (VerifiableInference.Desc.First.K8.whole p).claims :=
  List.mem_cons_self

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k8_slot (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (Lk : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.built[l]? = some Xl ∧
      cF.links[l]? = some Lk ∧
      ∃ T : Slot ProofFile.sameReply Lk.hear (k8No (subAt l), "K8.equations"),
        T.lot = VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Zp Bs.G₀ Xl l) ∧
        T.bare = eqBare ∧ T.law.runG = eqRunG ∧ T.law.pre = fun _ s => EqPre s := by
  obtain ⟨Bs, Xl, w, L, name, a, hB, hX, -, hL, -, -, -, hh⟩ := link_named h l hl
  exact ⟨Bs, Xl, L, hB, hX, hL,
    { lot := VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Zp Bs.G₀ Xl l)
      name := name, place := a, seated := hh, bare := eqBare
      states := eqBare_states _
      law := eqRunLaw (ProofFile.k8ParW Zp Bs.G₀ Xl l) eqBare (eqBare_mem _)
      keeps := fun n s s' cs hr => atRecord_same _ s s' cs hr
      still := fun n s s' cs hr => atRecord_still _ s s' cs hr }, rfl, rfl, rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.atRecord_same
#print axioms Johnson.AtFull.Shape.atRecord_still
#print axioms Johnson.AtFull.Shape.k8_slot
#print axioms Johnson.AtFull.Shape.eqBare
#print axioms Johnson.AtFull.Shape.eqBare_states
#print axioms Johnson.AtFull.Shape.eqBare_mem
