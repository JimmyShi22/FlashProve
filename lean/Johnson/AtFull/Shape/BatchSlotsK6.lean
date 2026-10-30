-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlotsK6.lean: THE SLOTS OF THE OUTPUT HEAD's FOUR RUNS OF CLAIMS (kind K6:
"norm", "join", "policy", "logits") AT THE HEAD's LINK OF THE PROOF FILE's OWN FIRST CHAIN (Slot,
Johnson/Desc/First/Batch/Shape/BatchBuild.lean), under the head at which the library's laws on that
chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). A joining of laws; nothing is evaluated.

  `names_at`: the seated sub-protocol's list of runs has the four names. `three_slot`: the slot of
    one of the three runs that are the kind's own.
  **`k6_slots`**: Bs by baseOf's value · Lk by cF.links[24]? · iU3 by
    Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3: there are slots for the pairs (3, "norm"), (3,
    "join"), (3, "policy"), (3, "logits") of Lk.hear whose laws' runG ARE threeRunG W.hS iU3 p
    ‹name› and joinRunG W.hS iU3 p, and whose pre IS, at all four, fun _ s => Ends p s, at W :=
    Bs.G₀.W and p := parOf W.hS (workAtW W) (another house's Johnson/Desc/K6/Shape/Laws.lean). Each
    slot's bare run is named too.

Limits. FOUR OF THE FIFTEEN RUNS BY KIND AND NAME (4 of the 215 runs). A slot pays nothing of its
law's pre. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchBuild
import Johnson.Desc.K6.Shape.Laws
import Johnson.Desc.Kinds.Law.SeatedRuns
import Johnson.IMR.K6Seat
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (seatedClaims parOf kind asClaim seatAt callerKeys)
open VerifiableInference.Desc.Kinds.Head.Law (seated_claims seated_run seated_join workAtW
  kind_names)
open VerifiableInference.Desc.Kinds.Head.Shape (threeLaw joinLaw threeRunG joinRunG Ends
  three_keeps join_keeps lookup_isSome three_strong join_strong bare)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem names_at {W : Verify.Public} {l : Nat} {ms : List (Nat × Nat)} {b : Block S Claim}
    (h : seatedClaims W l ms = some b) :
    b.claims.map (·.1) = ["norm", "join", "policy", "logits"] := by
  obtain ⟨iU3, -, e⟩ := seated_claims h
  rw [e, List.map_append, List.map_append, List.map_take, List.map_drop, kind_names]
  rfl

/-- One of the three runs that are the kind's own. -/
theorem three_slot {W : Verify.Public} {ms : List (Nat × Nat)} {b' : Block S Claim}
    (hb : seatedClaims W 24 ms = some b') {iU3 : Nat} (hU : W.H.tl.ix.U.getD 2 none = some iU3)
    {bs : List (Block S Claim)} {nm : String} {a : Place}
    (hs : bs[3]? = some (IM.seatedAs ProofFile.sameReply b' nm a)) (name : String)
    (hn : name ∈ ["norm", "join", "policy", "logits"]) (hj : name ≠ "join") :
    ∃ T : Slot ProofFile.sameReply bs (3, name),
      T.bare = bare W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name ∧
      T.law.runG = threeRunG W.hS iU3 (parOf W.hS (workAtW W)) name ∧
      T.law.pre = fun _ s => Ends (parOf W.hS (workAtW W)) s := by
  obtain ⟨run, hr⟩ := Option.isSome_iff_exists.mp
    (lookup_isSome b'.claims name (by rw [names_at hb]; exact hn))
  obtain ⟨i', hU', hk⟩ := seated_run hb hr hj
  obtain rfl : iU3 = i' := Option.some.inj (hU.symm.trans hU')
  refine ⟨
    { lot := b', name := nm, place := a, seated := hs, bare := run, states := hr
      law := threeLaw W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name run hk
      keeps := three_keeps W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name run hk
      still := fun n s s' cs hz => by
        rw [(three_strong W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name run hk n s s' cs
          hz).2.1] }, ?_, rfl, rfl⟩
  show run = _
  unfold VerifiableInference.Desc.Kinds.Head.Shape.bare
  rw [hk]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k6_slots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (iU3 : Nat),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ cF.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (∀ name ∈ ["norm", "policy", "logits"], ∃ T : Slot ProofFile.sameReply Lk.hear (3, name),
        T.bare = bare Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4 name ∧
        T.law.runG = threeRunG Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) name ∧
        T.law.pre = fun _ s => Ends (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) s) ∧
      ∃ T : Slot ProofFile.sameReply Lk.hear (3, "join"),
        T.bare = VerifiableInference.Desc.K3.joinRun
          (VerifiableInference.Desc.K3.seatCalls asClaim)
          (callerKeys (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) (seatAt Bs.G₀.W.hS iU3)) ∧
        T.law.runG = joinRunG Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) ∧
        T.law.pre = fun _ s => Ends (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', ms, e1, e2, -, hb, hla, -, -, -⟩ := IM.k6_of h.scope h.reads O
  have hs : Lk.hear[3]? = some (IM.seatedAs ProofFile.sameReply b' b.name IM.k6Place) :=
    e2.trans (congrArg some hla)
  obtain ⟨iU3, hU, -⟩ := seated_claims hb
  refine ⟨Bs, Lk, iU3, O.made, e1, hU, fun name hn => ?_, ?_⟩
  · refine three_slot hb hU hs name ?_ ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      rcases hn with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide
  · obtain ⟨run, hr⟩ := Option.isSome_iff_exists.mp
      (lookup_isSome b'.claims "join" (by rw [names_at hb]; simp))
    obtain ⟨i', hU', rfl⟩ := seated_join hb hr
    obtain rfl : iU3 = i' := Option.some.inj (hU.symm.trans hU')
    exact ⟨{ lot := b', name := b.name, place := IM.k6Place, seated := hs
             bare := _, states := hr
             law := joinLaw Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W))
             keeps := join_keeps _
             still := fun n s s' cs hz => by
               obtain ⟨⟨v, G, -, rfl, -⟩, -⟩ :=
                 join_strong Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) n s s' cs hz
               exact VerifiableInference.Desc.First.Shape.putFork_st s G }, rfl, rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.names_at
#print axioms Johnson.AtFull.Shape.three_slot
#print axioms Johnson.AtFull.Shape.k6_slots
