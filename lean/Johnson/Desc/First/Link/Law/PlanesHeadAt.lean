-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanesHeadAt.lean (kind K9): THE ONE CLAUSE OF
  `PlanesHeadOk` (OkPlanes.lean:
  whatever form a reader of the head's "planes" hands in at the fixed part passes
    `EntsOk`), AT WHAT IS FIXED AT EVERY STATE REACHED IN FRONT OF THE HEAD's BATCHING. In the
      goals' scope. Statements and proofs.

Why it holds. The head's readers of "planes" hand in `Aff.ent iU3 ((first + i) / K) ((first + i) %
K)` at i below the table's length (`planeEntry`, Johnson/Stored/HeadSeat.lean), K the width of the
reads' array in the snapshot's ledger. Where every table that is shown ends at or below that width
(`TabsBelow`), first + i < K: so the virtual row is 0.

  `planeEntry_make`: a form that `planeEntry` hands in, under "the table ends at or below cols": its
    one entry stands at row 0 of array iU3.
  `planesHead_of`: **the clause at a fixed part q**, from hT (TabsBelow at the snapshot's own
    width), the static clause, hU and h0: the premises of `entsK6_of` (EntsHead.lean), less
    K6Ready.
  `planesHead_at_347`: **the clause at fixed9 (phiAll u psiAll) x.1.2, x reached at 347.**
PREMISES THAT STAY AT 347: the scope; "reached"; hi (the plan names iU3 for the third vector); H :
PosPlan (a theorem in scope since PosPlanBuilt.lean; kept a premise here, so that this file imports
neither that file nor the four on which it rests); h0; hs (the static clause at what is fixed).
Limits. Nothing on the attention's clauses. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.OkPlanes
import Johnson.Desc.First.Link.Law.EntsHeadAt
import Johnson.Desc.First.Link.Law.SortLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head (PlaneRead planeEntry callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- A form that the reader hands in names one entry, at row 0 of array iU3. -/
theorem planeEntry_make {tab : List (String × ℕ × ℕ)} {iU3 cols : ℕ}
    (hT : ∀ y ∈ tab, y.2.1 + y.2.2 ≤ cols) {x : PlaneRead} {i : ℕ} {f : Aff}
    (h : planeEntry tab iU3 cols x i = some f) : EntsMake iU3 [f] := by
  unfold planeEntry at h
  obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
  have hm : e ∈ tab := List.mem_of_find?_eq_some he
  split at h
  · rename_i hi
    obtain rfl := Option.some.inj h
    have hlt : e.2.1 + i < cols := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi _) (hT e hm)
    intro g hg y hy
    obtain rfl := List.mem_singleton.1 hg
    simp only [Aff.ent, List.mem_singleton] at hy
    subst hy
    exact ⟨Nat.div_eq_of_lt hlt, rfl⟩
  · exact nomatch h

variable {β : Type}

/-- **THE CLAUSE AT A FIXED PART.** -/
theorem planesHead_of {iU3 : ℕ} {kap : Phi β → Option Seen} {nU : Array ℕ} {q : Q β}
    (hT : ∀ y w tr, kap q.1 = some y → q.2 = some w → w.F.trees[iU3]? = some tr →
      TabsBelow iU3 y w.F tr.K)
    (hs : ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 q.1).1 = some tlb → tlb.ix.U.getD 2 none = some iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ r, callerReaders (planesQ iU3 kap) q = some r →
      (∀ e col f, r.1 e col = some f → EntsOk nU q [f]) ∧
        ∀ col f, r.2 col = some f → EntsOk nU q [f] := by
  intro r hr
  unfold callerReaders at hr
  obtain ⟨at_, ha, rfl⟩ := Option.map_eq_some_iff.1 hr
  unfold planesQ at ha
  obtain ⟨z, hz, ha⟩ := Option.bind_eq_some_iff.1 ha
  split at ha
  · obtain ⟨tt, htt, ha⟩ := Option.bind_eq_some_iff.1 ha
    obtain ⟨w, hw, ha⟩ := Option.bind_eq_some_iff.1 ha
    obtain ⟨tr, htr, ha⟩ := Option.bind_eq_some_iff.1 ha
    split at ha
    · exact nomatch ha
    · obtain rfl := Option.some.inj ha
      have hB := (hT z w tr hz hw htr).2 tt htt
      exact ⟨fun e col f hf => ents_of_static pi8 hs hU h0 (planeEntry_make hB
          (show planeEntry tt.tab iU3 tr.K (if e == 0 then .bits0 else .bits1) col = some f from
            hf)),
        fun col f hf => ents_of_static pi8 hs hU h0 (planeEntry_make hB
          (show planeEntry tt.tab iU3 tr.K .pin col = some f from hf))⟩
  · exact nomatch ha

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE CLAUSE AT 347.** -/
theorem planesHead_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {iU3 : ℕ}
    (hi : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl)
    (H : ∀ t0, tabsOfPlan Bs.G₀.W.hS Bs.G₀.W.H = some t0 →
      PosPlan Xl.tl Xl.Fp (shapesOf t0.funs))
    {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 x) (u : HTailF2) {nU : Array ℕ} (h0 : 0 < nU.getD 2 0)
    (hs : ∀ tlb v, (pi8 (fixed9 (phiAll u psiAll) x.1.2).1).1 = some tlb →
      (fixed9 (phiAll u psiAll) x.1.2).2 = some v → StaticOk tlb v.F) :
    ∀ r, callerReaders (planesQ iU3 kapAll) (fixed9 (phiAll u psiAll) x.1.2) = some r →
      (∀ e col f, r.1 e col = some f → EntsOk nU (fixed9 (phiAll u psiAll) x.1.2) [f]) ∧
        ∀ col f, r.2 col = some f → EntsOk nU (fixed9 (phiAll u psiAll) x.1.2) [f] :=
  planesHead_of
    (tabsBelow_at_347 hS hR O hi e3 H x h (phiAll u psiAll) kapAll (hkap_all u)) hs
    (hU_head hS hR O hi x h pi8 (phiAll u psiAll) u (fun _ => rfl)) h0

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planeEntry_make
#print axioms VerifiableInference.Desc.LinkJoin.planesHead_of
#print axioms VerifiableInference.Desc.LinkJoin.planesHead_at_347
