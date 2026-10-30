-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FunsAtSeat.lean: THE APPROXIMATE RANGE PROOF (KIND K8): ONE MORE
THEOREM AT THE FOLD: AT EVERY STATE THAT THE FOLD HANDS ON IN FRONT OF THE ENTRY THAT SAMPLES, THE
CALLER'S LIST OF TABLES IS THE STRUCTURE'S OWN. NO SOUNDNESS.

Two readings of the verifier's state (Johnson/Desc/First/State.lean): `S.tl?`, the approximate range
proof's own Lean structure (`HTailF2`), which has a field `funs`; and `S.funs?`, the list of tables
as the sub-protocol that called for the range proof keeps it (at a layers' `Link` in what its own
rounds returned, at an attention `Link` and at the head's in the tables made there). The table's
reader takes the second; our law of the kind takes the first. Here: they are one list.
  `layers_funs_own`, `head_funs_own`, `att_funs_own`: behind an accepting run of each of the three
    texts of the step without a round that closes the list (Johnson/Desc/K8/ReadsQuiet.lean: layers,
    head; Johnson/Desc/First/Att/ReadsO.lean: readsAtSO): `S.tl?` is there, and `S.funs?` gives its
    field `funs`. By calls: layers_lays_tl (Johnson/Desc/First/K8/LawCondText.lean), layers_funs
    (Johnson/Desc/K8/ReadsQuietFuns.lean), head_ok, closed_ok (Johnson/Desc/K8/ReadsQuietLaws.lean),
    reads_next_o (Johnson/Desc/First/Att/Claims/ReadsNextO.lean), closeStep_tl
    (Johnson/Desc/First/K8/LawReadyAtt.lean).
  `joined_funs_own`: the step as the lot joins it behind ANY sub-protocol k: by
    quiet_arms (Johnson/Desc/First/K8/LawCondK1.lean). Nothing is asked of k, of the kind of the
    `Link`, or of the number l.
  `k1Reads_funs_own`: at the name that Johnson/IMR/K1Seat.lean gives the lot's entry (k1Reads).
  `funs_behind`: along the fold: if entry number k of the flat list is under k1Reads, the state
    behind the first k + 1 entries has the fact.
  `k8FunsAre`: **ALL 25 PLACES, ALONG THE FOLD FROM THE FIRST STATE**: by reads_under
    (Johnson/P1K8R/FrontAtSeat.lean) at each place.
  `k8FunsAreR`: the same at every statement that is reached at the number of the sampling entry
    (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean).
  `k8FunsAre_stay`: the same in the form `FunsAre` (Johnson/Desc/First/K8/LawFunsStay.lean), which
    that file carries through the sampling entry in both directions.
Limits. From an accepting fold alone: that the fold goes on at any value is not shown here: where it
rejects, every statement here holds emptily. The fold starts at the first state. Of the list itself
nothing is said: not that it is the right one, not that it is closed (that is k8Front's). secondHashFunction.
Of completeness's kind: no error term; nothing on soundness; nothing on hiding.

-/
import Johnson.P1K8R.FrontAtSeat
import Johnson.Desc.K8.ReadsQuietFuns
import Johnson.Desc.First.K8.LawFunsStay

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready
open ProofFile (Cl)

/-! ## Behind an accepting run of each of the three texts -/

/-- At a layers' `Link`: the list that is closed is the one that the own rounds returned. -/
theorem layers_funs_own (Q : VerifiableInference.Desc.K8.ReadsQuiet.PG) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.K8.ReadsQuiet.layers Q).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs := by
  obtain ⟨_, own, ha, ho, ht⟩ := layers_lays_tl Q h
  obtain ⟨_, funs, _, _, hf, _, hf'⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_funs h
  have e : s.funs? = some own.funs := by
    simp [VerifiableInference.Desc.First.S.funs?, ha, ho]
  obtain rfl : funs = own.funs := Option.some.inj (hf.symm.trans e)
  exact ⟨_, ht, hf'⟩

/-- At the head's `Link`: the tables that the step makes are laid, and their list is closed. -/
theorem head_funs_own (Q : VerifiableInference.Desc.K8.ReadsQuiet.PH) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.K8.ReadsQuiet.head Q).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs := by
  obtain ⟨_, _, _, t, _, _, ho, _, _, _, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨_, e', _, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  refine ⟨{ Q.hp.tl with funClosed := true, funs := t.funs }, ?_, ?_⟩
  · rw [e, e']
    simp [VerifiableInference.Desc.First.S.tl?, ho]
  · rw [e]
    simp [VerifiableInference.Desc.First.S.funs?, ho]

/-- At an attention `Link`: the like. -/
theorem att_funs_own (A : Attention.Plan) {s s' : S}
    (h : VerifiableInference.Desc.First.Att.readsAtSO A s = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs := by
  obtain ⟨_, _, _, _, _, c, _, _, _, _, _, hc, rfl⟩ := K5Law.reads_next_o A s s' h
  exact ⟨c.tl, rfl, (congrArg (fun y : HTailF2 => some y.funs) (closeStep_tl hc)).symm⟩

/-! ## The step as the lot joins it -/

/-- **Joined behind any sub-protocol k.** -/
theorem joined_funs_own (k : Block S Unit) (nm : String) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (piece : ℕ) (n : String) (a : Place) (w : String) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.Block.andThen nm k
      (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs := by
  obtain ⟨_, _, H⟩ := VerifiableInference.Desc.bindOk
    (x := k.decide s (rs.take k.rounds.length) (gs.take k.openings)) h
  rcases quiet_arms G l X piece n a w H with ⟨_, A, _, hd⟩ | ⟨_, _, _, ⟨_, _, _, hd⟩ | ⟨_, hd⟩⟩
  · exact att_funs_own A hd
  · exact layers_funs_own _ hd
  · exact head_funs_own _ hd

/-- At the lot's entry, by its name. -/
theorem k1Reads_funs_own (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ s'.funs? = some tl.funs :=
  joined_funs_own _ _ G l X _ _ _ _ h

/-! ## Along the fold -/

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- If entry number k is under the lot's entry, the state behind the first k + 1 entries has it. -/
theorem funs_behind {G : ProofFile.Ground} {b : Block S Cl} {k l pr : ℕ} {Xl : LinkH}
    {reads : Option (List ℕ)} (hf : c.blocksInOrder[k]? = some b)
    (hu : b.Under (IM.k1Reads Z G l Xl pr reads)) {s0 : S} {R : List Fmt.RoundView} {C : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (f : foldBlocks 0 (c.blocksInOrder.take (k + 1)) s0 R C = .ok out) :
    ∃ tl, out.1.tl? = some tl ∧ out.1.funs? = some tl.funs := by
  obtain ⟨t₄, R₄, C₄⟩ := out
  obtain ⟨t₃, R₃, C₃, f₃⟩ := Meaning.K2.fold_back (k := k) f
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next (k := k) hf f₃ f
  exact k1Reads_funs_own Z G l Xl pr reads (hu _ _ _ _ d)

/-- **k8FunsAre: AT ALL 25 PLACES, ALONG THE FOLD FROM THE FIRST STATE: THE CALLER'S LIST OF TABLES
IS THE STRUCTURE'S OWN.** -/
theorem k8FunsAre (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    ∃ tl, out.1.tl? = some tl ∧ out.1.funs? = some tl.funs := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨_, _, _, _, hf, _, hu⟩ := reads_under hS hR O (l := 24) (by omega) .head
      (IM.subs_head hS hR O.pub O.blank) 4 (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
    have f' : foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok out := f
    exact funs_behind (k := 342) hf hu f'
  · simp only [h24, if_false] at f
    by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      obtain ⟨_, _, _, _, hf, _, hu⟩ := reads_under hS hR O (l := 2 * g) (by omega) .layers
        (IM.subs_at hS hR O.pub O.blank (g := g) (by omega)) 3 (by unfold kindsBeforeBatching; rfl)
        (Or.inl rfl)
      have f' : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g) + 6)) (ProofFile.startS Z p) R C = .ok out := f
      exact funs_behind (k := 14 * (2 * g) + 5) hf hu f'
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      obtain ⟨_, _, _, _, hf, _, hu⟩ := reads_under hS hR O (l := 2 * g + 1) (by omega)
        .attention (IM.subs_att hS hR O.pub O.blank (g := g) (by omega)) 3
        (by unfold kindsBeforeBatching; cases (2 * g + 1 == 0) <;> rfl) (Or.inl rfl)
      have f' : foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g + 1) + 6)) (ProofFile.startS Z p) R C =
          .ok out := f
      exact funs_behind (k := 14 * (2 * g + 1) + 5) hf hu f'

/-- **AT EVERY REACHED STATE IN FRONT OF THE SAMPLING ENTRY.** -/
theorem k8FunsAreR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * x.1 + x.2 + 2) a) :
    ∃ tl, a.1.2.tl? = some tl ∧ a.1.2.funs? = some tl.funs := by
  obtain ⟨_, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.rchAt_fold h
  exact k8FunsAre hS hR O hx a.1.1 rs cols _ f

/-- The same in the form that rides through the sampling entry. -/
theorem k8FunsAre_stay (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ} (hx : x ∈ places) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks 0 (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) (ProofFile.startS Z p) R C = .ok out) :
    FunsAre out.1 := by
  obtain ⟨tl, ht, hf⟩ := k8FunsAre hS hR O hx p R C out f
  intro tl' ht' _
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  exact hf

end P1K8S

#print axioms P1K8S.layers_funs_own
#print axioms P1K8S.head_funs_own
#print axioms P1K8S.att_funs_own
#print axioms P1K8S.joined_funs_own
#print axioms P1K8S.k1Reads_funs_own
#print axioms P1K8S.funs_behind
#print axioms P1K8S.k8FunsAre
#print axioms P1K8S.k8FunsAreR
#print axioms P1K8S.k8FunsAre_stay
