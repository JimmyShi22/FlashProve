-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/NoMergeAt345.lean: IN FRONT OF THE LOOKUP ON THE HEAD's DIGITS (border 345 of the first
chain's flat list) THE MERGE HAS NOT LAID ITS END VALUE: K9.mergeOf s = none at every state that is
reached there: in the goals' scope, at the hash secondHashFunction, at an opening, where the description's test
on its plan accepts. Wanted by the lookups' files (for the one open fact of K3's narrowed
condition); the like at border 340 is other files' to show. A law file; no running text imports it.

THE ROAD. At border 341 it lies (k6Reached_341, Johnson/P4R/K6ReachedAt341.lean).
Numbers 341 to 344 (the head's own rounds · the second sending with the quiet step that lays the
tables · the approximate range proof · the third sending) each lay the head's part of the state
anew with the field wo as it was: read off laws that hand each step's outcome outright.

  KeepsWo s t      if s stands in the head's segment, so does t, with the same wo.
  keepsWo_own · keepsWo_sending · keepsWo_reads · keepsWo_putTl · keepsWo_range   the legs, on the
                   bare sub-protocols' decisions.
  at_342 · at_343 · at_344   the same at the chain's own blocks (which bare sub-protocol stands
                   there: by the laws of Johnson/IMR/, called as
                   Johnson/P4R/WaK6At346.lean calls them).
  noMerge_345      along "reached" over the wrapped list.
  noMerge_rchAt    in the form that P5J/K03MergeAll.lean calls: RchAt (P4.FD Z A B c) 345 a →
                   a.1.2.failed = none → K9.mergeOf a.1.2 = none (the premise on the mark is not
                   spent).
  noMerge_at       general in a family Rch and a reader at_ under hRch.
Limits. A law from accepts: idle where nothing is reached. The full size alone. Nothing on
soundness.

-/
import Johnson.P4R.WaK6At346
import Johnson.P4R.K6AtRchAt
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K11

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6Reached)
open VerifiableInference.Desc.K1 (commitOwn commitAtS laid)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.PH ReadsQuiet.head_ok)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **The head's part keeps the merge's end value.** -/
def KeepsWo (s t : S) : Prop := ∀ o, s.here = .head o → ∃ o', t.here = .head o' ∧ o'.wo = o.wo

theorem KeepsWo.trans {a b c : S} (h : KeepsWo a b) (k : KeepsWo b c) : KeepsWo a c := by
  intro o ho
  obtain ⟨o', ho', e⟩ := h o ho
  obtain ⟨o'', ho'', e'⟩ := k o' ho'
  exact ⟨o'', ho'', e'.trans e⟩

theorem KeepsWo.merge {s t : S} (k : KeepsWo s t) {o : HeadOwn} (ho : s.here = .head o) :
    VerifiableInference.Desc.K9.mergeOf t = VerifiableInference.Desc.K9.mergeOf s := by
  obtain ⟨o', ho', e⟩ := k o ho
  unfold VerifiableInference.Desc.K9.mergeOf
  rw [ho, ho']
  show o'.wo.map (·.sFv) = o.wo.map (·.sFv)
  rw [e]

/-- The head's own rounds. -/
theorem keepsWo_own (h : Head.Shape) (iU3 work l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : KeepsWo s s' := by
  obtain ⟨a, F1, X, Q, ha, -, -, rfl⟩ := Came.decide_record h iU3 work l hd
  intro o ho
  obtain rfl : a = o := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho)
  exact ⟨_, rfl, rfl⟩

/-- A sending. -/
theorem keepsWo_sending {Cl' : Type} {P : VerifiableInference.Desc.K1.Par} {link moment : Nat}
    {arrays : Option (List Nat)} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl') P link moment arrays).decide s rs gs = .ok s') :
    KeepsWo s s' := by
  intro o ho
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (commitOwn (Cl := Cl') P link moment arrays).decide
        { owed := VerifiableInference.Desc.K1.owedOf s,
          held := { L := L, F := F, tl := tl, w := VerifiableInference.Desc.K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      have hop : o.opened = true := by
        unfold S.fork? at hF
        rw [ho] at hF
        by_contra hc
        simp [hc] at hF
      subst h
      refine ⟨{ o with L := y.held.L, F := y.held.F }, ?_, rfl⟩
      simp [S.putFork, S.putLink, laid, ho, hop]
  · cases h

/-- The second sending with the quiet step that lays the tables. -/
theorem keepsWo_reads {q : Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {P : ReadsQuiet.PH} {name : String}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : ((VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).andThen
      name (ReadsQuiet.head P)).decide s rs gs = .ok s') : KeepsWo s s' := by
  obtain ⟨s2, h1, h2⟩ := andThen_ok h
  refine (keepsWo_sending h1).trans ?_
  obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, rfl⟩ := ReadsQuiet.head_ok h2
  intro o ho
  obtain rfl : a = o := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho)
  exact ⟨_, rfl, rfl⟩

theorem keepsWo_putTl (s : S) (tl : HTailF2) : KeepsWo s (s.putTl tl) := by
  intro o ho
  cases hop : o.opened with
  | true =>
    refine ⟨{ o with tl := tl }, ?_, rfl⟩
    unfold S.putTl
    rw [ho]
    simp [hop]
  | false =>
    refine ⟨o, ?_, rfl⟩
    unfold S.putTl
    rw [ho]
    simp [hop, ho]

/-- The approximate range proof. -/
theorem keepsWo_range {Cl' : Type} (p : VerifiableInference.Desc.First.K8.Par) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Cl') VerifiableInference.Desc.First.K8.atS
      p).decide s rs gs = .ok s') : KeepsWo s s' := by
  obtain ⟨tl, rfl⟩ := VerifiableInference.Desc.First.K8.decide_atS p s s' rs gs h
  exact keepsWo_putTl s tl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem at_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[342]? = some b0)
    (hd : b0.decide s rs gs = .ok t) : KeepsWo s t := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, h1, h2, hX, -, hla⟩ :=
    IM.k1_reads_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  obtain ⟨-, l, hl, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : l = Xl := Option.some.inj (hl.symm.trans hX)
  have hp : (if l.kind == 0 || l.kind == 1 then 4 else 5) = 5 := by
    rw [hk]
    rfl
  have hq : IM.k1Quiet Bs.G₀ 24 l = VerifiableInference.Desc.K8.ReadsQuiet.head
      ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ := by
    unfold IM.k1Quiet
    simp only [hp]
    exact VerifiableInference.Reads.AtSeat.quiet_is Bs.G₀ 24 l _ _ _ hk (g := l.g) (by
      rw [List.getElem?_map, Array.getElem?_toList, hl]
      show some (l.kind, l.g) = some (2, l.g)
      rw [hk])
  unfold IM.k1Reads at hd2
  rw [hq] at hd2
  exact keepsWo_reads hd2

theorem at_343 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[343]? = some b0)
    (hd : b0.decide s rs gs = .ok t) : KeepsWo s t := by
  obtain ⟨Lk, b, Xl, h1, h2, -, hla, -⟩ := IM.k8_of_head hS hR O
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  exact keepsWo_range _ ((IM.k8_yes hla s t rs gs).1 hd).1

theorem at_344 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[344]? = some b0)
    (hd : b0.decide s rs gs = .ok t) : KeepsWo s t := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, h1, h2, -, -, hla⟩ :=
    IM.k1_digits_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z)
      24 (IM.k1Ix 24 true + 1) 2 digits : Block S Unit).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  exact keepsWo_sending hd2

/-- **At every state reached at 345.** -/
theorem noMerge_345 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {s : S}
    (h : Reach 0 (c.blocksInOrder.map below) start 345 (z, s)) :
    VerifiableInference.Desc.K9.mergeOf s = none := by
  obtain ⟨s344, B4, r4, g4, h344, hB4, -, d4⟩ := P4.peel h
  obtain ⟨s343, B3, r3, g3, h343, hB3, -, d3⟩ := P4.peel h344
  obtain ⟨s342, B2, r2, g2, h342, hB2, -, d2⟩ := P4.peel h343
  obtain ⟨s341, B1, r1, g1, h341, hB1, -, d1⟩ := P4.peel h342
  have c1 := P4.yes_341 hS hR O hB1 d1
  obtain ⟨a, -, -, -, ha, -, -, -⟩ := Came.decide_record _ _ _ _ c1
  have k : KeepsWo s341 s :=
    (((keepsWo_own _ _ _ _ c1).trans (at_342 hS hR O hB2 d2)).trans
      (at_343 hS hR O hB3 d3)).trans (at_344 hS hR O hB4 d4)
  rw [k.merge ha]
  exact (P4.k6Reached_341 hS hR O (P4.plan_at O hOk 340) (reach_raw h341)).wo

variable {Str : Type}

/-- **In the form that Johnson/P5J/K03MergeAll.lean calls.** -/
theorem noMerge_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (P4.FD Z A B c) 345 a → a.1.2.failed = none →
      VerifiableInference.Desc.K9.mergeOf a.1.2 = none :=
  fun a h _ => noMerge_345 hS hR O hOk (z := a.1.1) (s := a.1.2) h

/-- General in the family and the reader. -/
theorem noMerge_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {α : Type} (Rch : ℕ → α → Prop) (at_ : α → (ProofFile.InstPub × S) × Str)
    (hRch : ∀ a, Rch 345 a → RchAt (P4.FD Z A B c) 345 (at_ a)) :
    ∀ a, Rch 345 a → (at_ a).1.2.failed = none →
      VerifiableInference.Desc.K9.mergeOf (at_ a).1.2 = none :=
  fun a h u => noMerge_rchAt hS hR O hOk (at_ a) (hRch a h) u

end

end P1K11

#print axioms P1K11.KeepsWo.merge
#print axioms P1K11.keepsWo_own
#print axioms P1K11.keepsWo_sending
#print axioms P1K11.keepsWo_reads
#print axioms P1K11.keepsWo_range
#print axioms P1K11.at_342
#print axioms P1K11.at_343
#print axioms P1K11.at_344
#print axioms P1K11.noMerge_345
#print axioms P1K11.noMerge_rchAt
#print axioms P1K11.noMerge_at
