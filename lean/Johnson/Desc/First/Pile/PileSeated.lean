-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pile/PileSeated.lean: "THE PILE STAYS" (`PileStays`,
Johnson/Desc/First/Pile/PileMakers.lean) AT THE OTHER MAKERS OF THE REQUEST'S OWN CHAIN; AND WHAT
THE WRITERS AMONG THEM WRITE. Statements with their proofs; no definition.

Main names (namespace `Meaning.K2`).
  The links' frames, over the laws of Johnson/Top/H0/Walk/FrameLaw.lean: `layFront_pile`,
    `openAtt_pile`, `openLay_pile`. **`openLayZero_rows`**: LINK 0's "opened" WRITES THE INDEX
    MASKS' NUMBER; the rows stay. **`clearWith_cases`**: "cleared" IS THE PILE'S ONE WRITER: the
    pile stays, or the row that the row's function returns, at the state's own index masks' number
    and messages, is laid at its end.
  Kind K1: `firstAtS_pile`, `commitAtS_pile`, `laterAt_pile`. Kinds K9 and K10: `oneEquation_pile`,
    `closing_pile`, `shut_pile`, `closeOf_pile`; **`batch_over`**: the batching, at any transitive
    relation that holds whatever leaves the pile. The quiet step behind the reads: `layers_pile`,
    `headReads_pile`, `readsAtO_pile`. Kind K2's five: `k2_pile`, `headFrontQ_pile`,
    `headOpenQ_pile`, `finishFrontQ_pile`, `finishBehindQ_pile`. Kind K12 at the chain's last
    proximity test: `atFinish_pile`. W's commitment with kind K13's sub-protocol behind it:
    `sendAtS_pile`, `rowsB_pile`, **`atM4_pile`**.
  More writers of State.lean: `pile_putLink`, `pile_putLive`; `not_mem_of_between`,
    `not_mem_of_link`.

Every "there is", walked. `clearWith_cases`: w, r, os: tied by the row's function's own equation.
NOT HERE: kind K13's batching (`K13.atM3`): it turns the pile into the one row and the stand to the
chain's end: the third writer.
Limits. Frame laws, as in PileMakers.lean. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Pile.PileMakers
import Johnson.Goal.Meaning.OwnMakers
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Top.H0.Tw.K2C.LeavesOut
import Johnson.Desc.K12.SeatLeaves
import Johnson.Desc.K13.Law.AtM4
import Johnson.Desc.K1.Law.HereAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.K9 (atS drawAlone adds batch oneEquation Where door drawnClean drawn
  Out Drawn St RowsOwed shut)
open Johnson.Desc.First.Walk

variable {Cl : Type}

/-! ## More writers of State.lean -/

theorem not_mem_of_between {s : S} (h : s.atBetween = true) : ∀ a, s.here ≠ .mem a := by
  intro a e
  unfold S.atBetween at h
  rw [e] at h
  cases h

theorem not_mem_of_link {s : S} {L : LinkCtx} (h : s.link? = some L) : ∀ a, s.here ≠ .mem a := by
  intro a e
  unfold S.link? at h
  rw [e] at h
  cases h

theorem pile_putLink (s : S) (L : LinkCtx) : PileStays s (s.putLink L) := by
  (unfold S.putLink; repeat' split) <;> first
    | exact pile_refl _
    | exact pile_of rfl rfl (by simp_all) (by simp)

theorem pile_putLive (s : S) (c : ChainCheck) : PileStays s (s.putLive c) := by
  unfold S.putLive
  split
  · exact pile_putLink _ _
  · exact pile_here rfl rfl rfl

/-! ## The links' frames, over the laws of Johnson/Top/H0/Walk/FrameLaw.lean -/

theorem layFront_pile (l : Nat) : Fn PileStays (layFront l) := fun s t h => by
  rw [(Law.layFront_ok h).1]
  exact pile_refl s

theorem openAtt_pile (P : AttPar) : Fn PileStays (openAtt P) := fun s t h => by
  obtain ⟨hB, -, -, -, hl, -, -, -, -, ho⟩ := Law.openAtt_ok h
  exact pile_of (by rw [ho]) (by rw [ho]) (not_mem_of_between hB) (not_mem_of_link hl)

theorem openLay_pile (P : LayPar) : Fn PileStays (openLay P) := fun s t h => by
  obtain ⟨hB, -, -, -, -, hl, -, -, -, -, ho⟩ := Law.openLay_ok h
  exact pile_of (by rw [ho]) (by rw [ho]) (not_mem_of_between hB) (not_mem_of_link hl)

/-- **Link 0's "opened" WRITES THE INDEX MASKS' NUMBER**; the rows on the table stay, and neither
state stands at the chain's end. -/
theorem openLayZero_rows {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    t.rows = s.rows ∧ (∀ a, s.here ≠ .mem a) ∧ ∀ a, t.here ≠ .mem a := by
  obtain ⟨hB, -, -, -, ⟨im, -, ho⟩, hl, -⟩ := Law.openLayZero_ok h
  have h1 := not_mem_of_between hB
  have h2 := not_mem_of_link hl
  exact ⟨by rw [rows_of_not_mem h1, rows_of_not_mem h2, ho], h1, h2⟩

/-- **"Cleared", THE PILE's ONE WRITER**: the pile stays, or the row that the row's function returns
at the state's own index masks' number and messages is laid at its end. -/
theorem clearWith_cases {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    PileStays s t ∨ ∃ w r os, row s.out.indexMasks w X.NCL s.st.oracles = .ok (r, os) ∧
      t.rows = s.rows ++ [r] ∧ t.out.indexMasks = s.out.indexMasks ∧
      (∀ a, s.here ≠ .mem a) ∧ ∀ a, t.here ≠ .mem a := by
  obtain ⟨C, F, hC, -⟩ := Law.clearWith_ok h
  have hn := not_mem_of_link hC
  have e := Law.clearWith_eq h
  cases hv : X.fv with
  | false =>
    left
    rw [e.1 hv]
    exact pile_of rfl rfl hn (fun _ k => nomatch k)
  | true =>
    right
    obtain ⟨w, r, os, -, hr, ht⟩ := e.2 hv
    have hn' : ∀ a, t.here ≠ .mem a := by
      rw [ht]
      exact fun _ k => nomatch k
    refine ⟨w, r, os, hr, ?_, by rw [ht]; rfl, hn, hn'⟩
    rw [rows_of_not_mem hn', rows_of_not_mem hn, ht]
    rfl

/-! ## K1's two -/

theorem commitAtS_pile (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole PileStays (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    exact pile_trans _ _ _ (pile_trans _ _ _
      (pile_here (s' := laid s y.held.w) rfl rfl rfl) (pile_putLink _ _)) (pile_putFork _ _)
  · cases h

theorem laterAt_pile (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole PileStays (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_pile _ link moment arrays

theorem firstAtS_pile (q : Params.First) (gp : GPar) :
    Whole PileStays (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  exact pile_here rfl rfl rfl

/-! ## K9's and K10's -/

theorem pile_atS_set (s : S) (p : K9.Part) : PileStays s (atS.set s p) := by
  have e : PileStays s ((s.putLink p.L).putFork p.F) :=
    pile_trans _ _ _ (pile_putLink s p.L) (pile_putFork _ p.F)
  exact e

theorem oneEquation_pile (p : Where) : Whole PileStays (oneEquation (Cl := Cl) atS p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  exact pile_atS_set _ _

theorem closing_pile (P : Close.Par) : Whole PileStays (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact (pile_putLive s { s.live with frame := x.1 } : PileStays s _)

theorem shut_pile (p : Where) (piece : Nat) : Whole PileStays (shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  exact pile_putLink _ _

theorem closeOf_pile (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole PileStays b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_pile p
  · exact closing_pile P
  · exact shut_pile p _

/-- **The batching, at any transitive relation that holds whatever leaves the pile.** -/
theorem batch_over {R : S → S → Prop} (ht : ∀ a b c, R a b → R b c → R a c)
    (hs : ∀ s s', PileStays s s' → R s s') (p : K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl R claims) :
    Whole R (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : R s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact hs _ _ (pile_atS_set _ _)
    · cases h1
  have a2 : R t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact ht _ _ _ (hcl t₁ x hx) (hs _ _ (pile_atS_set _ _))
  exact ht _ _ _ a1 a2

/-! ## The quiet step behind the reads -/

theorem layers_pile (P : K8.ReadsQuiet.PG) : Whole PileStays (K8.ReadsQuiet.layers P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, own, tl', ha, -, -, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact pile_of rfl rfl (by rw [ha]; exact fun _ k => nomatch k) (fun _ k => nomatch k)

theorem headReads_pile (P : K8.ReadsQuiet.PH) : Whole PileStays (K8.ReadsQuiet.head P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact pile_of rfl rfl (by rw [ha]; exact fun _ k => nomatch k) (fun _ k => nomatch k)

theorem readsAtSO_pile (A : Attention.Plan) : Fn PileStays (Att.readsAtSO A) := fun s s' h => by
  obtain ⟨a, t, tl, ha, rfl⟩ := readsAtSO_eq h
  exact pile_of rfl rfl (by rw [ha]; exact fun _ k => nomatch k) (fun _ k => nomatch k)

theorem readsAtO_pile {W : Verify.Public} {l g : Nat} {b : Block S Cl}
    (h : Att.readsAtO W l g = some b) : Whole PileStays b := by
  unfold Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨fun s _ _ s' e => readsAtSO_pile A s s' e, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

/-! ## Kind K2's five -/

theorem k2_pile (p : K2.P2) : Whole PileStays (K2.codeSwitchKind p : Block S Unit) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h : K2.decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok s' := h
  unfold K2.decideWith at h
  simp only at h
  split at h
  · cases h
  · split at h
    · obtain ⟨x, hx, h⟩ := K2.bindOk h
      obtain ⟨_, ha, h⟩ := K2.bindOk h
      obtain ⟨_, _, h⟩ := K2.bindOk h
      cases h
      exact pile_here rfl rfl rfl
    · rename_i a _ hh
      obtain ⟨_, _, h⟩ := K2.bindOk h
      obtain ⟨x, hx, h⟩ := K2.bindOk h
      obtain ⟨_, ha, h⟩ := K2.bindOk h
      cases h
      exact pile_of rfl rfl (by rw [hh]; exact fun _ k => nomatch k) (fun _ k => nomatch k)
    · rename_i a _ hh
      obtain ⟨_, _, h⟩ := K2.bindOk h
      obtain ⟨_, _, h⟩ := K2.bindOk h
      obtain ⟨x, hx, h⟩ := K2.bindOk h
      obtain ⟨_, ha, h⟩ := K2.bindOk h
      cases h
      exact pile_of rfl rfl (by rw [hh]; exact fun _ k => nomatch k) (fun _ k => nomatch k)
    · cases h

theorem headFrontQ_pile (tl : HTailF2) : Fn PileStays (K2.headFrontQ tl) := fun s s' h => by
  have ho := K2.headFrontOut tl s s' h
  unfold K2.headFrontQ at h
  split at h
  · cases h
  · rename_i hB
    split at h
    · cases h
    · obtain ⟨x, _, h⟩ := K2.bindOk h
      obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
      split at h
      · cases h
        exact pile_of (by rw [ho]) (by rw [ho]) (not_mem_of_between (by simpa using hB))
          (fun _ k => nomatch k)
      · cases h

theorem finishFrontQ_pile : Fn PileStays K2.finishFrontQ := fun s s' h => by
  have ho := K2.finishFrontOut s s' h
  unfold K2.finishFrontQ at h
  split at h
  · cases h
  · rename_i hB
    split at h
    · cases h
    · split at h
      · obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
        split at h
        · cases h
          exact pile_of (by rw [ho]) (by rw [ho]) (not_mem_of_between (by simpa using hB))
            (fun _ k => nomatch k)
        · cases h
      · cases h
      · cases h

theorem finishBehindQ_pile : Fn PileStays K2.finishBehindQ := fun s s' h => by
  unfold K2.finishBehindQ at h
  split at h
  · rename_i a ha
    cases hb : _root_.Tw.K2.finishBehind a.sw with
    | error e => rw [hb] at h; cases h
    | ok m =>
      rw [hb] at h
      cases h
      exact pile_of rfl rfl (by rw [ha]; exact fun _ k => nomatch k) (fun _ k => nomatch k)
  · cases h

theorem headOpenQ_pile (P : K2.HeadPar) : Fn PileStays (K2.headOpenQ P) := fun s s' h => by
  obtain ⟨a, y, ha, -, -, -, -, ho⟩ := K2.headOpenLays P s s' h
  refine pile_of (by rw [ho]) (by rw [ho]) (by rw [ha]; exact fun _ k => nomatch k) ?_
  unfold K2.headOpenQ at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := K2.bindOk h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hf, h⟩ := K2.bindOk h
        dsimp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h₁, h⟩ := K2.bindOk h
                split at h
                · cases h
                  exact fun _ k => nomatch k
                · cases h
        · cases h
  · cases h

/-! ## Kind K12's, at the first chain's last proximity test -/

theorem atFinish_pile (p : K12.P12) : Whole PileStays (K12.atFinish p) :=
  ⟨fun s rs gs s' h => pile_here (K12.Seat.atFinish_leaves_here p s rs gs s' h)
      (congrArg (·.pending) (K12.Seat.atFinish_leaves_out p s rs gs s' h))
      (congrArg (·.indexMasks) (K12.Seat.atFinish_leaves_out p s rs gs s' h)),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## W's commitment, with kind K13's sub-protocol behind it -/

theorem sendAtS_pile (Q : K1.Par) : Decides PileStays (K1.sendAtS Q : Block S Cl) := by
  intro s rs gs s' h
  obtain ⟨a, ids, h1, -, h2, -, ho, -⟩ := K1.sendAtS_here Q s s' rs gs h
  refine ⟨?_, by rw [ho], fun _ => ⟨a, h1⟩⟩
  unfold S.rows
  rw [h1, h2, ho]

theorem rowsB_pile (p : K13.Where) : Decides PileStays (K13.rowsB (Cl := Cl) K13.atS p) := by
  intro s rs gs s' h
  obtain ⟨m₀, l, o, owed, hs, -, -, e⟩ := K13.Law.rowsB_at h
  exact ⟨K13.Law.rowsB_rows h, by rw [e], fun _ => ⟨m₀, hs⟩⟩

theorem atM4_pile (p : K13.Where) (Q : K1.Par) :
    Whole PileStays (K13.atM4 (Cl := Cl) p (K1.sendAtS Q)) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' : ((K1.sendAtS Q : Block S Cl).decide s _ _).bind (fun m =>
      (K13.rowsB (Cl := Cl) K13.atS p).decide m _ _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := Keeps.ebind_ok h'
  exact pile_trans _ _ _ (sendAtS_pile Q _ _ _ _ h1) (rowsB_pile p _ _ _ _ h2)

#print axioms not_mem_of_between
#print axioms not_mem_of_link
#print axioms pile_putLink
#print axioms pile_putLive
#print axioms layFront_pile
#print axioms openAtt_pile
#print axioms openLay_pile
#print axioms openLayZero_rows
#print axioms clearWith_cases
#print axioms commitAtS_pile
#print axioms laterAt_pile
#print axioms firstAtS_pile
#print axioms pile_atS_set
#print axioms oneEquation_pile
#print axioms closing_pile
#print axioms shut_pile
#print axioms closeOf_pile
#print axioms batch_over
#print axioms layers_pile
#print axioms headReads_pile
#print axioms readsAtSO_pile
#print axioms readsAtO_pile
#print axioms k2_pile
#print axioms headFrontQ_pile
#print axioms finishFrontQ_pile
#print axioms finishBehindQ_pile
#print axioms headOpenQ_pile
#print axioms atFinish_pile
#print axioms sendAtS_pile
#print axioms rowsB_pile
#print axioms atM4_pile

end Meaning.K2
