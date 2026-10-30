-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/LotsK9.lean: LotsKeep.lean, continued: the lot of the batching kind K9, with
the closing kind K10's sub-protocol in it (Johnson/Desc/ProofFile/Lot/K9.lean: `k9Ninth`), in
PureKeeps.lean's one form for a lot, at every property of the verifier's state that SameRows
carries. A law file; no running text imports it.

  `putLink_st`     writing the open segment's book-keeping leaves the statement.
  `takeN_rows`, `asRow_rows`, `door_rows`   the one equation's door takes mask entries and adds one
                   open row to a group: SameRows, by RowsGround.lean's takeMaskP_rows |
                   addRowP_rows. (The unfolding follows Johnson/Goal/Meaning/RecK9.lean's
                   takeN_codes | asRow_codes | door_keeps. Kin: door_rows of
                   Johnson/Desc/First/Link/Law/RowsSameAt.lean, at the relation written out.)
  `rowsD_drawAlone`, `keepsD_adds`, `keepsD_batch`   the batching draw leaves the statement; the
                   adding runs the gatherer once and then leaves the statement: so THE BATCHING
                   KEEPS P WHEREVER THE GATHERER THAT IT IS HANDED DOES: LinkKeeps' own form.
  `rowsD_oneEquation`, `rowsD_closing`, `rowsD_shut`   the closing's three: the second by
                   Johnson/Desc/First/Close/Law/RidesMore.lean's k10_rides_more.
  `lotKeeps_k9`    the lot.
Limits. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.LotsMore
import Johnson.Goal.Meaning.RecK9
import Johnson.Desc.First.Close.Law.RidesMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName Place Claim)
open VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc.K9 (atS Where takeN asRow door drawAlone adds batch oneEquation shut
  closing closeOf St Out recOf putRec)
open Meaning.K2 (bindE there_some atS_get)

variable {Cl : Type} {R : Fmt.RoundView → Prop} {P : S → Prop}

theorem putLink_st (s : S) (L : LinkCtx) : (s.putLink L).st = s.st := by
  unfold S.putLink
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-! ## The one equation's door -/

theorem takeN_rows {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (y : List Nat × St X), takeN o n d acc = .ok y → SameRows d.st y.2.st
  | 0, d, acc, y, h => by
    cases h
    exact SameRows.refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact (takeMaskP_rows d x.2 o x.1 (there_some hx)).trans (takeN_rows o n x.2 _ y h)

theorem asRow_rows {X : Type} {Rw : ReqRows} {f : ReqFrame}
    {q : VerifiableInference.Desc.K9.Equation} {d : St X} {y : OnBytes.Row × St X}
    (h : asRow Rw f q d = .ok y) : SameRows d.st y.2.st := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact SameRows.refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_rows o _ d [] x hx

theorem door_rows {X : Type} {owed : VerifiableInference.Desc.K9.RowsOwed} {laid : Option Nat}
    {L : LinkCtx} {F : Fork} {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    SameRows d.st o.d.st := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact (asRow_rows hy).trans (addRowP_rows y.2 d' _ y.1 (there_some hd))

/-! ## The batching -/

theorem rowsD_drawAlone (p : Where) : RowsD (drawAlone (Cl := Cl) atS p) := by
  intro s s' rs gs h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨chi, _, h⟩ := bindE h
    obtain ⟨o, ho, h⟩ := bindE h
    cases h
    exact sameRows_of_eq (atS_get (there_some hq)).2
  · cases h

theorem keepsD_adds (hP : Rides P) (p : Where) (piece : Nat) (what : String)
    {claims : S → Except String (List Claim × S)}
    (hcl : ∀ s y, claims s = .ok y → P s → P y.2) :
    KeepsD R P (adds (Cl := Cl) atS p piece what claims) := by
  intro s s' rs gs _ h hs
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  exact hP x.2 _ (sameRows_of_eq (atS_get (there_some hq)).2) (hcl s x hx hs)

/-- **The batching keeps P wherever the gatherer that it is handed does.** -/
theorem keepsD_batch (hP : Rides P) (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : ∀ s y, claims s = .ok y → P s → P y.2) : KeepsD R P (batch atS p claims) := by
  intro s s' rs gs hr h hs
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact keepsD_adds (R := R) (Cl := Claim) hP p p.piece "the segment's" hcl t₁ s' [] []
    (fun _ hm => nomatch hm) h
    ((rowsD_drawAlone (Cl := Claim) p).keeps (R := R) hP s t₁ rs gs hr h1 hs)

/-! ## The closing's three -/

theorem rowsD_oneEquation (p : Where) : RowsD (oneEquation (Cl := Cl) atS p) := by
  intro s s' rs gs h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  have e := door_rows ho
  rw [(atS_get (there_some hq)).2] at e
  exact e

theorem rowsD_closing (Q : Close.Par) : RowsD (closing (Cl := Cl) Q) := by
  intro s s' rs gs h
  have h' : ((Close.closeFrame (recOf s).owed (recOf s).frame (recOf s).st (Close.entries Q) rs).map
      (fun x => (⟨none, x.1, x.2⟩ : Close.Rec))).map (putRec s) = .ok s' := h
  cases hx : Close.closeFrame (recOf s).owed (recOf s).frame (recOf s).st (Close.entries Q) rs with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok x =>
    rw [hx] at h'
    cases h'
    have k := Close.k10_rides_more s _ rs x hx
    exact ⟨k.2.2.2.1, k.2.2.2.2.1⟩

theorem rowsD_shut (p : Where) (piece : Nat) : RowsD (shut (Cl := Cl) p piece) := by
  intro s s' rs gs h
  simp only [shut] at h
  obtain ⟨L, _, h⟩ := bindE h
  cases h
  exact sameRows_of_eq (putLink_st _ _)

theorem closeOf_rows (p : Where) (Q : Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p Q, RowsD b ∧ b.after = [] := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨rowsD_oneEquation (Cl := Cl) p, rfl⟩
  · exact ⟨rowsD_closing Q, rfl⟩
  · exact ⟨rowsD_shut p _, rfl⟩

/-! ## The lot -/

/-- **Kind K9's lot.** -/
theorem lotKeeps_k9 (hP : Rides P) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps R P (ProofFile.k9Ninth Z) G := by
  have key : ∀ b₀ ∈ (ProofFile.k9Ninth Z).own G, RowsD b₀ ∧ b₀.after = [] := by
    intro b₀ h0
    unfold ProofFile.k9Ninth at h0
    dsimp only at h0
    obtain ⟨w, -, h0⟩ := List.mem_flatMap.1 h0
    split at h0
    · exact closeOf_rows _ _ b₀ h0
    · obtain rfl := List.mem_singleton.1 h0
      exact ⟨fun s s' _ _ hy => (by cases hy), rfl⟩
  have hbat : ∀ a mk, (ProofFile.k9Ninth Z).batch G a = some mk → ∃ p, mk = fun g => batch atS p g := by
    intro a mk h
    unfold ProofFile.k9Ninth at h
    dsimp only at h
    split at h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
        exact ⟨p, rfl⟩
      · cases h
    · cases h
  have all : ∀ b ∈ (ProofFile.k9Ninth Z).blocks G, KeepsD R P b := by
    intro b hb
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact keepsD_retype ((key b₀ h0).1.keeps hP)
    · cases h
  refine ⟨fun b hb _ _ => all b hb, fun b hb _ => all b hb, fun b hb _ _ _ => ?_,
    fun a mk hm f hf => ?_, fun a mk hm f => ?_⟩
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · exact keepsRuns_none rfl (key b₀ h0).2
    · cases h
  · obtain ⟨p, rfl⟩ := hbat a mk hm
    exact keepsD_batch hP p hf
  · obtain ⟨p, rfl⟩ := hbat a mk hm
    exact keepsRuns_none rfl rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.door_rows
#print axioms VerifiableInference.Desc.First.K2.keepsD_batch
#print axioms VerifiableInference.Desc.First.K2.closeOf_rows
#print axioms VerifiableInference.Desc.First.K2.lotKeeps_k9
