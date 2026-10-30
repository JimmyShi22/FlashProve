-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RoomKeepK9.lean: TWO SHARES OF THE KEEPING BENEATH room_at_reach
(Johnson/P1L20R/RoomKeep.lean): THE FIELDS batch AND behind OF KeepShares, TO THE LETTER: a link's
batching, at the link's own gatherer (25), and the runs behind it (25), hand on "the index-mask
message's ledger is not closed and has n entries left" and "that message is a member of no group".
K9's OWN SHARE IS PAID; THE RUNS' SHARE IS ONE NAMED PREMISE.
  `StIx s s'`: the statement and the index-mask message's number stay. `hands2_of_stIx`: that hands
    both clauses on.
  `batch_stIx`: the batching's decision leaves both, where the gatherer's run of claims does: the
    draw and the adding write K9's part back with the statement that they read (the proof is
    `Meaning.K2.batch_calm`'s, Johnson/Goal/Meaning/GroupCalmK9.lean, at this relation).
  `batch_keeps`, `behind_keeps`: at one link. `field_batch`, `field_behind`: **the two fields**,
    under hruns: at each of the 25 links every hearing sub-protocol's runs of claims, and its runs
    behind the batching, leave both (`Meaning.K2.RunsKeep StIx`). Neither "reached" nor the scope is
    spent.
Limits. hruns IS PAID BY NOBODY HERE: it is each hearing kind's runs' share. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.Goal.Meaning.GroupCalmK9

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open VerifiableInference.Desc (Block Chain Link Claim claimsInBy)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open VerifiableInference.Desc.K9 (batch atS drawAlone adds)
open Johnson.Desc.First.Walk.Tied
open Meaning.K2 (RunsKeep link_claims_runs link_behind_runs bindE there_some atS_get)
open P1L20 (Hands2 hands2_same KeepsAt outOfGroupsB nA)
open ProofFile (Cl)

/-- The statement and the index-mask message's number stay. -/
def StIx (s s' : S) : Prop := s'.st = s.st ∧ s'.out.indexMasks = s.out.indexMasks

theorem stIx_refl (s : S) : StIx s s := ⟨rfl, rfl⟩

theorem stIx_trans (a b c : S) (h : StIx a b) (k : StIx b c) : StIx a c :=
  ⟨k.1.trans h.1, k.2.trans h.2⟩

/-- Where both stay, the two clauses are handed on. -/
theorem hands2_of_stIx {s s' : S} (h : StIx s s') (ho : outOfGroupsB s = true) : Hands2 s s' :=
  hands2_same (by unfold Johnson.Desc.First.Walk.Law.ledgerAt; rw [h.1, h.2]) (by rw [h.1]) h.2 ho

/-- What goes on to the later chains is not what K9's lens writes. (The proof is that of `out_set`,
Johnson/Desc/First/Link/Law/DoorBlind.lean, which is not imported.) -/
theorem set_out (s : S) (q : VerifiableInference.Desc.K9.Part) : (atS.set s q).out = s.out := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    show ((S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
      q.F).out = _
    by_cases ho : x.opened = true <;> simp [S.putLink, S.putFork, ho]
  | _ => rfl

/-- **The batching's decision**, where the gatherer's run of claims leaves both. -/
theorem batch_stIx (p : VerifiableInference.Desc.K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl StIx claims) :
    Decides StIx (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : StIx s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      exact ⟨(atS_get (there_some hq)).2, by rw [set_out]⟩
    · cases h1
  have a2 : StIx t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    exact stIx_trans _ _ _ (hcl t₁ x hx) ⟨(atS_get (there_some hq)).2, by rw [set_out]⟩
  exact stIx_trans _ _ _ a1 a2

/-- **A link's batching keeps**, at any number, where the hearing sub-protocols' runs leave both. -/
theorem batch_keeps {Q : Type} (c : Chain S Cl) (start : Q → S) (k : ℕ)
    (p : VerifiableInference.Desc.K9.Where) (Lk : Link S Cl)
    (hruns : ∀ b ∈ Lk.hear, RunsKeep StIx b) :
    KeepsAt c start k (batch atS p (claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro z s s' _ hy ho
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  exact hands2_of_stIx
    (batch_stIx p (link_claims_runs stIx_refl stIx_trans Lk hruns) s rs gs s' e) ho

/-- **So do the runs behind it.** -/
theorem behind_keeps (Lk : Link S Cl) (hruns : ∀ b ∈ Lk.hear, RunsKeep StIx b) (s t : S)
    (h : Lk.runBehind s = .ok t) (ho : outOfGroupsB s = true) : Hands2 s t :=
  hands2_of_stIx (link_behind_runs stIx_refl stIx_trans Lk hruns s t h) ho

/-- **THE FIELD batch OF KeepShares, TO THE LETTER.** -/
theorem field_batch {Q : Type} (Z : ProofFile.Pub) (c : Chain S Cl) (start : Q → S)
    (hruns : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ b ∈ Lk.hear, RunsKeep StIx b) :
    ∀ l < 25, ∀ (Lk : Link S Cl) p, c.links[l]? = some Lk → IM.k9At Z l = some p →
      KeepsAt c start (14 * l + nA l + 2)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
          (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) :=
  fun l hl Lk p e _ => batch_keeps c start _ p Lk (hruns l hl Lk e)

/-- **THE FIELD behind OF KeepShares, TO THE LETTER.** -/
theorem field_behind {Q : Type} (c : Chain S Cl) (start : Q → S)
    (hruns : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ b ∈ Lk.hear, RunsKeep StIx b) :
    ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk → ∀ z s t,
      Reach 0 c.blocksInOrder start (14 * l + nA l + 3) (z, s) → Lk.runBehind s = .ok t →
      outOfGroupsB s = true → Hands2 s t :=
  fun l hl Lk e _ s t _ h ho => behind_keeps Lk (hruns l hl Lk e) s t h ho

end LPFK9

#print axioms LPFK9.batch_stIx
#print axioms LPFK9.field_batch
#print axioms LPFK9.field_behind
