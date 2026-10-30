-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RowsOneInScope.lean: IN SCOPE, WHERE THE PROOF FILE's PIN ON WHAT WAS MADE ACCEPTS:
THE SECOND READING OF THE THREE PUBLIC FILES HAS ONE VALUE, WHEREVER IT RETURNS: every radius among
it. No premise on the links' arms. Theorems on public data. A law file; no running text imports it.
  `planned_of_rows`   where sendRowsOf returns, so does `planned` of the program `verify-on-bytes`.
  `rows_fixed`      InScope W · ProofFile.pubPlain secondHashFunction W.pol W.lay W.KL = .ok Z · madePinnedAt … = true
                    · planned returns ⊢ sendRowsOf W.pol W.lay W.KL = rowsFrom (writtenMade.at
                    Hung.none) (List.replicate 25 1) 13 (armOf Z.made.p.X): of the four arguments
                    three are written.
  `rows_one_in_scope`   two sets of public files in scope, each with its public part, the pin's
                    yes and a return of sendRowsOf ⊢ the two values are one.
  `rows_are_W`      one such set, and a return of the closed term rowsW
(Johnson/LPFE1R/RowsAtWritten.lean) ⊢ the value is rowsW's. How: rows_of_made
(Johnson/Desc/First/Link/Law/RowsOfMade.lean) · made_in_scope
(Johnson/Goal/Numbers/MadeInScope.lean) · rowsFrom_four · twelve groups of layers in scope
(H2K.Sizes.public_at_scope) · rows_no_arms (Johnson/Desc/First/Link/Law/RowsNoArms.lean).

Limits. At secondHashFunction. THE RETURNS ARE PREMISES. That rowsW returns is an evaluation: Lean's kernel
refused the closed Bool (stuck, no timeout). So "one over the scope" is a theorem; "the written one"
is not, here. Nothing on what a radius means. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.RowsAtWritten
import Johnson.Desc.First.Link.Law.RowsOfMade
import Johnson.Desc.First.Link.Law.RowsNoArms
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (sendRowsOf SendRow)
open Johnson.G.MadeFree (Free Hung freeOf)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope)

theorem links_written : writtenMade.sized.proof.request.link.length = 25 := by decide +kernel

/-- Where the second reading returns, the planner has returned. -/
theorem planned_of_rows {pol lay KL : ByteArray} {r : List SendRow}
    (h : sendRowsOf pol lay KL = .ok r) :
    ∃ p, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p := by
  unfold sendRowsOf at h
  obtain ⟨_, hs, _⟩ := exc_bind h
  rw [VerifiableInference.Number.sendsOf_eq] at hs
  obtain ⟨p, hp, _⟩ := exc_bind hs
  exact ⟨p, hp⟩

/-- Of the second reading's four arguments three are written. -/
theorem rows_fixed {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {p : OnBytes.Model.Verify.Planned}
    (hp : OnBytes.Model.Verify.planned W.pol W.KL (some W.lay) = .ok p) :
    sendRowsOf W.pol W.lay W.KL =
      rowsFrom (writtenMade.at Hung.none) (List.replicate 25 1) 13 (armOf Z.made.p.X) := by
  have hm : freeOf Z.made.p.chains.made = writtenMade :=
    made_in_scope hW (show ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z from h) hy
  have e1 : Z.made.p.chains.made.sized = writtenMade.sized := congrArg Free.sized hm
  have e2 : Z.made.p.chains.made.key = writtenMade.key := congrArg Free.key hm
  have e3 : Z.made.p.chains.made.proof = writtenMade.proof := congrArg Free.proof hm
  have e4 : Z.made.p.chains.made.entry = writtenMade.entry := congrArg Free.entry hm
  obtain ⟨_, _, _, _, _, _, _, hX, _⟩ := OnBytes.Model.Verify.planned_parts hp
  have eX := (made_tie h hp).1
  have hN : Z.made.p.X.NGr = 12 := by
    rw [← eX]
    exact (H2K.Sizes.public_at_scope hW hX).groups
  rw [rows_of_made h hp, e1, links_written, hN]
  exact rowsFrom_four (c := Z.made.p.chains.made) (c' := writtenMade.at Hung.none) e1 e2 e3 e4 _ _ _

/-- **One value over the scope, under the pin.** -/
theorem rows_one_in_scope {W W' : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    (hW' : VerifierAndGoals.InScope W' = true) {Z Z' : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (h' : ProofFile.pubPlain OnBytes.secondHashFunction W'.pol W'.lay W'.KL = .ok Z')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hy' : madePinnedAt Z'.p.X.P Z'.p.chains.made Z'.first Z'.made = true)
    {r r' : List SendRow} (hr : sendRowsOf W.pol W.lay W.KL = .ok r)
    (hr' : sendRowsOf W'.pol W'.lay W'.KL = .ok r') : r = r' := by
  obtain ⟨p, hp⟩ := planned_of_rows hr
  obtain ⟨p', hp'⟩ := planned_of_rows hr'
  rw [rows_fixed hW h hy hp] at hr
  rw [rows_fixed hW' h' hy' hp'] at hr'
  exact rows_no_arms _ _ _ hr hr'

/-- **The value is the closed term's, where that returns.** -/
theorem rows_are_W {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {r w : List SendRow} (hr : sendRowsOf W.pol W.lay W.KL = .ok r) (hw : rowsW = .ok w) :
    r = w := by
  obtain ⟨p, hp⟩ := planned_of_rows hr
  rw [rows_fixed hW h hy hp] at hr
  exact rows_no_arms _ _ _ hr hw

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rows_fixed
#print axioms VerifiableInference.Desc.LinkJoin.rows_one_in_scope
#print axioms VerifiableInference.Desc.LinkJoin.rows_are_W
