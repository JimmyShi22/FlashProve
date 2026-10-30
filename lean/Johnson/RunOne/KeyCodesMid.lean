-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCodesMid.lean: THEOREMS. K13.quiet asks Own.linFits, not linOk (K13/Text.lean): linFits_of_yes is what the text gives; linOk_of_yes follows by linFits_eq. **INSIDE THE BLOCK batt.1.batt: THE STATE THAT K13.quiet IS HANDED HAS THE CODES OF THE BORDER IN FRONT; so, at a record that the first chain has reached, the older test linOk is asked AT THE PLAN's OWN CODES.** KeyCodesPaid.lean's
law speaks of borders; K13.quietB is the last quarter of its block (Key.batchTableRows := layPile · K13.frontB · K13.claimCombinationBlock · K13.quietB): this file walks the three quarters in front.
OBJECT. Key.batchTableRows keysOf one N sent (Johnson/Desc/Key/One.lean) · K13.quietB | K13.quiet (Johnson/Desc/K13/Kind.lean:141-146 · Text.lean:141-143) · Key.layPile. USER. The pair (linOk · K13.quiet) and layPile's line that reads s.d.st.codes.mask. LETTERS. keysOf · one · N · sent · the states; X · N · P · D · k · a in the tops.
  quiet_reads        a yes of the block from s: ∃ q msg, the part q that quietB reads has q.d.st.codes = s.d.st.codes, and K13.quiet q.d.st.codes one.lin = .ok msg
  pile_reads         layPile is handed s itself: the border's record
  linFits_of_yes     so, where s.d.st.codes = one.codes: Own.linFits one.codes one.lin = true · linOk_of_yes: and linOk one.codes one.lin = true
  first_growsBy      first_grows in the words of Johnson/Desc/StatementGrows.lean: ChainKeeps (GrowsBy st₁) (Key.descriptionFromSource X N P).first
  linOk_at_reached   **Hist₁ … k a → a yes of that block at a's record → linOk X.Y.k.oneTime.codes X.Y.k.oneTime.lin = true**
What is not claimed. At which k the block stands (the law holds at every k). Chains 2 | 3. Nothing on soundness.

-/
import Johnson.RunOne.KeyCodesPaid
import Johnson.Desc.StatementGrows
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false

namespace Johnson.RunOne.KeyCodes

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block Grows)
open VerifiableInference.Desc.Ground (groundKeeps_grows)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open LPFD (Hist₁)

variable {β Cl : Type}

/-- layPile is handed the border's record itself. -/
theorem pile_reads {keysOf : β → List (List Lkp.Keys)} {one : OneTime} {N : Pieces} {sent : Nat} {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') : ∃ a, layPile keysOf one s = .ok a := by
  obtain ⟨c, h123, -⟩ := ebind_ok h
  obtain ⟨b, h12, -⟩ := ebind_ok h123
  obtain ⟨a, h1, -⟩ := ebind_ok h12
  exact ⟨a, h1⟩

/-- **The state that K13.quiet is handed has the codes of the border in front.** -/
theorem quiet_reads {keysOf : β → List (List Lkp.Keys)} {one : OneTime} {N : Pieces} {sent : Nat} {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') :
    ∃ (q : VerifiableInference.Desc.K13.Part) (msg : Array OracleNotice), q.d.st.codes = s.d.st.codes ∧ VerifiableInference.Desc.K13.quiet q.d.st.codes one.lin = .ok msg := by
  obtain ⟨c, h123, h4⟩ := ebind_ok h
  obtain ⟨b, h12, h3⟩ := ebind_ok h123
  obtain ⟨a, h1, h2⟩ := ebind_ok h12
  have g1 : Grows (st₁ s) (st₁ a) := quietAt_keeps (Cl := Cl) (layPile_keeps groundKeeps_grows keysOf one) s _ _ a h1
  have g2 : Grows (st₁ a) (st₁ b) := VerifiableInference.Desc.K13.frontB_keeps groundKeeps_grows.quiet _ st₁ lens_lensSt _ a _ _ b h2
  have g3 : Grows (st₁ b) (st₁ c) := VerifiableInference.Desc.K13.battB_keeps groundKeeps_grows.quiet _ st₁ lens_lensSt _ b _ _ c h3
  obtain ⟨q, hq, h4⟩ := bind_ok h4
  obtain ⟨_, _, h4⟩ := bind_ok h4
  obtain ⟨msg, hm, -⟩ := bind_ok h4
  have e : q.d.st = st₁ c := lens_lensSt.get c q (VerifiableInference.Desc.K13.part_ok hq)
  refine ⟨q, msg, ?_, hm⟩
  rw [e]
  exact (g3.1.trans g2.1).trans g1.1

/-- So, where the border's codes are the plan's, K13.quiet's test on the shape is asked at the plan's own codes. THAT TEST IS Own.linFits (Johnson/Desc/K13/Text.lean:145), the older linOk taken over under a new name. -/
theorem linFits_of_yes {keysOf : β → List (List Lkp.Keys)} {one : OneTime} {N : Pieces} {sent : Nat} {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hs : s.d.st.codes = one.codes) (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') : VerifiableInference.Desc.Own.linFits one.codes one.lin = true := by
  obtain ⟨q, msg, hq, hm⟩ := quiet_reads h
  rw [hq, hs] at hm
  unfold VerifiableInference.Desc.K13.quiet at hm
  obtain ⟨_, h3, -⟩ := bind_ok hm
  by_cases ha : VerifiableInference.Desc.Own.linFits one.codes one.lin = true
  · exact ha
  · simp [VerifiableInference.Desc.K13.need, ha] at h3

/-- The same of the older test: by linFits_eq (Johnson/Desc/Own/LinAgree.lean:48). -/
theorem linOk_of_yes {keysOf : β → List (List Lkp.Keys)} {one : OneTime} {N : Pieces} {sent : Nat} {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hs : s.d.st.codes = one.codes) (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') : linOk one.codes one.lin = true :=
  (VerifiableInference.Desc.Own.linFits_eq one.codes one.lin) ▸ linFits_of_yes hs h

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- first_grows in the very words of Johnson/Desc/StatementGrows.lean (its premise ChainKeeps (GrowsBy st₁) F.first): By Grows st and GrowsBy st are one term by unfolding: Lean's word. -/
theorem first_growsBy :
    VerifiableInference.Desc.Keeps.ChainKeeps (VerifiableInference.Desc.ChainEnd.GrowsBy (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first := first_grows

/-- **At a record that the first chain has reached, linOk is asked at the plan's own codes.** -/
theorem linOk_at_reached (D : OnBytes.Maker.WholeD) (k : ℕ) (a : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D k a)
    {keysOf : LookupRecord → List (List Lkp.Keys)} {Np : Pieces} {sent : Nat} {s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hy : (batchTableRows (Cl := Claim) keysOf X.Y.k.oneTime Np sent).decide (show FirstState from a.2) rs gs = .ok s') : linOk X.Y.k.oneTime.codes X.Y.k.oneTime.lin = true :=
  linOk_of_yes (codes_at_reached₁ D k a h) hy

end Johnson.RunOne.KeyCodes

#print axioms Johnson.RunOne.KeyCodes.pile_reads
#print axioms Johnson.RunOne.KeyCodes.quiet_reads
#print axioms Johnson.RunOne.KeyCodes.linFits_of_yes
#print axioms Johnson.RunOne.KeyCodes.linOk_of_yes
#print axioms Johnson.RunOne.KeyCodes.first_growsBy
#print axioms Johnson.RunOne.KeyCodes.linOk_at_reached
