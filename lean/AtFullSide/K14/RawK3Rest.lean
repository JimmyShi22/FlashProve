-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawK3Rest.lean: OF THE RAW BOOK's ENTRIES AT THE WRITTEN DESCRIPTION WP (rawAheadW,
AtFullSide/K14/RawAheadWritten.lean) THE EIGHT WRITTEN PIECES NAME NONE OF THE FIFTY PLACES OF THE
KIND K3 (k3SitesW, AtFullSide/K14/RawK3Sites.lean) AS A SPENDER's; AND rawAheadW IS THE STRETCHES'
ENTRIES WITH NINE PIECES BEHIND THEM. One definition; statements with their proofs; two evaluations
in Lean's kernel on written data.

Limits. OF rawSegW, THE CARRYING ENTRIES OF THE CHAIN OF SEGMENTS (5,130), NOTHING IS SHOWN HERE:
k3Rest_none takes it as a premise. Nothing on the stretches. WP's own limit stands. Numbers and
addresses on public data: nothing on soundness, completeness or hiding.

  rawRestW        rawAheadW's nine pieces behind the stretches' entries, in the maker's order
  rawAhead_split  rawAheadW = the stretches' entries ++ rawRestW
  rawRest_all     a test of the form "all" accepts rawRestW if it accepts rawSegW and the written
                  pieces (rawShortW, AtFullSide/K14/RawEntriesKit.lean)
  k3Short_none    **no entry of the written pieces names one of the fifty places as its spender's**
  k3None_bent     A NEGATIVE TEST ON PUBLIC WRITTEN NUMBERS: see its docstring
  k3Rest_none     the same of rawRestW. CONDITIONAL: on rawSegW

OPTIONS ARE RAISED in front of the two evaluations: maxRecDepth to 1000000 (no lower number was
tried). What is assumed. Nothing beside each statement's own premises.
-/
import AtFullSide.K14.RawK3Sites
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14

/-- rawAheadW's nine pieces behind the stretches' entries. -/
def rawRestW : List Ahead :=
  foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten] ++ rawSegW ++ rawCarriesFoldedW ++
    rawCarriesOmegaW ++ rawCarriesWW ++ rawOwnCarryW

/-- The raw book's entries are the stretches' entries with these behind them. -/
theorem rawAhead_split : rawAheadW = rawWantsW.map (·.entry) ++ rawRestW := by
  unfold rawAheadW rawRestW
  simp only [List.append_assoc]

/-- A test of the form "all" accepts rawRestW if it accepts rawSegW and the written pieces. -/
theorem rawRest_all (t : Ahead → Bool) (hs : rawSegW.all t = true)
    (hr : rawShortW.all t = true) : rawRestW.all t = true := by
  unfold rawShortW at hr
  unfold rawRestW
  simp only [List.all_append, Bool.and_eq_true] at hr ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hr
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hs⟩, h5⟩, h6⟩, h7⟩, h8⟩

set_option maxRecDepth 1000000 in
/-- **No entry of the eight written pieces names one of the fifty places as its spender's.** -/
theorem k3Short_none :
    rawShortW.all (fun e => !k3SitesW.any fun s => s.at_.place == e.spender.place) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- BENT: the place ⟨1, some 0, 11, .K10⟩, at which link 0's fold stands, is laid in among the
fifty: a written entry of the folds names it as its spender's, and the test rejects. -/
theorem k3None_bent :
    rawShortW.all (fun e =>
      !((⟨⟨⟨1, some 0, 11, .K10⟩, k3Face 30 19, 0⟩, 0, ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨23214, 0⟩⟩ ::
        k3SitesW).any fun s => s.at_.place == e.spender.place)) = false := by
  decide +kernel

/-- The same of all nine pieces. CONDITIONAL: hs. -/
theorem k3Rest_none
    (hs : rawSegW.all (fun e => !k3SitesW.any fun s => s.at_.place == e.spender.place) = true) :
    rawRestW.all (fun e => !k3SitesW.any fun s => s.at_.place == e.spender.place) = true :=
  rawRest_all _ hs k3Short_none

end AtFullSide.K14

#print axioms AtFullSide.K14.rawAhead_split
#print axioms AtFullSide.K14.rawRest_all
#print axioms AtFullSide.K14.k3Short_none
#print axioms AtFullSide.K14.k3None_bent
#print axioms AtFullSide.K14.k3Rest_none
