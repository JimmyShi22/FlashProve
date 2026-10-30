-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LedgerThr.lean: the honest side of the kind "lookup"
(K3): THE LEDGER THAT THE STATE IN FRONT HOLDS IS AS THE LOOKUP'S LAWS ASK IT: from the first
chain's thread in front of the description's own member at a lookup's place. For whoever opens
`LeftAt` (Honest/K3/Law/Thread/LeftThr.lean), which binds that ledger by "the seat reads it
at the state".

  `ledger_thr`   CONDITIONAL ON `SiteAt` (Honest/K3/Law/Thread/SiteThr.lean) and the thread in
                   front: every ledger that the seat reads at the state meets `LedgerIn`
                   (Honest/K3/Law/Top.lean) at the site's face and the parameters' first slot

No instance of `SiteAt` is exhibited in this file; under the head and `SiteRest`:
`siteAt_lettersHead` (SiteAtHead.lean).

`SiteAt` has the field half: the list of halves holds, at the site's place, the elder row `proverSideOfLookupInChainAtOneOwner`
at these summands. Who pays the field, each at the fast summands and under hypotheses on the list:
where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean
[not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it
holds a lot with the halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like`
(HalfOfLotLike.lean [not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. On the verifier's side alone. Nothing on soundness, completeness or any other property
of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look (Sent placeAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3Letters)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}
  {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site} {lot : Block FS ProofFile.Cl}
  {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL ON `SiteAt` and the thread in front: the ledger that the seat reads at the state
in front has its arrays' sizes, counts the parameters' first slot, has room for the lookup's hidden
values, and these are free.** No instance of these hypotheses is exhibited in this file. -/
theorem ledger_thr (hS : SiteAt L b Z Bs ch s lot J wit D Lk) {k : Coins Bk} {st : FS}
    {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env} (hA : Thr L.thread b k st m E) (F : Fork)
    (hF : (seatOf K3Lot.ofForm s.digits).fork st = some F) : LedgerIn s.at_.face s.p.first F := by
  have hs' := hS.site
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨f1, _, f3, f4, _, _, _, _⟩ := site_facts _ _ x s hsx
  have hp : placeAt Z.p.X s.link s.digits = some s.p := by rw [f3, f4]; exact f1
  obtain ⟨hh, F', Fo⟩ := front_seatOf K3Lot.ofForm (onIn_thr L hS.k3At hp hS.lookIn hA)
  rw [placeAt_digits hp] at Fo
  obtain rfl : F' = F := Option.some.inj (Fo.fork.symm.trans hF)
  obtain ⟨rfl, hf⟩ := front_face Z s hS.site Fo
  rw [hf]
  exact ledgerIn_of_front Fo

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ledger_thr
