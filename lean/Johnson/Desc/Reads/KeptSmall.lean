-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeptSmall.lean: two more of the texts that stand between the fifth place of the
output head's segment and the run "policy" keep all that `KeptAll` (Reads/RowAtSeat.lean) asks: the
sub-protocol in which the approximate range proof draws its combination, and the output head's own
runs of claims.

What is shown. Steps: they speak of the written sub-protocol `K8.whole`
(Johnson/Desc/First/K8/Whole.lean) and of `runsBy` (Johnson/Desc/Kinds/HeadFrame.lean) at the seat
`seatAt` (Johnson/Stored/HeadSeatAt.lean).
  `keptAll_putTl`: writing the approximate range proof's part of the state keeps all ten fields,
    where what is written has the same matrices, list of tables and number of matrices.
  `keptAll_small`: **where the approximate range proof's sub-protocol accepts, `KeptAll` holds from
    the state in front to the state behind.** By the library's law on what its accepting means
    (`decide_atS_iff`, Johnson/Desc/First/K8/HearMeans.lean).
  `run_returns`: **where a run of the output head's own claims accepts, it returns the state as it
    stood.** So the run "norm" gives `KeptAll`.

Limits. Still owed between the two places: the lookup on the digits; the merge; the runs "objects",
"guests" and "join" of the lookup on the calls. Nothing on soundness.


-/
import Johnson.Desc.Reads.KeptCommit
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head

/-- Writing the approximate range proof's part of the state. -/
theorem keptAll_putTl (i : ℕ) (s : S) (tl tl' : HTailF2) (ht : s.tl? = some tl)
    (h1 : tl'.mats = tl.mats) (h2 : tl'.funs = tl.funs) (h3 : tl'.NM = tl.NM) :
    KeptAll i s (s.putTl tl') := by
  refine ⟨?_, ?_, fun o ho => ?_⟩
  · unfold S.putTl
    split <;> (try split) <;> rfl
  · unfold S.putTl
    split <;> (try split) <;> rfl
  · unfold S.tl? at ht
    rw [ho] at ht
    have ht' : (if o.opened = true then some o.tl else none) = some tl := ht
    by_cases hop : o.opened = true
    · rw [if_pos hop] at ht'
      have e : o.tl = tl := Option.some.inj ht'
      refine ⟨{ o with tl := tl' }, ?_, rfl, rfl, rfl, rfl, h1.trans (by rw [e]),
        h2.trans (by rw [e]), h3.trans (by rw [e]), rfl⟩
      unfold S.putTl
      simp [ho, hop]
    · rw [if_neg hop] at ht'
      cases ht'

/-- **Where the approximate range proof's sub-protocol accepts, KeptAll holds.** -/
theorem keptAll_small (p : VerifiableInference.Desc.First.K8.ParW) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (hd : (VerifiableInference.Desc.First.K8.whole p).decide s rs gs = .ok s') (i : ℕ) :
    KeptAll i s s' := by
  have hd' : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Claim)
      VerifiableInference.Desc.First.K8.atS p.toPar).decide s rs gs = .ok s' := hd
  obtain ⟨r, rfl⟩ := VerifiableInference.Desc.First.K8.decide_one _ p.toPar s s' rs gs hd'
  obtain ⟨tl, ht, hm⟩ := (VerifiableInference.Desc.First.K8.decide_atS_iff p.toPar s s' r gs).1 hd'
  rw [hm.2.2.2.2.2.2.2.2]
  exact keptAll_putTl i s tl _ ht rfl rfl rfl

/-- **A run of the output head's own claims that accepts returns the state as it stood.** -/
theorem run_returns {Cl : Type} {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Cl} {p : Par}
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ)
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ runsBy names runs keys toCl p (seatAt h iU3)) {n : ℕ} {s : S} {y : List Cl × S}
    (hr : c.2 n s = .ok y) : y.2 = s := by
  unfold runsBy at hc
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc
  dsimp only at hr
  obtain ⟨⟨g, b, x⟩, _, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨fs, _, hr⟩ := ReadsQuiet.bind_ok hr
  have e := congrArg Prod.snd (Except.ok.inj hr)
  rw [← e]
  show (if names.head? == some name then (seatAt h iU3).setKeyForms s (keys g b x) else s) = s
  split <;> rfl

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.keptAll_putTl
#print axioms VerifiableInference.Reads.AtSeat.keptAll_small
#print axioms VerifiableInference.Reads.AtSeat.run_returns
