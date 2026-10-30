-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean: THE LOOKUP ON THE DIGITS AT THE OUTPUT HEAD'S
SEGMENT, WITH THE QUIET STEP BEHIND IT: WHAT AN ACCEPT OF ITS DECISION LEAVES AND GIVES: for a walk
over reached states, which hands on decisions, not a piece's acceptances.

Whose. The sub-protocol and every law that is called here are the lookups' authors'. Their own
joining (k3_digits_keptW) stands at a piece; the two proofs here follow theirs line by line
(theStated_yes_digits, Johnson/Desc/First/Look/K3DigitsSeatedYes.lean; k3_digits_keptW) at the
decision.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  keptW_digits_bare: an accept of the bare lookup (K3.block at the digits' seat), from a state in
      the head's segment whose ledger has its sizes: KeptW
      (Johnson/Desc/Kinds/Law/WeightAtSame.lean).
  stated_yes_head: an accept of K3.theStated's value at the digits' address OF THE HEAD'S SEGMENT is
      an accept of the bare lookup and then of K3.quietHead. (The authors' theStated_yes_digits ends
      in "or no quiet step": at the head's segment that arm is empty.)
  digits_at_head: the two together with Johnson/Desc/Kinds/Law/QuietHeadGives.lean: KeptW from the
      state in front to the state behind; the covered positions are read behind; the claim that lies
      behind is the one that weightsClaim makes.

Every letter under "there is": stated_yes_head: P, sent, laid: by the address (the authors'
theOwn_is); n, gs': the part of the rounds and columns that the bare lookup takes; m: by the bare
lookup's equation. digits_at_head: cov, t: by quietHead's two reads.
What it does not say. That the sub-protocol accepts. hOk (its test on the plan), hH (the segment is
the head's), ho, hz (the state in front stands in the head's segment; its ledger has its sizes) are
premises. Nothing on soundness.
-/
import Johnson.Desc.First.Look.K3DigitsHeadStays
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.Kinds.Law.QuietHeadGives
import Johnson.Desc.Kinds.Law.KeptWLegs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The bare lookup on the digits, at the head's segment.** -/
theorem keptW_digits_bare {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl))
    {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    (h : (K3.block (K3.seatDigits claim) piece laid before p guests).decide s rs cols = .ok s')
    {o : HeadOwn} (ho : s.here = .head o) (hz : OnBytes.PscRun.Sized o.F) : KeptW s s' := by
  obtain ⟨o', h1, k⟩ := k3_digits_headStays claim piece laid before p guests s s' rs cols h o ho
  have K := k o.tl o.F o.claim
  have T := k3_digits_sameBut claim piece laid before p guests s s' rs cols h
  obtain ⟨F, y, hF, hn, e, hE⟩ :=
    decide_exact (K3.seatDigits claim) piece laid before p guests s s' rs cols h
  have hF0 : s.fork? = some F := hF
  have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have hG : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have eo : o'.opened = o.opened := congrArg (·.opened) K
  cases hop : o.opened with
  | false => simp [S.fork?, ho, hop] at hF0
  | true =>
    have eF : o.F = F := by simpa [S.fork?, ho, hop] using hF0
    have eG : o'.F = y.2 := by simpa [S.fork?, h1, eo.trans hop] using hG
    refine ⟨o, o', ho, h1, congrArg (·.x) K, congrArg (·.squaresP) K, eo,
      congrArg (·.lookHeard) K, by rw [T.out], T.req, ?_⟩
    rw [eF, eG]
    exact (hE (eF ▸ hz)).2

/-- **At the head's segment the quiet step is there.** -/
theorem stated_yes_head {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (hH : K3.isHead X i = true)
    (s c : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok c) :
    ∃ P sent laid n gs' m,
      (K3.block (K3.seatDigits claim) a.piece laid sent P []).decide s (rs.take n) gs' = .ok m ∧
      K3.quietHead X m = .ok c := by
  obtain ⟨B₁, hB₁, -, e2, -, e4⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', -, -, -, -, r2, -, hpl⟩ :=
    K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | false => exact absurd (hpc'.symm.trans hpc) (pieceAt_neD X i)
  | true =>
    rw [e2] at hd
    rw [e4] at hOk
    have hq : (a.link.bind fun j => K3.quietAt X j (a.piece == K3.pieceAt X j true)) =
        some (K3.quietHead X) := by
      simp [hi, hpc, K3.quietAt, hH]
    rcases hW with ⟨hn, -⟩ | ⟨f, hf, rfl⟩
    · rw [hq] at hn
      cases hn
    · obtain rfl : K3.quietHead X = f := Option.some.inj (hq.symm.trans hf)
      have hOk' : b.planOk = true := by
        have h0 : (b.planOk && true) = true := hOk
        simpa using h0
      have hd' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
          (fun s' => K3.quietHead X s') = .ok c := hd
      cases hb' : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
      | error e =>
        rw [hb'] at hd'
        cases hd'
      | ok m =>
        rw [hb'] at hd'
        rw [r2] at hb'
        exact ⟨P, sent, laid, _, _, m, K3.Law.blockVia_decide (hpl hOk') hb', hd'⟩

/-- **THE WHOLE SUB-PROTOCOL AT THE HEAD'S DIGITS, AT ITS DECISION.** -/
theorem digits_at_head {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (hH : K3.isHead X i = true)
    (s c : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok c) {o : HeadOwn} (ho : s.here = .head o)
    (hz : OnBytes.PscRun.Sized o.F) :
    KeptW s c ∧ ∃ (cov : Head.Covered) (t : Head.Tables), c.covered X.T X.P.h.V = .ok cov ∧
      ∀ o' x claim', c.here = .head o' → o'.x = some x → o'.claim = some claim' →
        First.Look.weightsClaim (runAt X cov x t) X.layers.wsLay = .ok claim' := by
  obtain ⟨P, sent, laid, n, gs', m, h1, h2⟩ :=
    stated_yes_head claim readers X codes shape a B h hOk i hi hpc hH s c rs gs hd
  obtain ⟨k2, rest⟩ := quietHead_gives X h2
  exact ⟨(keptW_digits_bare claim _ _ _ _ _ h1 ho hz).trans k2, rest⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_digits_bare
#print axioms VerifiableInference.Desc.Kinds.Head.Law.stated_yes_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.digits_at_head
