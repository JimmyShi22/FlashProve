-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ReturnTied.lean: kind K13, the members' batching: WHERE THE JOINED
SUB-PROTOCOL (`atM3`) RETURNS, THE ELEMENTS x AND eps AND THE POINT OF THE SUMCHECK's RUN ARE WHAT
ITS ROUNDS SAMPLED. Statements with their proofs.

Why. `atM3_return_row` (ShapeSim.lean of this folder) yields the row that is laid as `Batt.rowOf` at
what the sumcheck's run returns, at some x and some value hd of what was heard (`Psc.Heard`): these
two stand under "there are", tied to no round. The library's `batt_ok`
(Johnson/Desc/K13/Law/Law.lean) has the ties. Here the same statement keeps them, read as one
equation on what the rounds sampled (`sampledRV`, SampledRV.lean).
Kin in the library: Johnson/Desc/K13/Law/View.lean (`oneDrawn_read`, `oneRound_read`, `rounds_read`,
`whole_read`) reads the same three readers at the rounds of a TYPED transcript, into the field of
the library's laws. Here: at any rounds, in the programs' own elements.
Main names:
  `oneDrawn_sampled`, `oneRound_sampled`, `mapM_oneRound_sampled`, `heard_sampled`: the text's
    readers.
  `atM3_return_tied`: **`atM3_return_row`'s statement, and: the rounds that the batching is handed
    (the first 2 + kCol) sampled one element each: x, then hd's eps, then the challenges of hd's
    rounds in their order.**

What is not claimed. One direction: from a return. Which challenges of a proof file these rounds'
are. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.ShapeSim
import Johnson.Desc.K13.Honest.SampledRV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- The reader of one sampled element. -/
theorem oneDrawn_sampled {name : String} {r : Fmt.RoundView} {x : E} (h : oneDrawn name r = .ok x) :
    r.drawn.elems.map E.ofTriple = [x] := by
  unfold oneDrawn at h
  have h' := Law.there_ok.1 h
  split at h'
  · rename_i y hy
    rw [hy, ← Option.some.inj h']
    rfl
  · cases h'

/-- The reader of a round in which elements are sent and one is sampled. -/
theorem oneRound_sampled {r : Fmt.RoundView} {a : List E × E} (h : oneRound r = .ok a) :
    r.drawn.elems.map E.ofTriple = [a.2] := by
  unfold oneRound at h
  obtain ⟨q, _, h⟩ := Law.bind_ok.1 h
  obtain ⟨x, hx, h⟩ := Law.bind_ok.1 h
  rw [← Law.pure_ok.1 h]
  exact oneDrawn_sampled hx

/-- That reader over a list of rounds. -/
theorem mapM_oneRound_sampled : ∀ (l : List Fmt.RoundView) (inX : List (List E × E)),
    l.mapM oneRound = .ok inX → sampledRV l = inX.map fun p => [p.2]
  | [], inX, h => by
    rw [List.mapM_nil] at h
    rw [← Law.pure_ok.1 h]
    rfl
  | r :: l, inX, h => by
    rw [List.mapM_cons] at h
    obtain ⟨a, ha, h⟩ := Law.bind_ok.1 h
    obtain ⟨b, hb, h⟩ := Law.bind_ok.1 h
    rw [← Law.pure_ok.1 h]
    show r.drawn.elems.map E.ofTriple :: sampledRV l = [a.2] :: b.map fun p => [p.2]
    rw [oneRound_sampled ha, mapM_oneRound_sampled l b hb]

/-- What is heard in the sumcheck's rounds: eps is what the first sampled, the rounds' challenges
what the further ones did. -/
theorem heard_sampled {l : List Fmt.RoundView} {hd : Psc.Heard} (h : heard l = .ok hd) :
    sampledRV l = [hd.eps] :: hd.rounds.map fun p => [p.2] := by
  cases l with
  | nil => cases h
  | cons r₀ l =>
    unfold heard at h
    obtain ⟨a, ha, h⟩ := Law.bind_ok.1 h
    obtain ⟨mu, _, h⟩ := Law.bind_ok.1 h
    obtain ⟨inX, hx, h⟩ := Law.bind_ok.1 h
    rw [← Law.pure_ok.1 h]
    show r₀.drawn.elems.map E.ofTriple :: sampledRV l = [a.2] :: inX.map fun p => [p.2]
    rw [oneRound_sampled ha, mapM_oneRound_sampled l inX hx]

variable {Cl : Type}

/-- **Where the joined sub-protocol returns**: `atM3_return_row`'s statement, with x, hd's eps and
the challenges of hd's rounds tied to what the batching's rounds sampled. What hd holds of what was
sent stays under "there are". -/
theorem atM3_return_tied {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ (t : List ℕ × St) (msg : Array OracleNotice) (x : E) (hd : Psc.Heard) (o : Psc.Out),
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ Batt.fits P.lin.kCol s.out.pending = true ∧
      Psc.run (Batt.claimOf s.out.pending x) (Batt.summandOf s.out.pending x)
        (t.1.map fun i => ⟨s.out.indexMasks, i⟩) hd = some o ∧
      s' = withClaim s t.2.st msg (Batt.rowOf s.out.pending o) ∧
      sampledRV (rs.take (battRounds P).length) =
        [x] :: [hd.eps] :: hd.rounds.map fun p => [p.2] := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ (rs.take (battRounds P).length) _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  have he := frontB_ok atS P h1
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  have h3' := h3
  simp only [quietB, still, quiet_is, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok,
    Lens.part] at h3'
  obtain ⟨p', hp', _, _, msg, ⟨_, _, hm⟩, rfl⟩ := h3'
  obtain ⟨f, -, -, hfin, -⟩ := atM3_rec h
  have e1 : atS.enter s = some s.enterMem := by simp only [atS, hfin]
  rw [e1] at he
  have e2 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } := by
    rw [← Option.some.inj he]
    simp only [S.enterMem, hfin]
  subst e2
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  obtain ⟨r, rs', x, t, hd, o, hrs, _, b2, bx, _, b4, bh, b6, _, rfl⟩ := batt_ok hb
  refine ⟨t, msg, x, hd, o, b4, hm, b2, b6, rfl, ?_⟩
  rw [hrs]
  show r.drawn.elems.map E.ofTriple :: sampledRV rs' = _
  rw [oneDrawn_sampled bx, heard_sampled bh]

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.oneDrawn_sampled
#print axioms VerifiableInference.Desc.K13.Honest.oneRound_sampled
#print axioms VerifiableInference.Desc.K13.Honest.mapM_oneRound_sampled
#print axioms VerifiableInference.Desc.K13.Honest.heard_sampled
#print axioms VerifiableInference.Desc.K13.Honest.atM3_return_tied
