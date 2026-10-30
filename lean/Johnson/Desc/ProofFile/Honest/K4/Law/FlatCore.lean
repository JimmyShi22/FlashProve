-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatCore.lean: CONDITIONAL. Two definitions, and statements
with their proofs.

What is here. THE TWO TEXTS OF THE VERIFIER's MASKED SUMCHECK, TIED ON A TAPE. A state p of the flat
text (`Psc`, OnBytes/Model/Psc.lean) whose letters are written off a tape, as the library's laws on
the flat functions' returns write them, has the letters (`SameLetters`,
Johnson/Desc/Part/MaskedSumFlat.lean) of what the part's text (`hear`,
Johnson/Desc/Part/MaskedSum4.lean) hands back on rounds that hold what the tape holds. Both texts
are the verifier's: no prover is named.

  `TapeIs`, `TapeIs.tail`, `TapeIs.front`   the tape holds what the rounds hold
  `leading_of_scalars`, `varsRead_msOf`, `varsRead_lensT`   what the part's text has read, on the
     tape
  `pairOf`, `msOf_pairs`, `heard_of_tape`   **what `hear` hands back, in the tape's letters**; the
     last round holds the tape's end values
  `sameLetters_of_tape`   **the tie**: the letters

Limits. Premises: the tape begins with the sumcheck's rounds (the first message with the caller's
lead in front; a round for each variable; the further variable's; the end values'); p's seven
letters are those of these rounds, its target the public part of its claimed form at that ledger
(F.publicPart C = some T); the rounds' weights, read back off `msOf`, are ws (asked by name, though
it follows from the count of the rounds); `hear` returns, from the ledger at which p begins and at
p's claimed form, at a call with end values whose variables' weights are p's; THE TAPE HOLDS WHAT
THE ROUNDS HOLD (`TapeIs`: round by round, what was sent and what was sampled). The two running
claims are tied as readings, not as machine words. It stands on Johnson/Desc/Part/MaskedSumFlat.lean
(the two definitions), on Johnson/Desc/Part/MaskedSumJoint.lean with what it imports (where `hear`
returns; what was read), and on OnBytes/Desc/First/P1/LevelEnded.lean and
OnBytes/Desc/First/P1/TapeCut.lean.

Kin. The library ties a flat state to `heardAs` already, from another premise: `flatEnded`
(Johnson/Desc/Part/MaskedSumFlatProofs.lean, on which this file does not build): of `Ended`
(OnBytes/Tie/Pv/Psc/Run/PscSeam.lean: twelve equations on the state) and `LensT`; `level_ended`
(OnBytes/Desc/First/P1/LevelEnded.lean) has `Ended` where a product layer's flat function returns.
`sameLetters_of_tape` asks seven of the twelve, written on the tape's triples, has `LensT` from
`hear`'s return, and ties what `hear` itself hands back to `heardAs` (`heard_of_tape`), which
`flatEnded` does not.

No property is claimed.
-/
import Johnson.Desc.Part.MaskedSumFlat
import Johnson.Desc.Part.MaskedSumJoint
import OnBytes.Desc.First.P1.LevelEnded
import OnBytes.Desc.First.P1.TapeCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E mulE addE zeroE)
open OnBytes.Model (Reading World Aff Fork Psc)
open OnBytes.K.Kc (Tape FlatRound leading)
open OnBytes.Desc.First.P1 (msOf sentOf drawnOf claimAfter claimAfter_lib msOf_append_lit msOf_cons
  drop_length_add)
open VerifiableInference.Desc.Part.MaskedSum

/-! ## 1 The tape holds what the rounds hold -/

/-- Round by round: the tape's round number n has sent the leading scalars of the view's round
number n, and has sampled its elements. A tape that has no round number n counts as one that sent
nothing and sampled nothing. Behind a message's first item that is no scalar nothing is compared;
nor are the tape's rounds' names and two numbers, nor its rounds beyond the list. -/
def TapeIs (t : Tape) (rounds : List Fmt.RoundView) : Prop :=
  ∀ (n : ℕ) (r : Fmt.RoundView), rounds[n]? = some r →
    sentOf (t.drop n) = leading r.vals ∧ drawnOf (t.drop n) = r.drawn.elems.map E.ofTriple

/-- The tape behind its first round holds what the rounds behind the first hold. -/
theorem TapeIs.tail {t : Tape} {r : Fmt.RoundView} {rs : List Fmt.RoundView} (h : TapeIs t (r :: rs)) :
    TapeIs (t.drop 1) rs := by
  intro n r' hn
  have h1 := h (n + 1) r' (by simpa using hn)
  rw [List.drop_drop, Nat.add_comm 1 n]
  exact h1

/-- A tape that holds what a list of rounds holds also holds what the list's first stretch holds. -/
theorem TapeIs.front {t : Tape} {a b : List Fmt.RoundView} (h : TapeIs t (a ++ b)) : TapeIs t a := by
  intro n r hn
  have hl : n < a.length := (List.getElem?_eq_some_iff.mp hn).1
  exact h n r (by rw [List.getElem?_append_left hl]; exact hn)

/-- A message of scalars alone: its leading scalars are all. -/
theorem leading_of_scalars : ∀ (l : List Fmt.ItemValue) (s : List E), scalars l = some s → leading l = s
  | [], s, h => by
    have e : s = [] := (Option.some.inj h).symm
    rw [e]
    rfl
  | .e x :: l, s, h => by
    have h' : (scalars l).map (E.ofTriple x :: ·) = some s := h
    obtain ⟨s', hs', e⟩ := Option.map_eq_some_iff.mp h'
    rw [← e]
    show E.ofTriple x :: leading l = _
    rw [leading_of_scalars l s' hs']
  | .f _ :: _, _, h => by cases h
  | .word _ :: _, _, h => by cases h
  | .root _ :: _, _, h => by cases h
  | .answer _ :: _, _, h => by cases h

/-- What the part's text has read of the variables' rounds is what the flat text reads off the tape.
-/
theorem varsRead_msOf : ∀ (vs : List Var) (used : List Fmt.RoundView) (l : List (List E × E))
    (tp : Tape), VarsRead vs used l → TapeIs tp used → vs.length ≤ tp.length →
    l = (msOf (vs.map Var.weight) tp).map fun m => (m.2.1, m.2.2)
  | [], [], [], _, _, _, _ => by simp [msOf]
  | v :: vs, r :: used, (s, g) :: l, [], _, _, hl => by simp at hl
  | v :: vs, r :: used, (s, g) :: l, fr :: tp, hv, hT, hl => by
    obtain ⟨⟨h1, _, _, h4⟩, hv'⟩ := hv
    obtain ⟨a1, a2⟩ := hT 0 r rfl
    have b1 : fr.sent = s := by
      have : sentOf (fr :: tp) = fr.sent := rfl
      rw [← this, ← leading_of_scalars _ _ h1]
      exact a1
    have b2 : fr.drawn = [g] := by
      have : drawnOf (fr :: tp) = fr.drawn := rfl
      rw [← this, h4]
      exact a2
    rw [List.map_cons, msOf_cons, List.map_cons,
      ← varsRead_msOf vs used l tp hv' hT.tail (by simpa using hl), b1, b2]
    rfl
  | [], [], _ :: _, _, h, _, _ => h.elim
  | [], _ :: _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, h, _, _ => h.elim

/-- Each round that was read has as many scalars as its variable asks. -/
theorem varsRead_lensT : ∀ (vs : List Var) (used : List Fmt.RoundView) (l : List (List E × E)),
    (∀ v ∈ vs, 2 ≤ v.d) → VarsRead vs used l → LensT vs l
  | [], [], [], _, _ => trivial
  | v :: vs, r :: used, (s, g) :: l, hd, hv => by
    have h2 := hd v (by simp)
    exact ⟨by rw [hv.1.2.1]; omega,
      varsRead_lensT vs used l (fun u hu => hd u (by simp [hu])) hv.2⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

/-! ## 2 What `hear` hands back, in the tape's letters -/

/-- What a round of the tape sent, and the first element that it sampled; 0 if it sampled none. -/
def pairOf (r : FlatRound) : List E × E := (r.sent, r.drawn.headD zeroE)

/-- The flat text's rounds under as many weights, without the weights. -/
theorem msOf_pairs : ∀ (ws : List OnBytes.Psc.Weight) (rs : List FlatRound),
    ws.length = rs.length → ((msOf ws rs).map fun m => (m.2.1, m.2.2)) = rs.map pairOf
  | [], [], _ => by simp [msOf]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | w :: ws, r :: rs, h => by
    rw [msOf_cons, List.map_cons, List.map_cons, msOf_pairs ws rs (by simpa using h)]
    rfl

/-- **What `hear` hands back on rounds that hold what a tape holds, in the tape's letters**
(`heardAs`, Johnson/Desc/Part/MaskedSumFlat.lean). front: the caller's lead as sent. vals: the end
values as sent. -/
theorem heard_of_tape {C : Aff} {T mu0 eps beta : E} {front sentY vals : List E}
    {rs : List FlatRound} {rest t : Tape} {nm0 nmY nmV : Option String} {z0 w0 zY wY zV wV : ℕ}
    {dY n : ℕ} {F G' : Fork}
    (ht : t = ⟨nm0, z0, w0, front ++ [mu0], [eps]⟩ ::
      (rs ++ ⟨nmY, zY, wY, sentY, [beta]⟩ :: ⟨nmV, zV, wV, vals, []⟩ :: rest))
    (hTp : F.publicPart C = some T) (vs : List Var) (hvl : vs.length = rs.length)
    {rounds : List Fmt.RoundView} {h : Heard}
    (hh : hear C ⟨front.length, vs, some ⟨dY, n⟩⟩ F rounds = some (h, G'))
    (hT : TapeIs t rounds) :
    h = heardAs C T mu0 eps F.next vs (rs.map pairOf) dY sentY beta ∧
      LensT (vs ++ [Var.point zeroE (dY + 1)]) (rs.map pairOf ++ [(sentY, beta)]) ∧
      ∃ rv, rounds.getLast? = some rv ∧ scalars rv.vals = some vals := by
  obtain ⟨hsk, T', R, hT', hR, hh', _⟩ := hear_spec hh
  have eT : T' = T := Option.some.inj (hT'.symm.trans hTp)
  obtain ⟨r0, used, rv, front', hro, hS0, hfl, hVR, hSV⟩ := readAll_spec hR
  rw [hro] at hT
  -- the first round
  obtain ⟨c1, c2⟩ := hT 0 r0 rfl
  rw [leading_of_scalars _ _ hS0.1, ht] at c1
  rw [← hS0.2.2.2, ht] at c2
  have emu : R.mu = mu0 := by
    have c1' : front ++ [mu0] = front' ++ [R.mu] := c1
    exact (List.head_eq_of_cons_eq (List.append_inj' c1' rfl).2).symm
  have eeps : R.eps = eps := by
    have : [eps] = [R.eps] := c2
    exact (List.head_eq_of_cons_eq this).symm
  -- the variables' rounds
  have htl : t.drop 1 = rs ++ ⟨nmY, zY, wY, sentY, [beta]⟩ :: ⟨nmV, zV, wV, vals, []⟩ :: rest := by
    rw [ht]
    rfl
  have hwl : (vs.map Var.weight).length = rs.length := by rw [List.length_map, hvl]
  have hRr : R.rounds = rs.map pairOf ++ [(sentY, beta)] := by
    rw [varsRead_msOf _ used R.rounds (t.drop 1) hVR hT.tail.front (by
      rw [htl, List.length_append, List.length_append, hvl]
      simp), List.map_append, htl]
    show ((msOf (vs.map Var.weight ++ [Var.weight (Var.point zeroE (dY + 1))]) _).map _) = _
    rw [msOf_append_lit _ _ _ _ _ _ _ _ _ hwl, List.map_append, msOf_pairs _ _ hwl]
    rfl
  -- the end values
  have hul : used.length = rs.length + 1 := by
    rw [(VarsRead.length hVR).1, List.length_append, hvl]
    rfl
  have hrv : (r0 :: (used ++ [rv]))[rs.length + 2]? = some rv := by
    rw [show rs.length + 2 = (rs.length + 1) + 1 by omega, List.getElem?_cons_succ, ← hul,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hvv : vals = R.values := by
    have c3 := (hT (rs.length + 2) rv hrv).1
    rw [leading_of_scalars _ _ hSV.1, show rs.length + 2 = 1 + (rs.length + 1) by omega,
      ← List.drop_drop, htl, drop_length_add] at c3
    exact c3
  refine ⟨?_, ?_, rv, by rw [hro, ← List.cons_append, List.getLast?_concat],
    by rw [hvv]; exact hSV.1⟩
  · rw [hh', hRr, emu, eeps, eT, List.map_append]
    rfl
  · rw [← hRr]
    exact varsRead_lensT _ used _ (two_le_allK hsk) hVR

/-! ## 3 The tie -/

/-- **A state of the flat text whose letters are written off a tape has the letters of what `hear`
hands back on rounds that hold what the tape holds.** front: the caller's lead as sent. ws: the
variables' weights. vals: the end values as sent. -/
theorem sameLetters_of_tape {p : Psc} {C : Aff} {T mu0 eps beta : E} {front sentY vals : List E}
    {rs : List FlatRound} {rest t : Tape} {nm0 nmY nmV : Option String} {z0 w0 zY wY zV wV : ℕ}
    {ws : List OnBytes.Psc.Weight} {dY n : ℕ} {F G' : Fork}
    (ht : t = ⟨nm0, z0, w0, front ++ [mu0], [eps]⟩ ::
      (rs ++ ⟨nmY, zY, wY, sentY, [beta]⟩ :: ⟨nmV, zV, wV, vals, []⟩ :: rest))
    (hwl : ws.length = rs.length)
    (a1 : (msOf ws rs).map (·.1) = ws)
    (hvars : p.vars.toList = ws ++ [OnBytes.Psc.Weight.atZero (dY + 1)])
    (hr : p.r.toList =
      (msOf ws rs ++ [(OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)]).map (·.2.2))
    (hclaim : p.claim =
      claimAfter (msOf ws rs ++ [(OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)])
        (addE mu0 (mulE eps T)))
    (htar : p.target = T) (heps : p.eps = eps) (hstart : p.start = C) (hfirst : p.first = F.next)
    (hTp : F.publicPart C = some T) (vs : List Var) (hk : vs.map Var.weight = ws)
    {rounds : List Fmt.RoundView} {h : Heard}
    (hh : hear C ⟨front.length, vs, some ⟨dY, n⟩⟩ F rounds = some (h, G'))
    (hT : TapeIs t rounds) :
    SameLetters p h ∧ ∃ rv, rounds.getLast? = some rv ∧ scalars rv.vals = some vals := by
  obtain ⟨eh, hL, hv⟩ := heard_of_tape ht hTp vs (by rw [← hwl, ← hk, List.length_map]) hh hT
  have hw : (vs ++ [Var.point zeroE (dY + 1)]).map Var.weight =
      ws ++ [OnBytes.Psc.Weight.atZero (dY + 1)] := by
    rw [List.map_append, hk]
    rfl
  have hp : (msOf ws rs ++ [(OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)]).map
      (fun m => (m.2.1, m.2.2)) = rs.map pairOf ++ [(sentY, beta)] := by
    rw [List.map_append, msOf_pairs ws rs hwl]
    rfl
  refine ⟨?_, hv⟩
  rw [eh]
  refine ⟨hstart, htar, heps, hfirst, ?_, ?_, ?_⟩
  · rw [hvars]
    exact hw.symm
  · rw [hr]
    show _ = (rs.map pairOf).map (·.2) ++ [beta]
    have e := congrArg (List.map (·.2)) hp
    rw [List.map_map] at e
    exact e.trans (by rw [List.map_append]; rfl)
  · intro K _ ρ
    show ρ.val p.claim = ρ.val (after (vs ++ [Var.point zeroE (dY + 1)])
      (rs.map pairOf ++ [(sentY, beta)]) (addE mu0 (mulE eps T)))
    rw [after_read ρ _ _ _ _ hL rfl, hw, hclaim, claimAfter_lib, List.map_append, a1, hp]
    rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.TapeIs
#print axioms ProofFile.Honest.K4.TapeIs.tail
#print axioms ProofFile.Honest.K4.TapeIs.front
#print axioms ProofFile.Honest.K4.leading_of_scalars
#print axioms ProofFile.Honest.K4.varsRead_msOf
#print axioms ProofFile.Honest.K4.varsRead_lensT
#print axioms ProofFile.Honest.K4.pairOf
#print axioms ProofFile.Honest.K4.msOf_pairs
#print axioms ProofFile.Honest.K4.heard_of_tape
#print axioms ProofFile.Honest.K4.sameLetters_of_tape
