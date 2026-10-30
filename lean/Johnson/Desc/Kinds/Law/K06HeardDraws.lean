-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06HeardDraws.lean: WHAT THE OUTPUT HEAD'S HEARING RETURNS AS CHALLENGES IS,
COORDINATE BY COORDINATE, WHAT THE ROUNDS SAMPLED.
WHAT IT IS NOT. CONDITIONAL: THAT THE HEARING RETURNS IS A PREMISE; so is, in hear_pieces and in
hear_draws, THAT THE LEDGER IN FRONT IS WELL LAID (WellLaid F): IT IS SPENT ON NOTHING THAT THESE
TWO KEEP: the library's hear_parts and norm_parts ask it, and spend it on their own conclusions that
the ledgers behind are well laid; hear_pieces calls these two and throws the conclusions away;
hear_draws takes it through Law/K06HearEight.lean's hear_eight, where it is of substance for the
clauses on the ledgers, which hear_draws throws away: it narrows the two and buys nothing; to drop
it the two lemmas' proofs would have to be typed anew. Nothing on any value that was sent, on the
ledger, on whether the verifier accepts, on soundness, on completeness or on what a proof hides. OF
ANY RETURN, not of an honest run's: no prover is in this file.
  firstDrawn r    the first element that the round r sampled; 0 where it sampled none.
  vars_chal       the variables' rounds, as the part's reader read them: each challenge is the
                  round's first sampled element.
  heardBy_draws   where heardBy returns on its own rounds: the sumcheck's challenges are the first
                  sampled elements of the rounds number 1 .. z.size (round 0 samples an element that
                  is no coordinate; the round in the further variable and the last are left out).
  sumcheck_draws, level_draws   the same at the verifier's two texts; of a level also: the element
                  that it hands down is the first sampled element of its last round.
  batch_draws     the batching element is the round's first sampled element.
  hear_pieces     WHERE THE ONE HEARING RETURNS, USING THE ROUNDS UP, the rounds ARE eight pieces in
                  a row (four of them one round each): six of the table's lengths, the last two by
                  the number of zt's coordinates (the table's where that is lt, which is no premise
                  here).
  hear_draws      THE TOP: at these pieces: the point on the positions is all that round 0 sampled;
                  the two batching elements, the element that ends the first sumcheck and the four
                  sumchecks' challenges are the first sampled elements of their rounds.
CALLED, OF THE LIBRARY: heardBy_spec, heardBy_cut, hear_spec, readAll_spec, batch_one, level_length,
sumcheck_spec, zS_size, hear_parts, norm_parts, Part.MaskedSum.roundOf_spec, and the small lemmas on
a hearing's steps; of Law/K06HearEight.lean: point_spec, hear_eight.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06HearEight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)
open Part.MaskedSum (Var VarsRead readAll challenges)

/-- The first element that a round sampled; 0 where it sampled none. -/
def firstDrawn (r : Fmt.RoundView) : E := (r.drawn.elems.head?.map E.ofTriple).getD zeroE

/-- Each variable's challenge is its round's first sampled element. -/
theorem vars_chal : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → l.map (·.2) = used.map firstDrawn
  | [], [], [], _ => rfl
  | _ :: _, r :: _, (_, g) :: _, h => by
    have e : g = firstDrawn r := by
      have h4 : [g] = r.drawn.elems.map E.ofTriple := h.1.2.2.2
      unfold firstDrawn
      rw [← List.head?_map, ← h4]
      rfl
    rw [List.map_cons, List.map_cons, vars_chal h.2, e]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- **Where heardBy returns on its own rounds, the sumcheck's challenges are what the variables'
rounds sampled.** -/
theorem heardBy_draws {lead : Nat} {C : Array Hid → Form} {z : Point} {e : Nat} {F0 F1 : Fork}
    {rounds : List Fmt.RoundView} {cA : Array Hid} {S : Sum}
    (hv : heardBy lead C z e F0 rounds = some ((cA, S), F1, [])) :
    S.r = (((rounds.drop 1).take z.size).map firstDrawn).toArray := by
  obtain ⟨_, _, _, h, _, _, _, _, a4, _, _, hS⟩ := heardBy_spec hv
  obtain ⟨_, _, R, _, hR, hh, _⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, rfl, _, _, sv, _⟩ := Part.MaskedSum.readAll_spec
    (show readAll ⟨lead, z.toList.map (.point · 3), some ⟨2, e⟩⟩ rounds = some R from hR)
  have hu : used.length = z.size + 1 := by
    rw [sv.length.1, List.length_append, List.length_map, Array.length_toList]
    rfl
  rw [hS]
  show (challenges (callOf lead z e) h).toArray = _
  congr 1
  show h.r.take (z.toList.map (Var.point · 3)).length = _
  rw [hh]
  show (R.rounds.map (·.2)).take _ = _
  rw [vars_chal sv, List.length_map, Array.length_toList, List.drop_succ_cons, List.drop_zero,
    List.take_append_of_le_length (by omega), List.map_take]

/-- The same at the verifier's sumcheck. -/
theorem sumcheck_draws {z : Point} {e : Nat} {F0 F1 : Fork} {rounds : List Fmt.RoundView} {S : Sum}
    (hv : sumcheck z e F0 rounds = some (S, F1, [])) :
    S.r = (((rounds.drop 1).take z.size).map firstDrawn).toArray := by
  unfold sumcheck at hv
  obtain ⟨cs, F, left, h1, h2⟩ := bind_some hv
  obtain ⟨cA, s'⟩ := cs
  dsimp only at h2
  obtain ⟨hS, rfl, rfl⟩ := pure_some h2
  rw [← hS]
  show s'.r = _
  exact heardBy_draws h1

/-- The same at the verifier's level; and the element that it hands down. -/
theorem level_draws {z : Point} {start : Form} {F0 F1 : Fork} {rounds : List Fmt.RoundView}
    {line : Fmt.RoundView} {S : Sum} (hv : level z start F0 (rounds ++ [line]) = some (S, F1, []))
    (hlen : rounds.length = z.size + 3) :
    S.r = (((rounds.drop 1).take z.size).map firstDrawn).toArray ∧ S.down = firstDrawn line := by
  unfold level at hv
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some hv
  obtain ⟨cA, s'⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a0, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨hdn, rfl, rfl⟩ := need_some h3
  obtain ⟨hS, rfl, rfl⟩ := pure_some k3
  obtain ⟨e1, e2, _⟩ := Came.heardBy_cut h1
  rw [← hlen, List.take_left] at e1
  rw [← hlen, List.drop_left] at e2
  subst e2
  have hq : Part.MaskedSum.roundOf 0 1 line = some (a0, g) := by
    have h2' : (Part.MaskedSum.roundOf 0 1 line).map (fun x => (x, G1, ([] : List Fmt.RoundView))) =
        some ((a0, g), G2, []) := h2
    cases hr : Part.MaskedSum.roundOf 0 1 line with
    | none =>
      rw [hr] at h2'
      cases h2'
    | some y =>
      rw [hr] at h2'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2'
      rw [h2'.1]
  have h4 : g = line.drawn.elems.map E.ofTriple := (Part.MaskedSum.roundOf_spec hq).2.2.2
  rw [← hS]
  refine ⟨?_, ?_⟩
  · show s'.r = _
    exact heardBy_draws e1
  show dn = firstDrawn line
  unfold firstDrawn
  rw [← List.head?_map, ← h4, hdn]
  rfl

variable [Sizes] [Policy] [Request] [Token]

/-- The batching element is the round's first sampled element. -/
theorem batch_draws {n rows : Nat} {F Fa : Fork} {r : Fmt.RoundView} {A : Array Hid} {g : E}
    (h : sendThenBatch n rows F [r] = some ((A, g), Fa, [])) : g = firstDrawn r := by
  obtain ⟨r', x, hp, hx, hg, _⟩ := batch_one h
  obtain rfl := (List.cons.inj hp).1
  unfold firstDrawn
  rw [hx]
  exact hg.symm

variable [FinalNorm.In] [In]

/-- **Where the one hearing returns, using the rounds up, the rounds are eight pieces**: six of the
table's lengths, the last two by the number of zt's coordinates (the table's where that is lt). hW
is spent on nothing that is kept. -/
theorem hear_pieces {F G : Fork} {H : HeardAll} {rs : List Fmt.RoundView} (hW : WellLaid F)
    (h : hear F rs = some (H, G, [])) :
    ∃ (r0 r1 line r4 : Fmt.RoundView) (tS tP tN tL : List Fmt.RoundView),
      rs = [r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ (tN ++ tL)))))) ∧
      tS.length = lPd + lt + 3 ∧ tP.length = lt + 3 ∧ tN.length = (FinalNorm.zt).size + 3 ∧
      tL.length = (FinalNorm.zt ++ halves Norm.lPd).size + 3 := by
  obtain ⟨Fd, Fe, lr, hNorm, _, _, hN, hLg, hleft⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _, h2, h3, h4, _, _, _⟩ :=
    norm_parts hW hNorm
  obtain ⟨r0, rfl, hpv, hn0⟩ := point_spec h0
  have sPV : H.1.pV.size = lt := by rw [hpv, List.size_toArray, List.length_map, hn0]
  obtain ⟨r1, _, rfl, _, _, _⟩ := batch_one h1
  obtain ⟨r4, _, rfl, _, _, _⟩ := batch_one h3
  have lS : tS.length = lPd + lt + 4 := by rw [level_length h2, zS_size H.1.pV sPV]
  obtain ⟨_, _, _, _, _, _, lP, _⟩ := sumcheck_spec h4
  rw [sPV] at lP
  obtain ⟨_, _, _, _, _, _, lN, _⟩ := sumcheck_spec hN
  obtain ⟨_, _, _, _, _, _, lL, _⟩ := sumcheck_spec hLg
  have hne : tS ≠ [] := by
    intro e
    rw [e] at lS
    simp at lS
  refine ⟨r0, r1, tS.getLast hne, r4, tS.dropLast, tP, lr.take ((FinalNorm.zt).size + 3),
    (lr.drop ((FinalNorm.zt).size + 3)).take ((FinalNorm.zt ++ halves Norm.lPd).size + 3),
    ?_, by rw [List.length_dropLast, lS]; rfl, lP, lN, lL⟩
  have e7 : (lr.drop ((FinalNorm.zt).size + 3)).take
      ((FinalNorm.zt ++ halves Norm.lPd).size + 3) = lr.drop ((FinalNorm.zt).size + 3) :=
    List.take_of_length_le (List.drop_eq_nil_iff.mp hleft.symm)
  rw [hrs, e7, List.take_append_drop, ← List.append_assoc tS.dropLast,
    List.dropLast_append_getLast hne]

/-- **THE CHALLENGES THAT THE HEARING RETURNS ARE WHAT THE ROUNDS SAMPLED.** hW is spent on nothing
that is kept. -/
theorem hear_draws {F G : Fork} {H : HeardAll} {r0 r1 line r4 : Fmt.RoundView}
    {tS tP tN tL : List Fmt.RoundView} (hW : WellLaid F)
    (h : hear F ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ (tN ++ tL))))))) =
      some (H, G, []))
    (lS : tS.length = lPd + lt + 3) (lP : tP.length = lt + 3)
    (lN : tN.length = (FinalNorm.zt).size + 3) :
    H.1.pV = (r0.drawn.elems.map E.ofTriple).toArray ∧ H.1.gam = firstDrawn r1 ∧
    H.1.squares.r = (((tS.drop 1).take (lPd + lt)).map firstDrawn).toArray ∧
    H.1.squares.down = firstDrawn line ∧ H.1.om = firstDrawn r4 ∧
    H.1.products.r = (((tP.drop 1).take lt).map firstDrawn).toArray ∧
    H.2.1.normed.r = (((tN.drop 1).take (FinalNorm.zt).size).map firstDrawn).toArray ∧
    H.2.2.logits.r =
      (((tL.drop 1).take (FinalNorm.zt ++ halves Norm.lPd).size).map firstDrawn).toArray := by
  obtain ⟨Fa, Fb, Fc, Fd, Fe, h0, h1, h2, h3, h4, h5, h6, _, _, _, sPV⟩ :=
    hear_eight hW h rfl rfl lS rfl rfl lP lN
  obtain ⟨r0', e0, hpv, _⟩ := point_spec h0
  obtain rfl := (List.cons.inj e0).1
  have zs : (zS H.1.pV).size = lPd + lt := zS_size H.1.pV sPV
  obtain ⟨a, b⟩ := level_draws h2 (by rw [lS, zs])
  rw [zs] at a
  have c := sumcheck_draws h4
  rw [sPV] at c
  exact ⟨hpv, batch_draws h1, a, b, batch_draws h3, c, sumcheck_draws h5, sumcheck_draws h6⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.vars_chal
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heardBy_draws
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sumcheck_draws
#print axioms VerifiableInference.Desc.Kinds.Head.Law.level_draws
#print axioms VerifiableInference.Desc.Kinds.Head.Law.batch_draws
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_pieces
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_draws
