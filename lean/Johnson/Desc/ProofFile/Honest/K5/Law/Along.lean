-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Along.lean: CONDITIONAL: the ledger and the rounds along the
hearing of an attention segment's own rounds: each masked sumcheck of that hearing, seen from the
ledger behind. Definitions of propositions, and statements with their proofs. No arithmetic of the
field occurs.

The kind's hearing (`hear`, Johnson/Desc/First/Att/K5AttentionKind.lean) is one text; the honest side's row
(`shapes`, Johnson/Desc/K5/Honest/Faces.lean) is a list of parts. A law on one masked sumcheck asks:
the part's own text (`hear`, Johnson/Desc/Part/MaskedSum4.lean) has heard these rounds at this call
from a sized ledger, and the ledger at which the row is made is later. Here these are drawn from the
kind's hearing, for each of its sumchecks, with the sumcheck's number among the row's parts and its
stretch of the rounds in the row's own count (`firstOf`).

Main names:
  `SumHeardAt x rs G q C vs e hh`   one sumcheck of the hearing, seen from the ledger G
  `Along x rs G hd`                 all of them: the softmax-table units', and the six behind
  `SumHeardAt.mono`, `Along.mono`   a later ledger sees the same
  `SumHeardAt.r_length`             a challenge for each variable, and one more
  `Stands`, with `Stands.take`, `sum`, `batch`, `close`, `takes`, `units`
                                    where the hearing stands between two verbs: which stages are
                                    left, how many parts are done, which rounds are left
  `along_of_hear`                   **where the hearing returns from a sized ledger, `Along`
                                    holds.** CONDITIONAL on these two
  `along_of_hear_road`              the same from the library's other sentence on a ledger's sizes

Limits. One direction, from a return. Nothing on what the rounds hold, on the challenges or on what
lies under a slot. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Shape
import Johnson.Desc.Part.MaskedSumLedger
import OnBytes.Tie.Pv.Psc.Run.PscHide
import Johnson.Desc.K5.Honest.Law.Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Sized Later)
open VerifiableInference.Desc.Part (MaskedSum.hear MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.Part.MaskedSum (hear_keeps row_keeps)
open VerifiableInference.Desc.First.Att.P (Stage products script keyStage Heard hear batched St take
  sum batch close take_spec sum_spec batch_spec close_spec TakesRan UnitsRan hear_ran)
open H2K5.Honest (PartShape shapesOf shapes cut firstOf iSE iVM iVD iSF iSD iHB keyVars)

/-- **One masked sumcheck of the kind's hearing**, seen from the ledger G behind. x: the planner's
numbers of these rounds. rs: all rounds that the kind heard. q: the sumcheck's number among the
row's parts. C: the form that its sum is claimed to equal. vs, e: its variables and ends. hh: what
the hearing holds of it. It says: part q of the row is a sumcheck with these variables and ends;
the part's own text has heard just the stretch of part q, from a sized ledger, and handed back hh;
G is later than the ledger that it handed back. -/
def SumHeardAt (x : OnBytes.Params.AttentionRounds) (rs : List Fmt.RoundView) (G : Fork) (q : Nat)
    (C : Aff) (vs : List Var) (e : Ends) (hh : MaskedSum.Heard) : Prop :=
  ∃ (lead : Nat) (F' G' : Fork), (shapes x)[q]? = some (.sum ⟨lead, vs, some e⟩) ∧
    MaskedSum.hear C ⟨lead, vs, some e⟩ F' ((rs.drop (firstOf x q)).take (vs.length + 3)) =
      some (hh, G') ∧
    Sized F' ∧ Later G' G

/-- The variables and the ends of a sumcheck of products of two maps. -/
def prodVs (n : Nat) : List Var := List.replicate n (.plain 4)
def prodEnds (m : Nat) : Ends := ⟨2, 2 * m⟩

/-- The ends of the sumcheck on the key at the index; its variables: `keyVars`
(Johnson/Desc/K5/Honest/Law/Named.lean). -/
def keyEnds (x : OnBytes.Params.AttentionRounds) : Ends := ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩

/-- **All masked sumchecks of the kind's hearing**, each with its number in the row, its start form
and its field of what was heard. -/
structure Along (x : OnBytes.Params.AttentionRounds) (rs : List Fmt.RoundView) (G : Fork) (hd : Heard) :
    Prop where
  /-- as many softmax-table units were heard as the plan has -/
  units : hd.scores.size = x.score.length
  /-- a softmax-table unit: the start is the seventh of its seven scalars -/
  score : ∀ (i : Nat) (u : Nat × Nat) (o : Nat × MaskedSum.Heard), x.score[i]? = some u →
    hd.scores[i]? = some o → SumHeardAt x rs G i (.slot (o.1 + 6)) (prodVs u.1) (prodEnds u.2) o.2
  division : SumHeardAt x rs G (iSE x) (.slot (hd.five + 1)) (prodVs x.e) (prodEnds x.pairs)
    hd.division
  below : SumHeardAt x rs G (iVM x) (.slot hd.values) (prodVs x.valueM) (prodEnds x.pairs) hd.below
  on : SumHeardAt x rs G (iVD x) (.slot (hd.values + 1)) (prodVs x.valueD) (prodEnds x.pairs) hd.on
  atIndex : SumHeardAt x rs G (iSF x) (batched x.pairs hd.om hd.maxima 1 0) (prodVs x.attained)
    (prodEnds x.pairs) hd.atIndex
  key : SumHeardAt x rs G (iSD x) (batched x.pairs hd.om' hd.atIndex.sEnd 2 1) (keyVars x)
    (keyEnds x) hd.key
  cells : SumHeardAt x rs G (iHB x) (.ofConst zeroE) (prodVs x.bits) (prodEnds x.pairs) hd.cells

/-- A later ledger sees the same. -/
theorem SumHeardAt.mono {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G G2 : Fork}
    {q : Nat} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    (h : SumHeardAt x rs G q C vs e hh) (l : Later G G2) : SumHeardAt x rs G2 q C vs e hh := by
  obtain ⟨lead, F', G', a, b, c, d⟩ := h
  exact ⟨lead, F', G', a, b, c, d.trans l⟩

/-- What the hearing holds of a sumcheck has a challenge for each variable, and one more. -/
theorem SumHeardAt.r_length {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G : Fork}
    {q : Nat} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    (h : SumHeardAt x rs G q C vs e hh) : hh.r.length = vs.length + 1 := by
  obtain ⟨lead, F', G', _, hh', _, _⟩ := h
  obtain ⟨_, T, R, _, hR, he, _⟩ := VerifiableInference.Desc.Part.MaskedSum.hear_spec hh'
  obtain ⟨_, used, _, _, _, _, _, hv, _⟩ :=
    VerifiableInference.Desc.Part.MaskedSum.readAll_spec hR
  rw [he]
  show (R.rounds.map (·.2)).length = _
  rw [List.length_map, hv.length.2, List.length_append, List.length_singleton]

theorem Along.mono {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {G G2 : Fork}
    {hd : Heard} (h : Along x rs G hd) (l : Later G G2) : Along x rs G2 hd :=
  ⟨h.units, fun i u o hu ho => (h.score i u o hu ho).mono l, h.division.mono l, h.below.mono l,
    h.on.mono l, h.atIndex.mono l, h.key.mono l, h.cells.mono l⟩

/-! ## Lists, and the row's count of rounds -/

namespace AlongLists

theorem drop_cons {α : Type} : ∀ {l : List α} {n : Nat} {a : α} {t : List α},
    l.drop n = a :: t → l[n]? = some a ∧ l.drop (n + 1) = t
  | [], n, a, t, h => by simp at h
  | x :: l, 0, a, t, h => by
    rw [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | x :: l, n + 1, a, t, h => by
    have := drop_cons (l := l) (n := n) (a := a) (t := t) (by simpa using h)
    simpa using this

theorem drop_add {α : Type} : ∀ (l : List α) (a b : Nat), (l.drop a).drop b = l.drop (a + b)
  | [], a, b => by simp
  | x :: l, 0, b => by simp
  | x :: l, a + 1, b => by
    rw [List.drop_succ_cons, drop_add l a b, Nat.add_right_comm, List.drop_succ_cons]

end AlongLists

open AlongLists

/-- The first round of the next part. -/
theorem firstOf_step (x : OnBytes.Params.AttentionRounds) (q : Nat) (s : PartShape)
    (h : (shapes x)[q]? = some s) : firstOf x (q + 1) = firstOf x q + s.rounds := by
  unfold firstOf cut
  have hc : ((shapes x).map (·.rounds))[q]? = some s.rounds := by
    rw [List.getElem?_map, h]
    rfl
  rw [List.take_add_one, hc]
  simp [List.foldl_append]

/-! ## Where the hearing stands -/

/-- **Where the hearing stands between two verbs.** st: the stages that are left. q: the parts of
the row that are done. It says: the parts that are left are those of the stages left, at the scalars
that wait; the rounds left are those from the first round of part q on; the ledger is sized. -/
structure Stands (x : OnBytes.Params.AttentionRounds) (rs : List Fmt.RoundView) (st : List Stage) (q : Nat)
    (s : St) : Prop where
  parts : (shapes x).drop q = shapesOf s.2.2 st
  left : s.2.1 = rs.drop (firstOf x q)
  sized : Sized s.1

variable {x : OnBytes.Params.AttentionRounds} {rs : List Fmt.RoundView} {st : List Stage} {q : Nat}

theorem Stands.take {n j : Nat} {s s' : St} (a : Stands x rs (.scalars n :: st) q s)
    (h : take n s = some (j, s')) : Stands x rs st q s' ∧ Later s.1 s'.1 := by
  obtain ⟨F, r, lead⟩ := s
  obtain ⟨G, r', lead'⟩ := s'
  obtain ⟨_, e2, e3, _, _, v, _, _, _, hw⟩ := take_spec h
  subst e2 e3
  have l1 : Later F ({ F with next := F.next + n } : Fork) :=
    ⟨Nat.le_add_right _ _, rfl, id, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  have l : Later F G := l1.trans (OnBytes.PscRun.hideRun_keeps hw)
  exact ⟨⟨a.parts, a.left, l.sized a.sized⟩, l⟩

theorem Stands.sum {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (a : Stands x rs (.sum vs e :: st) q s) (h : sum C (.sum vs e) s = some (hh, s')) :
    Stands x rs st (q + 1) s' ∧ Later s.1 s'.1 ∧ SumHeardAt x rs s'.1 q C vs e hh := by
  obtain ⟨F, r, lead⟩ := s
  obtain ⟨G, r', lead'⟩ := s'
  obtain ⟨e1, e2, G1, f, h1, h2⟩ := sum_spec h
  subst e1 e2
  have hp := drop_cons (show (shapes x).drop q = .sum ⟨lead, vs, some e⟩ :: shapesOf 0 st from
    a.parts)
  have hl : r = rs.drop (firstOf x q) := a.left
  have l : Later F G := (hear_keeps h1).trans (row_keeps h2)
  refine ⟨⟨hp.2, ?_, l.sized a.sized⟩, l, lead, F, G1, hp.1, ?_, a.sized, row_keeps h2⟩
  · show r.drop (vs.length + 3) = _
    rw [hl, drop_add, firstOf_step x q _ hp.1]
    rfl
  · rw [← hl]
    exact h1

theorem Stands.batch {rows : Nat} {w : Array E} {s s' : St}
    (a : Stands x rs (.batch rows :: st) q s) (h : batch rows s = some (w, s')) :
    Stands x rs st (q + 1) s' ∧ Later s.1 s'.1 := by
  obtain ⟨F, r, lead⟩ := s
  obtain ⟨G, r', lead'⟩ := s'
  obtain ⟨e1, e2, r0, _, e3, _⟩ := batch_spec h
  subst e1 e2
  have hp := drop_cons (show (shapes x).drop q = .one lead :: shapesOf 0 st from a.parts)
  have hl : rs.drop (firstOf x q) = r0 :: r' := (show r = _ from a.left).symm.trans e3
  refine ⟨⟨hp.2, ?_, a.sized⟩, Later.refl _⟩
  show r' = _
  rw [firstOf_step x q _ hp.1]
  exact (drop_cons hl).2.symm

theorem Stands.close {n : Nat} {d : List E} {s s' : St}
    (a : Stands x rs (.point n :: st) q s) (h : close n s = some (d, s')) :
    Stands x rs st (q + 1) s' ∧ Later s.1 s'.1 := by
  obtain ⟨F, r, lead⟩ := s
  obtain ⟨G, r', lead'⟩ := s'
  obtain ⟨e1, e2, r0, e3, _⟩ := close_spec h
  subst e1 e2
  have hp := drop_cons (show (shapes x).drop q = .one lead :: shapesOf 0 st from a.parts)
  have hl : rs.drop (firstOf x q) = r0 :: r' := (show r = _ from a.left).symm.trans e3
  refine ⟨⟨hp.2, ?_, a.sized⟩, Later.refl _⟩
  show r' = _
  rw [firstOf_step x q _ hp.1]
  exact (drop_cons hl).2.symm

theorem Stands.takes : ∀ (k : Nat) (js : List Nat) (s s' : St), TakesRan 3 k js s s' →
    Stands x rs (List.replicate k (.scalars 3) ++ st) q s → Stands x rs st q s' ∧ Later s.1 s'.1
  | 0, [], s, s', h, a => by
    have e : s' = s := h
    rw [e]
    exact ⟨a, Later.refl _⟩
  | k + 1, j :: js, s, s', ⟨s1, h1, h2⟩, a => by
    obtain ⟨b, l1⟩ := Stands.take
      (show Stands x rs (.scalars 3 :: (List.replicate k (.scalars 3) ++ st)) q s from a) h1
    obtain ⟨c, l2⟩ := Stands.takes k js s1 s' h2 b
    exact ⟨c, l1.trans l2⟩
  | 0, _ :: _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, h, _ => h.elim

theorem Stands.units : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St)
    (q : Nat), UnitsRan us os s s' →
    Stands x rs ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ st) q s →
    Stands x rs st (q + us.length) s' ∧ Later s.1 s'.1 ∧ os.length = us.length ∧
      ∀ (i : Nat) (u : Nat × Nat) (o : Nat × MaskedSum.Heard), us[i]? = some u → os[i]? = some o →
        SumHeardAt x rs s'.1 (q + i) (.slot (o.1 + 6)) (prodVs u.1) (prodEnds u.2) o.2
  | [], [], s, s', q, h, a => by
    have e : s' = s := h
    rw [e]
    exact ⟨a, Later.refl _, rfl, fun i u o hu _ => by cases hu⟩
  | u :: us, o :: os, s, s', q, ⟨s1, ⟨sa, t7, sm⟩, rest⟩, a => by
    obtain ⟨b, l1⟩ := Stands.take (show Stands x rs
      (.scalars 7 :: .sum (prodVs u.1) (prodEnds u.2) ::
        ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ st)) q s from a) t7
    obtain ⟨c, l2, H⟩ := Stands.sum b sm
    obtain ⟨d, l3, hlen, K⟩ := Stands.units us os s1 s' (q + 1) rest c
    refine ⟨?_, l1.trans (l2.trans l3), by rw [List.length_cons, List.length_cons, hlen], ?_⟩
    · rw [List.length_cons, show q + (us.length + 1) = q + 1 + us.length by omega]
      exact d
    · intro i u' o' hu ho
      cases i with
      | zero =>
        cases hu
        cases ho
        exact H.mono l3
      | succ i =>
        rw [show q + (i + 1) = q + 1 + i by omega]
        exact K i u' o' hu ho
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

/-! ## The whole hearing -/

/-- **Where the kind's hearing returns from a sized ledger, each of its masked sumchecks was heard
by the part's own text, on its own stretch of the rounds, from a sized ledger, and the ledger behind
the whole hearing is later.** CONDITIONAL on: the hearing returns, begun with no scalar waiting; the
ledger in front is sized. -/
theorem along_of_hear {x : OnBytes.Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView}
    {lead : Nat} {hd : Heard} (hz : Sized F) (hh : hear x (F, rs, 0) = some (hd, G, rest, lead)) :
    Along x rs G hd := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ra, rb, r1,
    r2, r3, r4, r5, r6, r7, r8, r9, -, r10, r11, r12, r13, r14, r15, r16⟩ := (hear_ran hh).ran
  have a0 : Stands x rs (List.replicate x.planeMessages (.scalars 3) ++
      ((x.score.flatMap fun u => [.scalars 7, products u.1 u.2]) ++
        [.scalars 5, .scalars x.lt, .scalars 2, .sum (prodVs x.e) (prodEnds x.pairs), .batch 2,
          .scalars 2, .sum (prodVs x.valueM) (prodEnds x.pairs),
          .sum (prodVs x.valueD) (prodEnds x.pairs), .point (2 * x.lgk + 2 * x.lt + 4),
          .scalars x.pairs, .batch x.pairs, .sum (prodVs x.attained) (prodEnds x.pairs),
          .batch x.pairs, .sum (keyVars x) (keyEnds x), .batch x.pairs,
          .sum (prodVs x.bits) (prodEnds x.pairs)])) 0 (F, rs, 0) := by
    refine ⟨?_, rfl, hz⟩
    rw [← List.append_assoc]
    rfl
  obtain ⟨aa, _⟩ := Stands.takes _ _ _ _ ra a0
  obtain ⟨ab, _, hlen, U⟩ := Stands.units _ _ _ _ 0 rb aa
  rw [Nat.zero_add] at ab
  obtain ⟨b1, t2⟩ := ab.take r1
  obtain ⟨b2, t3⟩ := b1.take r2
  obtain ⟨b3, t4⟩ := b2.take r3
  obtain ⟨b4, t5, H4⟩ := b3.sum r4
  obtain ⟨b5, t6⟩ := b4.batch r5
  obtain ⟨b6, t7⟩ := b5.take r6
  obtain ⟨b7, t8, H7⟩ := b6.sum r7
  obtain ⟨b8, t9, H8⟩ := b7.sum r8
  obtain ⟨b9, t10⟩ := b8.close r9
  obtain ⟨b10, t11⟩ := b9.take r10
  obtain ⟨b11, t12⟩ := b10.batch r11
  obtain ⟨b12, t13, H12⟩ := b11.sum r12
  obtain ⟨b13, t14⟩ := b12.batch r13
  obtain ⟨b14, t15, H14⟩ := b13.sum r14
  obtain ⟨b15, t16⟩ := b14.batch r15
  obtain ⟨_, t17, H16⟩ := b15.sum r16
  have c14 : Later s14.1 G := t16.trans t17
  have c12 : Later s12.1 G := t14.trans (t15.trans c14)
  have c8 : Later s8.1 G := t10.trans (t11.trans (t12.trans (t13.trans c12)))
  have c7 : Later s7.1 G := t9.trans c8
  have c4 : Later s4.1 G := t6.trans (t7.trans (t8.trans c7))
  have cb : Later sb.1 G := t2.trans (t3.trans (t4.trans (t5.trans c4)))
  refine ⟨by rw [← Array.length_toList]; exact hlen, fun i u o hu ho => ?_, H4.mono c4, H7.mono c7,
    H8.mono c8, H12.mono c12, H14.mono c14, H16⟩
  have := U i u o hu (by rw [Array.getElem?_toList]; exact ho)
  rw [Nat.zero_add] at this
  exact this.mono cb

/-- The same from the library's other sentence "the ledger is sized", a structure with the same
three clauses (OnBytes/Tie/Pv/Psc/Run/PscHide.lean). -/
theorem along_of_hear_road {x : OnBytes.Params.AttentionRounds} {F G : Fork}
    {rs rest : List Fmt.RoundView} {lead : Nat} {hd : Heard} (hz : OnBytes.Model.Road.Sized F)
    (hh : hear x (F, rs, 0) = some (hd, G, rest, lead)) : Along x rs G hd :=
  along_of_hear ⟨hz.vp, hz.mf, hz.got⟩ hh

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.SumHeardAt.mono
#print axioms ProofFile.Honest.K5.SumHeardAt.r_length
#print axioms ProofFile.Honest.K5.Along.mono
#print axioms ProofFile.Honest.K5.AlongLists.drop_cons
#print axioms ProofFile.Honest.K5.AlongLists.drop_add
#print axioms ProofFile.Honest.K5.firstOf_step
#print axioms ProofFile.Honest.K5.Stands.take
#print axioms ProofFile.Honest.K5.Stands.sum
#print axioms ProofFile.Honest.K5.Stands.batch
#print axioms ProofFile.Honest.K5.Stands.close
#print axioms ProofFile.Honest.K5.Stands.takes
#print axioms ProofFile.Honest.K5.Stands.units
#print axioms ProofFile.Honest.K5.along_of_hear
#print axioms ProofFile.Honest.K5.along_of_hear_road
