-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/PtsSizes.lean: CONDITIONAL. Ten definitions, and statements with their
proofs.

What is here. How many coordinates the sampled values have that the honest parts of the feed-forward
layers' rounds read off the challenges heard (`ptsOf`, Johnson/Desc/K4/Honest/Front.lean), where the
challenges have the shape of the verifier's table of rounds (`rounds`,
OnBytes/Desc/First/K4/Rounds.lean).

K4 is the sub-protocol of the feed-forward layers' rounds. PV: the norms' token point. rhoI: the
point on the norms' numbers. rhoM: the point on the layers with routed experts. rt: the challenges
of the second token sumcheck. rs: those of the batched sumcheck. `masked` is the library's maker of
the rows of a sumcheck of that name out of four numbers (OnBytes/Desc/First/K4/Rounds.lean): it
reads no mask.

  `idxOf`, `rowsNamed_eq`, `idxOf_cons`, `idxOf_append`, `idxOf_length`, `idx_at`   the numbers of
     the rows that bear a name
  `OwnFits`   K4's own challenges have the table's shape
  `preJoin`, `preTerms`, `preStack`, `preJoin2`, `postJoin`, `postTerms`, `postStack`,
  `postJoin2`   the table in front of four of its rows, and behind them
  `rounds_zero`, `rounds_join`, `rounds_terms`, `rounds_stack`, `rounds_join2`   the table, cut
     there
  `masked_count`, `preJoin_join`, `preJoin_eps`, `preTerms_eps`, `preTerms_join`, `preStack_eps`,
     `preStack_join`, `preJoin2_join`   how many rows of a stretch bear a name
  `elems_size`, `inner_size`   a point's round; the rounds of a sumcheck
  `pts_PV`, `pts_rhoI`, `pts_rhoM`, `pts_rt`, `pts_rs`   **the five sizes**

Limits. Two premises on the challenges heard: each of K4's own challenges holds as many elements as
the table's row for its round says (`OwnFits`: at PV, rhoI, rhoM; rt and rs want the number alone);
and so many of them have been heard as the field's rounds want: that number is written as the length
of a stretch of the table, at `pts_PV` as «more than none» (the lengths as numbers:
Johnson/Desc/K4/Honest/Law/PtsCounts.lean). `postJoin`, `postTerms`, `postStack` and `postJoin2` are
the proofs' witnesses: the five statements `rounds_zero` to `rounds_join2` say «there is a rest»; no
statement names the four. Five fields alone: PV, rhoI, rhoM, rt, rs. Nothing on the values. Nothing
on what the lookup in front has sampled.

Kin. THE LIBRARY CUTS THE SAME TABLE IN OTHER WAYS: `rounds_eq`
(Johnson/Desc/First/K4/Returns/Whole.lean) has it as five stretches, one for each function of the
hearing; another `rounds_eq` (Johnson/Road/K4/DsTailR.lean) as the points' rows and then the rest;
`k4_rounds_cut` (Johnson/Desc/ProofFile/Honest/K4/Law/Mark.lean) lays the stretches of rounds of a
variable of the first three masked sumchecks apart. The table's length as a number: `rounds_len`
(Johnson/Road/K4/K4CutRows.lean). BY READING, `preTerms Q` LISTS THE ROWS OF `rowsNorms Q.P Q.g`
(Johnson/Desc/First/K4/Returns/Norms.lean), in other brackets and with one `if` where that text has
two, and `preStack Q` those of `rowsNorms`, `rowsTerms` (Returns/Terms.lean) and one row more: TWO
TEXTS OF ONE STRETCH; no statement that we know ties them; none of these files is imported here.
`idxOf` lists the numbers that `k4Listed` (Johnson/Desc/ProofFile/Honest/K4/Law/MarkWide.lean) lists
at the test on a row's name; that walk is general in the test and written by recursion; no statement
that we know ties the two. The first rounds of all seven masked sumchecks as numbers: `starts_eq`
(Johnson/Desc/ProofFile/Honest/K4/Law/StartsAre.lean), by `rowsNamed_eq`, `idxOf_append` and
`idxOf_cons` of this file.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.PtsLaw
open OnBytes (E zeroE)
open OnBytes.Model (RoundName ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (Rd rounds masked layerRds pointRd batchRd)

/-! ## 1 The rows that bear a name -/

/-- The numbers, from k on, of the rows of a table that bear the name r. -/
def idxOf (l : List Rd) (r : RoundName) (k : Nat) : List Nat :=
  ((l.zipIdx k).filter fun x => x.1.name == r).map (·.2)

/-- The program's list of the rows that bear a name. -/
theorem rowsNamed_eq (Q : K4Pub) (r : RoundName) :
    rowsNamed Q r = idxOf (rounds Q.P Q.hp Q.g) r 0 := rfl

/-- One row more in front. -/
theorem idxOf_cons (x : Rd) (l : List Rd) (r : RoundName) (k : Nat) :
    idxOf (x :: l) r k = if x.name == r then k :: idxOf l r (k + 1) else idxOf l r (k + 1) := by
  unfold idxOf
  rw [List.zipIdx_cons, List.filter_cons]
  split <;> rfl

/-- Two stretches of a table. -/
theorem idxOf_append (r : RoundName) : ∀ (a b : List Rd) (k : Nat),
    idxOf (a ++ b) r k = idxOf a r k ++ idxOf b r (k + a.length)
  | [], b, k => rfl
  | x :: a, b, k => by
    have e : k + (x :: a).length = k + 1 + a.length := by
      rw [List.length_cons]
      omega
    rw [List.cons_append, idxOf_cons, idxOf_cons, idxOf_append r a b (k + 1), e]
    split <;> rfl

/-- As many numbers as rows bear the name. -/
theorem idxOf_length (r : RoundName) : ∀ (a : List Rd) (k : Nat),
    (idxOf a r k).length = a.countP fun x => x.name == r
  | [], _ => rfl
  | x :: a, k => by
    rw [idxOf_cons]
    split
    · rename_i h
      rw [List.length_cons, idxOf_length r a (k + 1), List.countP_cons]
      simp [h]
    · rename_i h
      rw [idxOf_length r a (k + 1), List.countP_cons]
      simp [h]

/-- **A row that bears the name r, behind a stretch A of the table, is number A.length; among the
rows of that name it is the one whose number is how many rows of A bear the name.** -/
theorem idx_at (A B : List Rd) (x : Rd) (r : RoundName) (hx : (x.name == r) = true) :
    (idxOf (A ++ x :: B) r 0)[A.countP fun y => y.name == r]? = some A.length := by
  rw [idxOf_append, idxOf_cons, if_pos hx, ← idxOf_length r A 0,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, Nat.zero_add]
  rfl

/-! ## 2 The challenges' shape -/

/-- Each of K4's own challenges that has been heard holds as many elements as the table's row for
its round says. -/
def OwnFits (Q : K4Pub) (heard : List Fmt.Drawn) : Prop :=
  ∀ (j : Nat) (d : Fmt.Drawn) (x : Rd), (heard.drop Q.r0)[j]? = some d →
    (rounds Q.P Q.hp Q.g)[j]? = some x → d.elems.length = x.drawn

/-! ## 3 The table, cut in front of a row -/

/-- In front of the first round named "join". -/
def preJoin (Q : K4Pub) : List Rd :=
  [pointRd .zero Q.P.y.h.lt] ++
  (if Q.g == 0 then [pointRd .zero (Q.P.y.ls + Q.P.y.h.lt), pointRd .zero (Q.P.y.lPd - Q.P.y.ls)]
   else []) ++
  [batchRd (ledNS Q.P.y.h.xl * Q.P.y.NI) (ledNS Q.P.y.h.xl)]

/-- In front of the second token sumcheck. -/
def preTerms (Q : K4Pub) : List Rd :=
  preJoin Q ++ [pointRd .join Q.P.rd.lNI] ++ layerRds Q.P.rd.muV ++
  [batchRd (ledNP Q.P.y.h.xl * Q.P.y.NI) (ledNP Q.P.y.h.xl * Q.P.y.NI)] ++
  masked Q.P.y.h.lt 2 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)

/-- In front of the batched sumcheck. -/
def preStack (Q : K4Pub) : List Rd :=
  preTerms Q ++ masked Q.P.y.h.lt 2 1 (nEndT Q.P.y) ++ [batchRd 0 2]

/-- In front of the second round named "join". -/
def preJoin2 (Q : K4Pub) : List Rd :=
  preStack Q ++
  masked Q.hp.lamS 1 2 (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - (if Q.g == 0 then 1 else 0))) ++
  layerRds Q.P.rd.muH

/-- Behind the second round named "join". -/
def postJoin2 (Q : K4Pub) : List Rd :=
  layerRds Q.P.rd.muH2 ++ [batchRd (if Q.g == 0 then 1 else 0) Q.hp.NCL] ++
  masked Q.P.wsLay.lk 1 1 1

/-- Behind the batched sumcheck's first round. -/
def postStack (Q : K4Pub) : List Rd :=
  List.replicate Q.hp.lamS { name := .pscRound, sent := 2 } ++
  [{ name := .pscY, sent := 2, notZero := 1 },
   { name := .pscValues
     sent := 2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - (if Q.g == 0 then 1 else 0)), drawn := 0 }] ++
  layerRds Q.P.rd.muH ++ [pointRd .join (Q.P.y.h.ll - 1)] ++ postJoin2 Q

/-- Behind the second token sumcheck's first round. -/
def postTerms (Q : K4Pub) : List Rd :=
  List.replicate Q.P.y.h.lt { name := .pscRound, sent := 2 } ++
  [{ name := .pscY, sent := 1, notZero := 1 },
   { name := .pscValues, sent := nEndT Q.P.y, drawn := 0 }] ++
  [batchRd 0 2] ++ [{ name := .pscEpsilon, sent := 1 }] ++ postStack Q

/-- Behind the first round named "join". -/
def postJoin (Q : K4Pub) : List Rd :=
  layerRds Q.P.rd.muV ++
  [batchRd (ledNP Q.P.y.h.xl * Q.P.y.NI) (ledNP Q.P.y.h.xl * Q.P.y.NI)] ++
  masked Q.P.y.h.lt 2 2 (ledNO Q.P.y.h.xl * Q.P.y.NI) ++ [{ name := .pscEpsilon, sent := 2 }] ++
  postTerms Q

/-- The table's first row. -/
theorem rounds_zero (Q : K4Pub) : ∃ B, rounds Q.P Q.hp Q.g = [] ++ pointRd .zero Q.P.y.h.lt :: B :=
  ⟨_, rfl⟩

/-- The table, cut at the first round named "join". -/
theorem rounds_join (Q : K4Pub) :
    ∃ B, rounds Q.P Q.hp Q.g = preJoin Q ++ pointRd .join Q.P.rd.lNI :: B := by
  refine ⟨postJoin Q, ?_⟩
  simp only [rounds, preJoin, postJoin, postTerms, postStack, postJoin2, masked,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The table, cut at the second token sumcheck's first round. -/
theorem rounds_terms (Q : K4Pub) :
    ∃ B, rounds Q.P Q.hp Q.g = preTerms Q ++ { name := .pscEpsilon, sent := 2 } :: B := by
  refine ⟨postTerms Q, ?_⟩
  simp only [rounds, preTerms, preJoin, postTerms, postStack, postJoin2, masked,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The table, cut at the batched sumcheck's first round. -/
theorem rounds_stack (Q : K4Pub) :
    ∃ B, rounds Q.P Q.hp Q.g = preStack Q ++ { name := .pscEpsilon, sent := 1 } :: B := by
  refine ⟨postStack Q, ?_⟩
  simp only [rounds, preStack, preTerms, preJoin, postStack, postJoin2, masked,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The table, cut at the second round named "join". -/
theorem rounds_join2 (Q : K4Pub) :
    ∃ B, rounds Q.P Q.hp Q.g = preJoin2 Q ++ pointRd .join (Q.P.y.h.ll - 1) :: B := by
  refine ⟨postJoin2 Q, ?_⟩
  simp only [rounds, preJoin2, preStack, preTerms, preJoin, postJoin2, masked,
    List.append_assoc, List.cons_append, List.nil_append]

/-- How many rows of a masked sumcheck bear a name. -/
theorem masked_count (k a b c : Nat) (r : RoundName) :
    (masked k a b c).countP (fun x => x.name == r) =
      (if RoundName.pscEpsilon == r then 1 else 0) + (if RoundName.pscRound == r then k else 0) +
        (if RoundName.pscY == r then 1 else 0) + (if RoundName.pscValues == r then 1 else 0) := by
  cases r <;> simp [masked, List.countP_append, List.countP_replicate]

/-- No round named "join" stands in front of the first. -/
theorem preJoin_join (Q : K4Pub) : (preJoin Q).countP (fun x => x.name == .join) = 0 := by
  unfold preJoin
  split <;> simp [pointRd, batchRd]

/-- Nor does a sumcheck begin there. -/
theorem preJoin_eps (Q : K4Pub) : (preJoin Q).countP (fun x => x.name == .pscEpsilon) = 0 := by
  unfold preJoin
  split <;> simp [pointRd, batchRd]

/-- Two sumchecks begin in front of the second token sumcheck. -/
theorem preTerms_eps (Q : K4Pub) : (preTerms Q).countP (fun x => x.name == .pscEpsilon) = 2 := by
  simp [preTerms, layerRds, List.countP_append, masked_count, preJoin_eps, pointRd, batchRd]

/-- One round named "join" stands there. -/
theorem preTerms_join (Q : K4Pub) : (preTerms Q).countP (fun x => x.name == .join) = 1 := by
  simp [preTerms, layerRds, List.countP_append, masked_count, preJoin_join, pointRd, batchRd]

/-- Three sumchecks begin in front of the batched sumcheck. -/
theorem preStack_eps (Q : K4Pub) : (preStack Q).countP (fun x => x.name == .pscEpsilon) = 3 := by
  simp [preStack, List.countP_append, masked_count, preTerms_eps, batchRd]

/-- One round named "join" stands there. -/
theorem preStack_join (Q : K4Pub) : (preStack Q).countP (fun x => x.name == .join) = 1 := by
  simp [preStack, List.countP_append, masked_count, preTerms_join, batchRd]

/-- One round named "join" stands in front of the second. -/
theorem preJoin2_join (Q : K4Pub) : (preJoin2 Q).countP (fun x => x.name == .join) = 1 := by
  simp [preJoin2, layerRds, List.countP_append, masked_count, preStack_join]

/-! ## 4 A point's round; the rounds of a sumcheck -/

/-- The elements of the challenge of the row behind a stretch A are as many as the row says. -/
theorem elems_size (Q : K4Pub) (heard : List Fmt.Drawn) (hf : OwnFits Q heard) (A B : List Rd)
    (x : Rd) (hs : rounds Q.P Q.hp Q.g = A ++ x :: B)
    (hn : A.length < (heard.drop Q.r0).length) :
    ((((some A.length).bind fun j => (heard.drop Q.r0)[j]?).map elemsOf).getD #[]).size =
      x.drawn := by
  have hd : (heard.drop Q.r0)[A.length]? = some (heard.drop Q.r0)[A.length] :=
    List.getElem?_eq_getElem hn
  have hx : (rounds Q.P Q.hp Q.g)[A.length]? = some x := by
    rw [hs, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  show ((((heard.drop Q.r0)[A.length]?).map elemsOf).getD #[]).size = _
  rw [hd]
  show (elemsOf _).size = _
  rw [← hf _ _ _ hd hx]
  simp [elemsOf]

/-- The challenges of the n rounds behind row number s are n, once they have been heard. -/
theorem inner_size (own : List Fmt.Drawn) (s n : Nat) (hn : s + 1 + n ≤ own.length) :
    (whole n (onesFrom own (s + 1) n)).size = n := by
  have h : (onesFrom own (s + 1) n).size = n := by
    simp only [onesFrom, List.size_toArray, List.length_map, List.length_take, List.length_drop]
    omega
  unfold whole
  rw [if_pos (by simpa using h), h]

/-! ## 5 The five sizes -/

/-- PV has a coordinate for each bit of a token's number, once K4's first challenge is heard. -/
theorem pts_PV (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : 0 < (heard.drop Q.r0).length) : (ptsOf Q w heard).PV.size = Q.P.y.h.lt := by
  obtain ⟨B, hB⟩ := rounds_zero Q
  have hi : (rowsNamed Q .zero)[0]? = some 0 := by
    rw [rowsNamed_eq, hB]
    exact idx_at [] B _ .zero rfl
  simp only [ptsOf]
  rw [hi]
  exact elems_size Q heard hf [] B _ hB hn

/-- rhoI has lNI coordinates, once the first round named "join" is heard. -/
theorem pts_rhoI (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (preJoin Q).length < (heard.drop Q.r0).length) :
    (ptsOf Q w heard).rhoI.size = Q.P.rd.lNI := by
  obtain ⟨B, hB⟩ := rounds_join Q
  have hi : (rowsNamed Q .join)[0]? = some (preJoin Q).length := by
    have h := idx_at (preJoin Q) B (pointRd .join Q.P.rd.lNI) .join rfl
    rw [preJoin_join] at h
    rw [rowsNamed_eq, hB]
    exact h
  simp only [ptsOf]
  rw [hi]
  exact elems_size Q heard hf _ B _ hB hn

/-- rhoM has ll - 1 coordinates, once the second round named "join" is heard. -/
theorem pts_rhoM (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) (hf : OwnFits Q heard)
    (hn : (preJoin2 Q).length < (heard.drop Q.r0).length) :
    (ptsOf Q w heard).rhoM.size = Q.P.y.h.ll - 1 := by
  obtain ⟨B, hB⟩ := rounds_join2 Q
  have hi : (rowsNamed Q .join)[1]? = some (preJoin2 Q).length := by
    have h := idx_at (preJoin2 Q) B (pointRd .join (Q.P.y.h.ll - 1)) .join rfl
    rw [preJoin2_join] at h
    rw [rowsNamed_eq, hB]
    exact h
  simp only [ptsOf]
  rw [hi]
  exact elems_size Q heard hf _ B _ hB hn

/-- rt has lt coordinates, once the rounds of the second token sumcheck's variables are heard. -/
theorem pts_rt (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn)
    (hn : (preTerms Q).length + 1 + Q.P.y.h.lt ≤ (heard.drop Q.r0).length) :
    (ptsOf Q w heard).rt.size = Q.P.y.h.lt := by
  obtain ⟨B, hB⟩ := rounds_terms Q
  have hi : (starts Q)[2]? = some (preTerms Q).length := by
    have h := idx_at (preTerms Q) B { name := .pscEpsilon, sent := 2 } .pscEpsilon rfl
    rw [preTerms_eps] at h
    show (rowsNamed Q .pscEpsilon)[2]? = _
    rw [rowsNamed_eq, hB]
    exact h
  simp only [ptsOf]
  rw [hi]
  exact inner_size _ _ _ hn

/-- rs has lamS coordinates, once the rounds of the batched sumcheck's variables are heard. -/
theorem pts_rs (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn)
    (hn : (preStack Q).length + 1 + Q.hp.lamS ≤ (heard.drop Q.r0).length) :
    (ptsOf Q w heard).rs.size = Q.hp.lamS := by
  obtain ⟨B, hB⟩ := rounds_stack Q
  have hi : (starts Q)[3]? = some (preStack Q).length := by
    have h := idx_at (preStack Q) B { name := .pscEpsilon, sent := 1 } .pscEpsilon rfl
    rw [preStack_eps] at h
    show (rowsNamed Q .pscEpsilon)[3]? = _
    rw [rowsNamed_eq, hB]
    exact h
  simp only [ptsOf]
  rw [hi, Array.size_reverse]
  exact inner_size _ _ _ hn

end OnBytes.Desc.First.K4.Honest.PtsLaw

#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.idxOf
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rowsNamed_eq
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.idxOf_cons
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.idxOf_append
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.idxOf_length
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.idx_at
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.OwnFits
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preTerms
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preStack
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin2
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.postJoin2
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.postStack
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.postTerms
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.postJoin
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rounds_zero
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rounds_join
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rounds_terms
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rounds_stack
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.rounds_join2
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.masked_count
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin_join
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin_eps
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preTerms_eps
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preTerms_join
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preStack_eps
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preStack_join
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin2_join
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.elems_size
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.inner_size
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.pts_PV
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.pts_rhoI
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.pts_rhoM
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.pts_rt
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.pts_rs
