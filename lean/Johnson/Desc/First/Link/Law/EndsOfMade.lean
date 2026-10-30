-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EndsOfMade.lean: WHERE THE PROOF FILE's PUBLIC PART Z IS MADE, THE INDEX
MASKS' AND W's (tree, tenant), AS THE TABLE's NUMBERS OFF THE PLAN NAME THEM (`numbersOf`,
Johnson/P5T/NumbersOf.lean), ARE SEATS OF ENTRIES WITH A SAMPLE OF THE PLAN's OWN LIST (`planSeats`,
Johnson/P5T/PlanSeats.lean): THE TWO MEMBERSHIPS OF THE NAMED TEST `endsThere`
(Johnson/P5J/GroupsPaid.lean; = PlanOk's "groups", by its groups_is). AT EVERY Z THAT IS MADE: NO
SCOPE, NO WRITTEN VALUE, NO PIN. Theorems on public data. A law file; no running text imports it.

WHY IT HOLDS. `index` and `w` are `find?`s over the plan's entries with the silent default (0, 0).
W: the planner's list of sendings ends with the literal label "W" (Johnson/G/Sends.lean: wSend;
sendsFrom); its first oracle message is W itself (OnBytes/Iop/Lin.lean: linMessageW), which has a
sample by the shape's own test (LinShape.ok: vectorMessageOk), and the planner's sizing runs that
test (sized_tests, OnBytes/Params/Fit/TreesSized.lean). THE START: the list begins with the literal
label "link 0, moment 0" (frameSends), which `segOf` reads back; the first group keeps nothing
(reqGroupAt at no message alive), so the roles are: the link's own messages of moment 0, the fold's
mask, what rides at the start; just one message rides there (proofSized_request), with a sample
(reqShapeOk, which the sizing runs too). At each sending the rule that lays oracle messages into
trees returns: sendsFrom's own test against the plan.
  `wThereB`, `startSmpdB`   two small tests with code.
  `made_parts`      what the making of Z holds: a return of sendsFrom with the first chain's list
                    fifth; a return of the planner's sizing.
  `entryAt`, `planSeats_has`   the entry that planSeats lays for a sending's oracle message.
  `w_there`         ProofFile.pureRoad.pub o pol lay KL = .ok Z ⊢ wThereB (planSeats Z dl) = true. NO
                    OTHER PREMISE.
  `start_smpd`      the same and hS ⊢ startSmpdB (planSeats Z dl) = true.
  `w_mem`, `index_mem`   from the small tests to the memberships.
  `ends_of_made`    pub … = .ok Z · hS ⊢ the two memberships, as one Bool, in endsThere's own
                    text at numbersOf's index and w.

Limits. ONE PREMISE STAYS: hS : Z.made.p.chains.made.sized.proof.request = Z.first.shape:
planSeats takes the ROLES off the shape that is read back from the first chain's parameter bytes and
the SENDINGS off the planner's sizes. The kind K2's lot asks that equation (P1K2.tied,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) and gives no sub-protocol where it fails: that "the
description is made" gives it is NOT SHOWN HERE. That N Zp cF has numbersOf's index and w
(withRows and withTold turn neither) is not said here: its files are not imported. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.MadeSends
import Johnson.P5T.NumbersOf
import Johnson.Desc.ProofFile.Law.PlainIsMade
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.Goal.Numbers.PlanTauInScope
import Johnson.Goal.Conditions.LinkTypedAtLines
import OnBytes.Params.Fit.TreesSized
import OnBytes.Model.VerifyDerives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (Listed Sending ChainSends frameSends wSend)
open VerifiableInference.Number (sendsFrom packMade)
open P5T (PSeat planSeats numbersOf)

/-- An entry of the label "W" with a sample is there. -/
def wThereB (ps : List PSeat) : Bool := ps.any fun p => p.label == "W" && p.smpd

/-- The first entry of the role "at the start" is there and has a sample. -/
def startSmpdB (ps : List PSeat) : Bool := (ps.find? (·.isStart)).any (·.smpd)

/-- **What the making of Z holds**: the list of sendings is a return of sendsFrom at what the
planner has made, with the first chain's list fifth; and the sizes are a return of the planner's
sizing. -/
theorem made_parts {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    (∃ k0 k1 k2 e p1 p2,
      sendsFrom Z.made.p.chains.made = .ok [k0, k1, k2, e, Z.made.proof.1, p1, p2]) ∧
      ∃ l x, sized l x = .ok Z.made.p.chains.made.sized := by
  obtain ⟨m, hm, hb⟩ := ProofFile.Law.pub_madeOfAtO h
  unfold VerifiableInference.PlanWritten.madeOfAtO at hm
  obtain ⟨p, hp, hm⟩ := exc_bind hm
  obtain ⟨s, hs, hm⟩ := exc_bind hm
  have ep := VerifiableInference.Number.packMade_p hm
  obtain ⟨_, hc⟩ := VerifiableInference.PlanWritten.plannedAtO_parts hp
  obtain ⟨shapes, hcf⟩ := OnBytes.Model.Verify.chainsOf_made hc
  have hz := configure_sized hcf
  have e1 : Z.made.p.chains = p.chains := by
    rw [← hb, ← ep]
    rfl
  have e2 : Z.made.proof = m.proof := by
    rw [← hb]
    rfl
  rw [e1, e2]
  refine ⟨?_, _, _, hz⟩
  unfold packMade at hm
  split at hm
  · cases hm
    exact ⟨_, _, _, _, _, _, hs⟩
  · cases hm

/-- What the prover's message with W holds begins with W. -/
theorem linW_head {S : LinShape} {a : Array OracleNotice} (h : linMessageW S = some a) :
    ∃ tl, a.toList = ⟨S.w, S.wLeafClass⟩ :: tl := by
  refine ⟨a.toList.tail, ?_⟩
  unfold linMessageW at h
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  split at h
  · obtain ⟨y, _, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    split <;> simp
  · cases h
    split <;> simp

/-- W has a sample, by the shape's own test. -/
theorem w_answers {S : LinShape} (h : S.ok = true) : 0 < S.w.answers := by
  unfold LinShape.ok at h
  simp only [Bool.and_eq_true] at h
  have hv := h.1.1.1.1.1.1.1.2
  unfold LinShape.vectorMessageOk at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact hv.2

/-- The entry that `planSeats` lays for oracle message i of sending s, the n-th of the list. -/
def entryAt (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (s : Sending) (n : Nat) (ly : TreeLay)
    (i : Nat) : PSeat :=
  { label := s.label, send := n
    seg := P5T.segOf ((reqGroups Z.first.shape).toList.length + 1) 16 s.label, idx := i
    j := P5T.rootsBefore dl (s.entry - 1) + ly.tree.getD i 0, t := ly.part.getD i 0
    shape := (s.sent.getD i default).shape
    role := (match P5T.segOf ((reqGroups Z.first.shape).toList.length + 1) 16 s.label with
      | some (l, m) => P5T.rolesOf Z.first.shape (reqGroups Z.first.shape).toList l m
      | none => []).getD i P5T.Role.other }

theorem planSeats_has {Z : ProofFile.Pub} {dl : List Fmt.DeclaredRound} {s : Sending} {n : Nat}
    {ly : TreeLay} (hzi : (s, n) ∈ Z.made.proof.1.sends.zipIdx)
    (hly : layTrees Z.made.proof.1.codes s.sent.toArray = some ly) {i : Nat}
    (hi : i < s.sent.length) : entryAt Z dl s n ly i ∈ planSeats Z dl := by
  refine List.mem_flatMap.2 ⟨(s, n), hzi, ?_⟩
  dsimp only
  rw [hly]
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem lay_some {cs : Codes} {sent : Array OracleNotice} (h : (treesOf cs sent).isSome = true) :
    ∃ ly, layTrees cs sent = some ly := by
  unfold treesOf at h
  cases hq : layTrees cs sent with
  | none => rw [hq] at h; cases h
  | some ly => exact ⟨ly, rfl⟩

/-- **An entry of the label "W" with a sample is there.** -/
theorem w_there {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (dl : List Fmt.DeclaredRound) :
    wThereB (planSeats Z dl) = true := by
  obtain ⟨⟨k0, k1, k2, e, p1, p2, hs⟩, l, x, hz⟩ := made_parts h
  obtain ⟨w, hw, hc, hmap, htr⟩ := sendsFrom_first hs
  have hok := linOk_ok (sized_tests hz).1
  unfold wSend at hw
  split at hw
  · rename_i a ha
    cases hw
    obtain ⟨tl, htl⟩ := linW_head ha
    have hmem : (("W", a.toList) : String × List OracleNotice) ∈
        Z.made.proof.1.sends.map (fun s => (s.label, s.sent)) := by
      rw [hmap, List.map_append]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    obtain ⟨s, hsm, hse⟩ := List.mem_map.1 hmem
    obtain ⟨e1, e2⟩ := Prod.mk.inj hse
    obtain ⟨n, hn, hg⟩ := List.mem_iff_getElem.1 hsm
    have hzi : (s, n) ∈ Z.made.proof.1.sends.zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (by rw [List.getElem?_eq_getElem hn, hg])
    obtain ⟨ly, hly⟩ := lay_some (htr s hsm)
    unfold wThereB
    refine List.any_eq_true.2 ⟨entryAt Z dl s n ly 0,
      planSeats_has hzi hly (by rw [e2, htl]; simp), ?_⟩
    have h0 : (s.sent.getD 0 default).shape = Z.made.p.chains.made.sized.proof.batch.shape.w := by
      rw [e2, htl]
      rfl
    simp only [entryAt, PSeat.smpd, e1, h0, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
    exact w_answers hok
  · cases hw

/-! ## The first entry at the start -/

/-- The first hit in a list made over a stretch of numbers. -/
theorem firstHit_from {β : Type} (mk : Nat → β) (P : β → Bool) (j : Nat) (hP : P (mk j) = true) :
    ∀ (n s : Nat), s ≤ j → j < s + n → (∀ i, s ≤ i → i < j → P (mk i) = false) →
      ((List.range' s n).map mk).find? P = some (mk j)
  | 0, s, h1, h2, _ => by omega
  | n + 1, s, h1, h2, h3 => by
    rw [List.range'_succ, List.map_cons]
    by_cases e : s = j
    · subst e
      rw [List.find?_cons_of_pos hP]
    · rw [List.find?_cons_of_neg (by rw [h3 s (Nat.le_refl _) (by omega)]; simp)]
      exact firstHit_from mk P j hP n (s + 1) (by omega) (by omega) fun i a b => h3 i (by omega) b

theorem firstHit_range {β : Type} (mk : Nat → β) (P : β → Bool) (n j : Nat) (hj : j < n)
    (hP : P (mk j) = true) (hlt : ∀ i, i < j → P (mk i) = false) :
    ((List.range n).map mk).find? P = some (mk j) := by
  rw [List.range_eq_range']
  exact firstHit_from mk P j hP n 0 (Nat.zero_le _) (by omega) fun i _ b => hlt i b

/-- As many with their numbers as without. -/
theorem zipIdx_filter_length {α : Type} (l : List α) (q : α → Bool) :
    (l.zipIdx.filter fun x => q x.1).length = (l.filter q).length := by
  have e : l.filter q = (l.zipIdx.filter fun x => q x.1).map (·.1) := by
    conv_lhs => rw [← List.zipIdx_map_fst 0 l]
    rw [List.filter_map]
    rfl
  rw [e, List.length_map]

/-- The label of the first link's first sending is read back. -/
theorem segOf_zero (n : Nat) : P5T.segOf (n + 1) 16 s!"link {0}, moment 0" = some (0, 0) := by
  unfold P5T.segOf
  rw [List.range_succ_eq_map (n := n), List.findSome?_cons]
  rfl

/-- The groups begin with the first link's, which keeps nothing. -/
theorem groups_head (S : ReqShape) :
    ∃ g gs, (reqGroups S).toList = g :: gs ∧ g.target.kept = #[] ∧ g.born = #[] := by
  rw [reqGroups_eq]
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- The frame's sendings begin with the first link's first. -/
theorem frame_head (z : ProofSized) (a : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (hk : g.target.kept = #[]) :
    ∃ tl, frameSends z a 0 (g :: gs) links =
      ⟨s!"link {0}, moment 0",
        ((((links.head?.map (·.messages)).getD []).filter fun m => m.moment == 0).map
          fun m => (⟨m.shape, m.leafClass⟩ : OracleNotice)) ++
          [foldMaskNotice (ioppFoldShape ⟨z.request.code, z.request.maskCode, g.k, g.h⟩ {})] ++
          z.request.atStart⟩ :: tl := by
  unfold frameSends
  have e : keptOf g = [] := by
    unfold keptOf
    rw [hk]
  simp only [e, Nat.lt_irrefl, if_false, List.map_nil, List.nil_append, beq_self_eq_true, if_true,
    List.append_nil]
  split <;> exact ⟨_, rfl⟩

/-- Three stretches of a list. -/
theorem getD_three {α : Type} (A : List α) (x : α) (B : List α) (d : α) :
    (∀ i, i < A.length → (A ++ [x] ++ B).getD i d = A.getD i d) ∧
      (A ++ [x] ++ B).getD A.length d = x ∧
      ∀ i, (A ++ [x] ++ B).getD (A.length + 1 + i) d = B.getD i d := by
  refine ⟨fun i hi => ?_, ?_, fun i => ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left hi]
  · rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_append, List.length_singleton]
    congr 2
    omega

/-- The roles of the first link's first sending, where its group keeps nothing. -/
theorem roles_zero (S : ReqShape) (g : ReqGroup) (gs : List ReqGroup) (hb : g.born = #[]) :
    P5T.rolesOf S (g :: gs) 0 0 =
      ((((S.link[0]?).map (·.messages)).getD []).zipIdx.filter fun x => x.1.moment == 0).map
        (fun x => P5T.Role.own x.2) ++ [P5T.Role.mask] ++
        (List.range S.atStart.length).map P5T.Role.atStart := by
  unfold P5T.rolesOf
  simp [hb]

/-- What rides at the start has a sample, by the shape's own test. -/
theorem start_answers {s : ReqShape} (h : reqShapeOk s = true) :
    ∀ n ∈ s.atStart, 0 < n.shape.answers := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro n hn
  have t := List.all_eq_true.1 h.1.1.1.1.2 n hn
  simp only [Bool.and_eq_true, beq_iff_eq] at t
  have a1 := h.1.1.1.1.1.1.1.2
  have a2 := t.1.2
  omega

/-- **The first entry at the start is there and has a sample**, where the sizes' request's shape
is the shape that is read back from the first chain's parameter bytes. -/
theorem start_smpd {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hS : Z.made.p.chains.made.sized.proof.request = Z.first.shape) (dl : List Fmt.DeclaredRound) :
    startSmpdB (planSeats Z dl) = true := by
  obtain ⟨⟨k0, k1, k2, e, p1, p2, hs⟩, l, x, hz⟩ := made_parts h
  obtain ⟨w, hw, hc, hmap, htr⟩ := sendsFrom_first hs
  obtain ⟨_, hreq, _⟩ := sized_tests hz
  obtain ⟨_, _, nt, hat⟩ := proofSized_request (sized_proof hz)
  have hans : 0 < nt.shape.answers :=
    start_answers (reqOk_shape hreq) nt (by rw [hat]; exact List.mem_singleton.2 rfl)
  have hat' : Z.first.shape.atStart = [nt] := by rw [← hS]; exact hat
  obtain ⟨g, gs, hg, hk, hb⟩ := groups_head Z.first.shape
  obtain ⟨tl, hfr⟩ := frame_head Z.made.p.chains.made.sized.proof
    Z.made.p.chains.made.sized.set.samples g gs Z.first.shape.link hk
  rw [hS, hg, hfr, hat] at hmap
  cases hsd : Z.made.proof.1.sends with
  | nil =>
    rw [hsd] at hmap
    simp at hmap
  | cons s0 rest =>
    rw [hsd, List.cons_append, List.map_cons, List.map_cons] at hmap
    obtain ⟨h0, _⟩ := List.cons.inj hmap
    obtain ⟨e1, e2⟩ := Prod.mk.inj h0
    obtain ⟨ly, hly⟩ := lay_some (htr s0 (by rw [hsd]; exact List.mem_cons_self ..))
    obtain ⟨B, hps⟩ : ∃ B, planSeats Z dl =
        (List.range s0.sent.length).map (entryAt Z dl s0 0 ly) ++ B := by
      unfold planSeats
      dsimp only
      rw [hsd, List.zipIdx_cons, List.flatMap_cons]
      dsimp only
      rw [hly]
      exact ⟨_, rfl⟩
    have hrole : ∀ i, (entryAt Z dl s0 0 ly i).role =
        ((((((Z.first.shape.link[0]?).map (·.messages)).getD []).zipIdx.filter
          fun x => x.1.moment == 0).map (fun x => P5T.Role.own x.2)) ++ [P5T.Role.mask] ++
          [P5T.Role.atStart 0]).getD i P5T.Role.other := by
      intro i
      show (match P5T.segOf ((reqGroups Z.first.shape).toList.length + 1) 16 s0.label with
        | some (l, m) => P5T.rolesOf Z.first.shape (reqGroups Z.first.shape).toList l m
        | none => []).getD i P5T.Role.other = _
      rw [e1, segOf_zero, hg]
      show (P5T.rolesOf Z.first.shape (g :: gs) 0 0).getD i P5T.Role.other = _
      rw [roles_zero _ g gs hb, hat']
      rfl
    have hlen : ((((Z.first.shape.link[0]?).map (·.messages)).getD []).zipIdx.filter
        fun x => x.1.moment == 0).length =
        ((((Z.first.shape.link.head?).map (·.messages)).getD []).filter
          fun m => m.moment == 0).length := by
      rw [List.head?_eq_getElem?]
      exact zipIdx_filter_length _ fun m : ReqMessage => m.moment == 0
    generalize hA : ((((Z.first.shape.link[0]?).map (·.messages)).getD []).zipIdx.filter
        fun x => x.1.moment == 0) = A at hrole hlen
    generalize hA' : ((((Z.first.shape.link.head?).map (·.messages)).getD []).filter
        fun m => m.moment == 0) = A' at e2 hlen
    obtain ⟨r1, r2, r3⟩ := getD_three (A.map fun x => P5T.Role.own x.2) P5T.Role.mask
      [P5T.Role.atStart 0] P5T.Role.other
    obtain ⟨_, _, t3⟩ := getD_three (A'.map fun m => (⟨m.shape, m.leafClass⟩ : OracleNotice))
      (foldMaskNotice (ioppFoldShape ⟨Z.made.p.chains.made.sized.proof.request.code,
        Z.made.p.chains.made.sized.proof.request.maskCode, g.k, g.h⟩ {})) [nt] default
    rw [List.length_map] at r1 r2 r3 t3
    have hfind : ((List.range s0.sent.length).map (entryAt Z dl s0 0 ly)).find? (·.isStart) =
        some (entryAt Z dl s0 0 ly (A.length + 1)) := by
      refine firstHit_range _ _ _ _ ?_ ?_ fun i hi => ?_
      · rw [e2]
        simp only [List.length_append, List.length_map, List.length_singleton]
        omega
      · show (match (entryAt Z dl s0 0 ly (A.length + 1)).role with
          | .atStart _ => true | _ => false) = true
        rw [hrole, show A.length + 1 = A.length + 1 + 0 from rfl, r3]
        rfl
      · show (match (entryAt Z dl s0 0 ly i).role with
          | .atStart _ => true | _ => false) = false
        rw [hrole]
        rcases Nat.lt_or_ge i A.length with hi' | hi'
        · rw [r1 i hi', List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem hi']
          rfl
        · obtain rfl : i = A.length := by omega
          rw [r2]
    unfold startSmpdB
    rw [hps, List.find?_append, hfind]
    show decide (0 < (s0.sent.getD (A.length + 1) default).shape.answers) = true
    rw [e2, hlen, show A'.length + 1 = A'.length + 1 + 0 from rfl, t3]
    exact decide_eq_true hans

/-! ## The two memberships -/

theorem w_mem (ps : List PSeat) (h : wThereB ps = true) :
    (numbersOf ps).w ∈ (ps.filter (·.smpd)).map (·.seat) := by
  show ((ps.find? fun p => p.label == "W" && p.smpd).map (·.seat)).getD (0, 0) ∈ _
  cases e : ps.find? fun p => p.label == "W" && p.smpd with
  | none =>
    obtain ⟨p, hp, hq⟩ := List.any_eq_true.1 h
    exact absurd hq (by simpa using List.find?_eq_none.1 e p hp)
  | some p =>
    have h1 := List.find?_some e
    simp only [Bool.and_eq_true] at h1
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_of_find?_eq_some e, h1.2⟩, rfl⟩

theorem index_mem (ps : List PSeat) (h : startSmpdB ps = true) :
    (numbersOf ps).index ∈ (ps.filter (·.smpd)).map (·.seat) := by
  show ((ps.find? (·.isStart)).map (·.seat)).getD (0, 0) ∈ _
  unfold startSmpdB at h
  cases e : ps.find? (·.isStart) with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨List.mem_of_find?_eq_some e, h⟩, rfl⟩

/-- **The two memberships, wherever Z is made.** -/
theorem ends_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hS : Z.made.p.chains.made.sized.proof.request = Z.first.shape) (dl : List Fmt.DeclaredRound) :
    ((((planSeats Z dl).filter (·.smpd)).map (·.seat)).contains (numbersOf (planSeats Z dl)).index
      && (((planSeats Z dl).filter (·.smpd)).map (·.seat)).contains
        (numbersOf (planSeats Z dl)).w) = true := by
  rw [Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem]
  exact ⟨index_mem _ (start_smpd h hS dl), w_mem _ (w_there h dl)⟩

/-! ## Negative tests of the two small tests -/

/-- An entry, by its label, its role and its number of answers. -/
def toyAt (label : String) (role : P5T.Role) (answers : Nat) : PSeat :=
  { label := label, send := 0, seg := none, idx := 0, j := 0, t := 0,
    shape := { (default : OracleShape) with answers := answers }, role := role }

theorem w_bites : wThereB [] = false ∧ wThereB [toyAt "W" .other 0] = false ∧
    wThereB [toyAt "W" .other 1] = true := by decide

theorem start_bites : startSmpdB [] = false ∧
    startSmpdB [toyAt "" (.atStart 0) 0, toyAt "" (.atStart 1) 1] = false ∧
    startSmpdB [toyAt "" (.atStart 0) 1] = true := by decide

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ends_of_made
#print axioms VerifiableInference.Desc.LinkJoin.w_bites
#print axioms VerifiableInference.Desc.LinkJoin.start_bites
#print axioms VerifiableInference.Desc.LinkJoin.start_smpd
#print axioms VerifiableInference.Desc.LinkJoin.made_parts
#print axioms VerifiableInference.Desc.LinkJoin.w_there
