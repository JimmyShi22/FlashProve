-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SendsListed.lean: what the planner's list of a chain's sendings is, where sendsFrom
(Johnson/G/SendsFrom.lean) returns: the listed sendings' notices and labels, in their order, with
entries that rise. Statements and proofs, over that file alone. No Mathlib.

What for. The list of rounds' side of the facts "seatsCarried" and "msgShapes"
(Johnson/Desc/K12/Door/LaidOfLists.lean: SendsAre) speaks of a chain's sendings sorted by entry.
Here: the sort is idle, and the proof file's first chain's sendings are frameSends' list with W's
sending behind it.
  mapM_ok           what a routine's returns have in common with its arguments, a list's mapM's
                    return has with the list
  oneOf             sendsFrom's inner routine "one", by name: its text
  member_ok         what that routine's step at one listed sending returns
  picked_rise       the numbers of the entries that a test picks rise
  oneOf_ok          where oneOf returns C: C.codes; C.sends' notices and labels are the listed
                    ones'; the entries rise strictly
  sorted_idle       so the sort by entry leaves C.sends as it is
  mapM_id_ok        a list of returns, taken in turn
  sendsFrom_one     sendsFrom is its own text at oneOf: by rfl
  proof_first       where sendsFrom c returns L: L's fifth member is what oneOf returns at
                    frameSends' list with W's sending behind it
  proof_first_sent  that member's codes are the sized proof's, and its notices, sorted by entry, are
                    that list's

Limits. One direction: from routines that return. oneOf is a second text of sendsFrom's lines: it
will have to be turned with them (sendsFrom_one then fails, loudly). Nothing on soundness.

-/
import Johnson.G.SendsFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Params

/-- What a routine's returns have in common with its arguments, a list's mapM's return has with the
list. -/
theorem mapM_ok {α β γ : Type} (f : α → Except String β) (g : β → γ) (g' : α → γ)
    (hg : ∀ a b, f a = .ok b → g b = g' a) : ∀ (l : List α) (out : List β),
    l.mapM f = .ok out → out.map g = l.map g'
  | [], out, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | a :: l, out, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e =>
      rw [ha] at h
      cases h
    | ok b =>
      rw [ha] at h
      have h' : (l.mapM f >>= fun bs => pure (b :: bs)) = Except.ok out := h
      cases hl : l.mapM f with
      | error e =>
        rw [hl] at h'
        cases h'
      | ok bs =>
        rw [hl] at h'
        cases h'
        rw [List.map_cons, List.map_cons, hg a b ha, mapM_ok f g g' hg l bs hl]

/-- sendsFrom's inner routine, by name. -/
def oneOf (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
    Except String ChainSends := do
  let R := P.rounds.toArray
  let seeds := P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed"
  unless seeds.length == l.length do
    throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
  let out ← (seeds.zip l).mapM fun (r, s) => do
    unless treesOf codes s.sent.toArray == some r.1.entry.roots do
      throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
    match R[r.2 + 1]? with
    | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
    | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
  pure ⟨file, ch, codes, out⟩

/-- What one member's routine returns. -/
theorem member_ok (file : String) (ch : Nat) (codes : Codes) (R : Array PlanRound)
    (x : (PlanRound × Nat) × Listed) (b : Sending)
    (h : (do
      unless treesOf codes x.2.sent.toArray == some x.1.1.entry.roots do
        throw s!"{file} {ch}, entry {x.1.2 + 1} ({x.2.label}): the trees are not the entry's roots"
      match R[x.1.2 + 1]? with
      | some b => pure (⟨x.1.2 + 1, x.2.label, x.2.sent, x.1.1.entry, b.entry⟩ : Sending)
      | none => throw s!"{file} {ch}, entry {x.1.2 + 1}: no entry behind it" :
        Except String Sending) = .ok b) :
    b.sent = x.2.sent ∧ b.label = x.2.label ∧ b.entry = x.1.2 + 1 := by
  by_cases ht : (treesOf codes x.2.sent.toArray == some x.1.1.entry.roots) = true
  · simp only [ht] at h
    cases hR : R[x.1.2 + 1]? with
    | none =>
      rw [hR] at h
      cases h
    | some r =>
      rw [hR] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩
  · simp only [ht] at h
    cases h

/-- The numbers of the entries that a test picks rise. -/
theorem picked_rise {α : Type} (l : List α) (p : α × Nat → Bool) :
    ((l.zipIdx.filter p).map fun r => r.2 + 1).Pairwise (· < ·) := by
  have h1 : ((l.zipIdx.filter p).map Prod.snd).Sublist (l.zipIdx.map Prod.snd) :=
    List.Sublist.map _ List.filter_sublist
  rw [List.zipIdx_map_snd] at h1
  have h2 : ((l.zipIdx.filter p).map Prod.snd).Pairwise (· < ·) :=
    List.Pairwise.sublist h1 List.pairwise_lt_range'
  rw [List.pairwise_map] at h2 ⊢
  exact h2.imp fun h => Nat.succ_lt_succ h

/-- **Where the inner routine returns.** -/
theorem oneOf_ok (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned)
    (C : ChainSends) (h : oneOf file ch codes l P = .ok C) :
    C.codes = codes ∧ C.sends.map (·.sent) = l.map (·.sent) ∧
      C.sends.map (·.label) = l.map (·.label) ∧ (C.sends.map (·.entry)).Pairwise (· < ·) := by
  unfold oneOf at h
  by_cases hlen : ((P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").length ==
      l.length) = true
  · simp only [hlen] at h
    have hl : l.length ≤ (P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").length :=
      Nat.le_of_eq (eq_of_beq hlen).symm
    have hl' : (P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").length ≤ l.length :=
      Nat.le_of_eq (eq_of_beq hlen)
    generalize hf : (fun x : (PlanRound × Nat) × Listed => (match x with
      | (r, s) => do
        unless treesOf codes s.sent.toArray == some r.1.entry.roots do
          throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
        match P.rounds.toArray[r.2 + 1]? with
        | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
        | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it" :
          Except String Sending)) = f at h
    have hm : ∀ a b, f a = .ok b →
        b.sent = a.2.sent ∧ b.label = a.2.label ∧ b.entry = a.1.2 + 1 := by
      intro a b hab
      subst hf
      obtain ⟨r, s⟩ := a
      exact member_ok file ch codes P.rounds.toArray (r, s) b hab
    cases ho : ((P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").zip l).mapM f with
    | error e =>
      have h' : (((P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").zip l).mapM f >>=
        fun out => pure (⟨file, ch, codes, out⟩ : ChainSends)) = Except.ok C := h
      rw [ho] at h'
      cases h'
    | ok out =>
      have h' : (((P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed").zip l).mapM f >>=
        fun out => pure (⟨file, ch, codes, out⟩ : ChainSends)) = Except.ok C := h
      rw [ho] at h'
      cases h'
      refine ⟨rfl, ?_, ?_, ?_⟩
      · show out.map (·.sent) = _
        rw [mapM_ok f (·.sent) (fun a => a.2.sent) (fun a b hab => (hm a b hab).1) _ out ho]
        show List.map ((fun s : Listed => s.sent) ∘ Prod.snd) _ = _
        rw [← List.map_map, List.map_snd_zip hl]
      · show out.map (·.label) = _
        rw [mapM_ok f (·.label) (fun a => a.2.label) (fun a b hab => (hm a b hab).2.1) _ out ho]
        show List.map ((fun s : Listed => s.label) ∘ Prod.snd) _ = _
        rw [← List.map_map, List.map_snd_zip hl]
      · show (out.map (·.entry)).Pairwise (· < ·)
        rw [mapM_ok f (·.entry) (fun a => a.1.2 + 1) (fun a b hab => (hm a b hab).2.2) _ out ho]
        show (List.map ((fun r : PlanRound × Nat => r.2 + 1) ∘ Prod.fst) _).Pairwise (· < ·)
        rw [← List.map_map, List.map_fst_zip hl']
        exact picked_rise _ _
  · simp only [hlen] at h
    cases h

/-- **The sort by entry is idle.** -/
theorem sorted_idle (C : ChainSends) (h : (C.sends.map (·.entry)).Pairwise (· < ·)) :
    (C.sends.mergeSort fun a b => a.entry ≤ b.entry) = C.sends := by
  refine List.mergeSort_of_pairwise ?_
  rw [List.pairwise_map] at h
  exact h.imp fun hab => decide_eq_true (Nat.le_of_lt hab)

/-- A list of seven routines' returns, taken in turn. -/
theorem mapM_id_ok {α : Type} : ∀ (l : List (Except String α)) (L : List α),
    l.mapM id = .ok L → l = L.map .ok
  | [], L, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | x :: l, L, h => by
    rw [List.mapM_cons] at h
    cases x with
    | error e => cases h
    | ok a =>
      have h' : (l.mapM id >>= fun bs => pure (a :: bs)) = Except.ok L := h
      cases hl : l.mapM id with
      | error e =>
        rw [hl] at h'
        cases h'
      | ok bs =>
        rw [hl] at h'
        cases h'
        rw [List.map_cons, mapM_id_ok l bs hl]

/-- sendsFrom is its own text at the inner routine's name. -/
theorem sendsFrom_one (c : Configured) : sendsFrom c =
    (match c.key, c.proof with
    | [k0, k1, k2], [p0, p1, p2] => do
      let w1 ← wSend c.sized.key.once.shape
      let s1 ← linSharedSends c.sized.key.once.shape c.sized.set.samples
      let w2 ← wSend c.sized.proof.batch.shape
      let s2 ← linSharedSends c.sized.proof.batch.shape c.sized.set.samples
      [ oneOf "key" 0 c.sized.key.codes
          ([⟨"the index-mask message", [c.sized.key.once.input]⟩,
            ⟨"the multiplicities", (Wf.messageOf c.sized.key.ranges.x).toList⟩] ++
            ioppSends "the ranges' test" c.sized.set.samples c.sized.key.ranges.x.choice.masksRide 1
              c.sized.key.ranges.x.stages ++ [w1]) k0,
        oneOf "key" 1 c.sized.key.codes s1 k1,
        oneOf "key" 2 c.sized.key.codes (ioppSends "the own test" c.sized.set.samples
          c.sized.key.once.shape.choice.masksRide 1 c.sized.key.once.shape.testOwn) k2,
        oneOf "entry" 0 c.sized.entryCodes
          (⟨"the link's message", (linkMessage c.sized.link.shape c.sized.set.samples).toList⟩ ::
            ioppSends "the link's test" c.sized.set.samples c.sized.link.shape.choice.masksRide 1
              c.sized.link.shape.test) c.entry,
        oneOf "proof" 0 c.sized.proof.codes
          (frameSends c.sized.proof c.sized.set.samples 0 (reqGroups c.sized.proof.request).toList
            c.sized.proof.request.link ++ [w2]) p0,
        oneOf "proof" 1 c.sized.proof.codes s2 p1,
        oneOf "proof" 2 c.sized.proof.codes (ioppSends "the own test" c.sized.set.samples
          c.sized.proof.batch.shape.choice.masksRide 1 c.sized.proof.batch.shape.testOwn) p2
      ].mapM id
    | _, _ => throw "the key or the proof has not three plans") := rfl

/-- **The proof file's first chain's list.** -/
theorem proof_first {c : Configured} {L : List ChainSends} (h : sendsFrom c = .ok L) :
    ∃ (P0 : Planned) (W : Listed) (C : ChainSends),
      wSend c.sized.proof.batch.shape = .ok W ∧ L[4]? = some C ∧
      oneOf "proof" 0 c.sized.proof.codes
        (frameSends c.sized.proof c.sized.set.samples 0 (reqGroups c.sized.proof.request).toList
          c.sized.proof.request.link ++ [W]) P0 = .ok C := by
  rw [sendsFrom_one] at h
  split at h
  · rename_i k0 k1 k2 p0 p1 p2 _ _
    cases h1 : wSend c.sized.key.once.shape with
    | error e =>
      rw [h1] at h
      cases h
    | ok w1 =>
      rw [h1] at h
      cases h2 : linSharedSends c.sized.key.once.shape c.sized.set.samples with
      | error e =>
        simp only [bind, Except.bind, h2] at h
        cases h
      | ok s1 =>
        cases h3 : wSend c.sized.proof.batch.shape with
        | error e =>
          simp only [bind, Except.bind, h2, h3] at h
          cases h
        | ok w2 =>
          cases h4 : linSharedSends c.sized.proof.batch.shape c.sized.set.samples with
          | error e =>
            simp only [bind, Except.bind, h2, h3, h4] at h
            cases h
          | ok s2 =>
            simp only [bind, Except.bind, h2, h3, h4] at h
            have e := mapM_id_ok _ L h
            have e4 := congrArg (fun l => l[4]?) e
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_map] at e4
            cases hL : L[4]? with
            | none =>
              rw [hL] at e4
              cases e4
            | some C =>
              rw [hL] at e4
              exact ⟨p0, w2, C, rfl, rfl, Option.some.inj e4⟩
  · cases h

/-- **The sorted notices of the proof file's first chain.** -/
theorem proof_first_sent {c : Configured} {L : List ChainSends} (h : sendsFrom c = .ok L) :
    ∃ (W : Listed) (C : ChainSends), wSend c.sized.proof.batch.shape = .ok W ∧ L[4]? = some C ∧
      C.codes = c.sized.proof.codes ∧
      (C.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent) =
        (frameSends c.sized.proof c.sized.set.samples 0 (reqGroups c.sized.proof.request).toList
          c.sized.proof.request.link ++ [W]).map (·.sent) := by
  obtain ⟨P0, W, C, hW, hC, ho⟩ := proof_first h
  obtain ⟨e1, e2, -, e4⟩ := oneOf_ok _ _ _ _ _ _ ho
  exact ⟨W, C, hW, hC, e1, by rw [sorted_idle C e4, e2]⟩

end Johnson.G

#print axioms Johnson.G.mapM_ok
#print axioms Johnson.G.oneOf_ok
#print axioms Johnson.G.sorted_idle
#print axioms Johnson.G.mapM_id_ok
#print axioms Johnson.G.sendsFrom_one
#print axioms Johnson.G.proof_first
#print axioms Johnson.G.proof_first_sent
