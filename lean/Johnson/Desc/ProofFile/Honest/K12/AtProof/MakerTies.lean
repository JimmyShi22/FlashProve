-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/MakerTies.lean

What it proves. Laws on the text of the maker of the book of random values: "one owner and one
start": the entry by which a fold spends a fresh table that was sent ahead (foldEntries,
Honest/BookFolds.lean) and the entry by which a part carries that table whole (SentMsg.carry at a
message of sentIn, Honest/BookCarry.lean) have one owner and one start. General in the chain's
sub-protocols and in the library's list of sendings, which is a letter: so at every plan. No premise
on a label: both functions leave out the same sendings, whichever these are.

Names.
  main_fresh, maskStart_fresh   at a fresh table the coefficients begin where the message begins.
  takeWhile_fst, tie_facts   helpers.
  mapM_mem, mapM_back           on List.mapM at Except: each member of the return comes of a member
      of the list, and each member of the list has its return.
  spent_is_sent, sent_is_spent, carry_ties   the laws.
  sent_round, addrOfRound_lt   two small ones for a caller.

By what. The texts of addrIn, planOf, foldBehind, freshOf, foldEntries (Honest/BookFolds.lean),
addrOfRound, seedRounds, foldK, isFresh, msgDue, sendDue, maskStart (Honest/BookRows.lean),
msgStretch (Honest/BookCoins.lean), sentIn, SentMsg.carry (Honest/BookCarry.lean); ProofFile's ex_map and
mapM_all (Honest/BookSharedKit.lean); of the writers of the hash build's side: that the maker's twin
texts agree: addrIn_planOf, planOf_rounds, foldBehind_foldK (Honest/K14/BookMakers.lean).

Limits.
- Laws on two of the maker's functions, not on the book that bookWhole returns: for that see
  MakerBook.lean and MakerBookU.lean.
- "One" is "the same", not "only one": nothing here says that no two entries bear one owner and
  start (the book's own test on that is another law).
- The tie is by sender, start, round and the mark "fresh": not by the message's number, which the
  carrying entry's name bears.
- Nothing on a count but the spent run's 2 k + 1; nothing on which messages make a group.
- Where a fold sends its own fresh table there is no such entry: another road.
- They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K14.BookMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block)
open ProofFile.Honest.BookShared (ex_map mapM_all)
open ProofFile.Honest.K14 (addrIn_planOf planOf_rounds foldBehind_foldK)

theorem takeWhile_fst {α : Type} (p : α → Bool) : ∀ l : List (α × ℕ),
    (l.takeWhile fun r => p r.1).length = ((l.map (·.1)).takeWhile p).length
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.takeWhile_cons, List.takeWhile_cons]
    cases p a.1 with
    | true =>
      show (List.takeWhile (fun r => p r.1) l).length + 1 = _ + 1
      rw [takeWhile_fst p l]
    | false => rfl

/-- In front of a fresh table's coefficients the message has no random value: no main row. -/
theorem main_fresh (codes : OnBytes.Codes) (k : ℕ) (n : OnBytes.OracleNotice) (d : MsgDue)
    (hf : isFresh n = true) (h : msgDue codes k n = some d) : d.main = ⟨0, 0⟩ := by
  unfold isFresh at hf
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hf
  obtain ⟨⟨h0, h1⟩, h2⟩ := hf
  unfold msgDue at h
  simp only [h0, beq_self_eq_true, if_true, Option.bind_some] at h
  obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold MsgDue.main
  simp only [Nat.zero_mul, h2, beq_self_eq_true, if_true, bne_self_eq_false, Bool.and_false,
    Bool.false_eq_true, if_false, Nat.add_zero]
  split <;> rfl

/-- **One start**: where message number j of a sending is a fold's fresh table, the place at which
its coefficients begin among the sender's random values (what a fold's spending entry is laid at) is
the place at which the whole message begins (what a carrying entry is laid at). -/
theorem maskStart_fresh (codes : OnBytes.Codes) (k : ℕ) (ns : List OnBytes.OracleNotice) (j : ℕ)
    (n : OnBytes.OracleNotice) (hj : ns[j]? = some n) (hf : isFresh n = true) :
    maskStart codes k ns j = (msgStretch codes k ns j).map (·.1) := by
  unfold maskStart msgStretch
  rw [hj]
  cases sendDue codes k (ns.take j) with
  | none => rfl
  | some a =>
    show ((msgDue codes k n).map fun d => a.plus d.main) =
      ((msgDue codes k n).map fun d => (a, d.all)).map (·.1)
    cases hd : msgDue codes k n with
    | none => rfl
    | some d =>
      show some (a.plus d.main) = some a
      rw [main_fresh codes k n d hf hd]
      rfl

/-- Each member of what List.mapM returns comes of a member of the list. -/
theorem mapM_mem {α β : Type} (f : α → Except String β) (l : List α) (out : List β)
    (h : l.mapM f = .ok out) : ∀ y ∈ out, ∃ x ∈ l, f x = .ok y :=
  mapM_all (P := fun y => ∃ x ∈ l, f x = .ok y) l out (fun a ha _ hb => ⟨a, ha, hb⟩) h

/-- Each member of the list has its return among what List.mapM returns. -/
theorem mapM_back {α β : Type} (f : α → Except String β) : ∀ (l : List α) (out : List β),
    l.mapM f = .ok out → ∀ x ∈ l, ∃ y ∈ out, f x = .ok y
  | [], _, _, x, hx => by cases hx
  | a :: l, out, h, x, hx => by
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
        obtain rfl : b :: bs = out := Except.ok.inj h'
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨b, List.mem_cons_self, ha⟩
        · obtain ⟨y, hy, e⟩ := mapM_back f l bs hl x hx'
          exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

/-- What the two functions read at one fresh message agrees: the owner and the start. -/
theorem tie_facts {S Cl : Type} (bs : List (Block S Cl)) (L : List PlanB) (codes : OnBytes.Codes)
    (ns : List OnBytes.OracleNotice) (n : OnBytes.OracleNotice) (i j f k : ℕ) (o a : Addr)
    (st : Due) (st' : Due × Due) (hj : ns[j]? = some n) (hf : isFresh n = true)
    (hfb : foldBehind (planOf bs ++ L) i = some (f, false, k))
    (ho : addrIn (planOf bs) i = some o) (hst : maskStart codes k ns j = some st)
    (ha : addrOfRound bs i = some a)
    (hs : msgStretch codes
      ((foldK ((bs.flatMap (·.rounds) ++ L.flatMap (·.rounds)).drop (i + 1))).getD 0) ns j =
        some st') : o = a ∧ st = st'.1 := by
  have hk := foldBehind_foldK hfb
  rw [List.flatMap_append, planOf_rounds] at hk
  rw [hk] at hs
  have hs' : msgStretch codes k ns j = some st' := hs
  rw [addrIn_planOf, ha] at ho
  rw [maskStart_fresh codes k ns j n hj hf, hs'] at hst
  exact ⟨(Option.some.inj ho).symm, (Option.some.inj hst).symm⟩

/-- **One owner and one start, at every plan: each spending entry is a listed fresh message's.** bs:
a chain's sub-protocols. L: the chain behind it in which a table is spent that no fold of this chain
follows. c: the library's sendings of the chain: a letter. Where the maker's foldEntries returns es
and its sentIn returns ms: each entry of es is marked as spent, bears the name of its spender's
fold, counts 2 k + 1 values of the extension field, and has the owner and the start of a message of
ms that is a fold's fresh table; its spender holds the first "FOLD epsilon" behind that message's
round, a fold of k rounds that sends no root of its own. No premise on a label: both functions leave
out the same sendings, whichever these are. -/
theorem spent_is_sent {S Cl : Type} (bs : List (Block S Cl)) (L : List PlanB)
    (c : Johnson.G.ChainSends) (es : List Ahead) (ms : List SentMsg)
    (he : foldEntries (planOf bs) L c = .ok es)
    (hm : sentIn bs c (L.flatMap (·.rounds)) = .ok ms) :
    ∀ e ∈ es, ∃ m ∈ ms, ∃ f k : ℕ, m.fresh = true ∧
      foldBehind (planOf bs ++ L) m.round = some (f, false, k) ∧
      addrIn (planOf bs ++ L) f = some e.spender ∧
      e = ⟨runName foldMaskRun e.spender "fold", m.sender, m.start, ⟨0, 2 * k + 1⟩, e.spender,
        true⟩ := by
  intro e he'
  unfold foldEntries at he
  rw [planOf_rounds] at he
  unfold sentIn at hm
  dsimp only at he
  split at he
  · cases he
  split at hm
  · cases hm
  obtain ⟨ll, hll, rfl⟩ := ex_map he
  obtain ⟨mm, hmm, rfl⟩ := ex_map hm
  obtain ⟨l1, hl1, hel⟩ := List.mem_flatten.1 he'
  obtain ⟨x, hx, hin⟩ := mapM_mem _ _ _ hll l1 hl1
  obtain ⟨j, hj, hG⟩ := mapM_mem _ _ _ hin e hel
  obtain ⟨nj, hnj, ej⟩ := List.mem_map.1 hj
  obtain ⟨hz, hfr⟩ := List.mem_filter.1 hnj
  obtain ⟨l2, hl2, hin2⟩ := mapM_back _ _ _ hmm x hx
  obtain ⟨m, hm2, hH⟩ := mapM_back _ _ _ hin2 nj hz
  have hget : x.2.sent[nj.2]? = some nj.1 := List.mem_zipIdx_iff_getElem?.1 hz
  subst ej
  split at hG
  · cases hG
  · cases hG
  · rename_i f k hfb
    split at hG
    · rename_i o p st ho hp hst
      split at hH
      · rename_i a st' ha hs
        obtain rfl := Except.ok.inj hG
        obtain rfl := Except.ok.inj hH
        obtain ⟨rfl, rfl⟩ := tie_facts bs L c.codes x.2.sent nj.1 x.1 nj.2 f k o a st st' hget hfr
          hfb ho hst ha hs
        exact ⟨_, List.mem_flatten.2 ⟨l2, hl2, hm2⟩, f, k, hfr, hfb, hp, rfl⟩
      · cases hH
    · cases hG

/-- **And each listed fresh message has such an entry**: with the message's sender and start, marked
as spent; its spender holds the first "FOLD epsilon" behind the message's round. -/
theorem sent_is_spent {S Cl : Type} (bs : List (Block S Cl)) (L : List PlanB)
    (c : Johnson.G.ChainSends) (es : List Ahead) (ms : List SentMsg)
    (he : foldEntries (planOf bs) L c = .ok es)
    (hm : sentIn bs c (L.flatMap (·.rounds)) = .ok ms) :
    ∀ m ∈ ms, m.fresh = true → ∃ e ∈ es, ∃ f k : ℕ,
      foldBehind (planOf bs ++ L) m.round = some (f, false, k) ∧
      addrIn (planOf bs ++ L) f = some e.spender ∧
      e = ⟨runName foldMaskRun e.spender "fold", m.sender, m.start, ⟨0, 2 * k + 1⟩, e.spender,
        true⟩ := by
  intro m hm' hfresh
  unfold foldEntries at he
  rw [planOf_rounds] at he
  unfold sentIn at hm
  dsimp only at he
  split at he
  · cases he
  split at hm
  · cases hm
  obtain ⟨ll, hll, rfl⟩ := ex_map he
  obtain ⟨mm, hmm, rfl⟩ := ex_map hm
  obtain ⟨l2, hl2, hml⟩ := List.mem_flatten.1 hm'
  obtain ⟨x, hx, hin2⟩ := mapM_mem _ _ _ hmm l2 hl2
  obtain ⟨nj, hz, hH⟩ := mapM_mem _ _ _ hin2 m hml
  have hget : x.2.sent[nj.2]? = some nj.1 := List.mem_zipIdx_iff_getElem?.1 hz
  split at hH
  · rename_i a st' ha hs
    obtain rfl := Except.ok.inj hH
    have hfr : isFresh nj.1 = true := hfresh
    have hj : nj.2 ∈ freshOf x.2.sent :=
      List.mem_map.2 ⟨nj, List.mem_filter.2 ⟨hz, hfr⟩, rfl⟩
    obtain ⟨l1, hl1, hin⟩ := mapM_back _ _ _ hll x hx
    obtain ⟨e, hel, hG⟩ := mapM_back _ _ _ hin nj.2 hj
    split at hG
    · cases hG
    · cases hG
    · rename_i f k hfb
      split at hG
      · rename_i o p st ho hp hst
        obtain rfl := Except.ok.inj hG
        obtain ⟨rfl, rfl⟩ := tie_facts bs L c.codes x.2.sent nj.1 x.1 nj.2 f k o a st st' hget hfr
          hfb ho hst ha hs
        exact ⟨_, List.mem_flatten.2 ⟨l1, hl1, hel⟩, f, k, hfb, hp, rfl⟩
      · cases hG
  · cases hH

/-- **So a fold's spending entry and the entry by which a part carries that fresh table whole have
one owner and one start.** dest: any address. -/
theorem carry_ties {S Cl : Type} (bs : List (Block S Cl)) (L : List PlanB)
    (c : Johnson.G.ChainSends) (es : List Ahead) (ms : List SentMsg)
    (he : foldEntries (planOf bs) L c = .ok es)
    (hm : sentIn bs c (L.flatMap (·.rounds)) = .ok ms) :
    ∀ m ∈ ms, m.fresh = true → ∃ e ∈ es, ∀ dest : Addr,
      (e.owner, e.start) = ((m.carry dest).owner, (m.carry dest).start) := by
  intro m hm' hfresh
  obtain ⟨e, he', f, k, -, -, h1⟩ := sent_is_spent bs L c es ms he hm m hm' hfresh
  refine ⟨e, he', fun dest => ?_⟩
  show (e.owner, e.start) = (m.sender, m.start)
  rw [h1]

/-- A listed message's sender is the part that holds its round. -/
theorem sent_round {S Cl : Type} (bs : List (Block S Cl)) (c : Johnson.G.ChainSends)
    (later : List Fmt.DeclaredRound) (ms : List SentMsg) (hm : sentIn bs c later = .ok ms) :
    ∀ m ∈ ms, addrOfRound bs m.round = some m.sender := by
  intro m hm'
  unfold sentIn at hm
  split at hm
  · cases hm
  obtain ⟨mm, hmm, rfl⟩ := ex_map hm
  obtain ⟨l2, hl2, hml⟩ := List.mem_flatten.1 hm'
  obtain ⟨x, -, hin2⟩ := mapM_mem _ _ _ hmm l2 hl2
  obtain ⟨nj, -, hH⟩ := mapM_mem _ _ _ hin2 m hml
  split at hH
  · rename_i a st' ha hs
    obtain rfl := Except.ok.inj hH
    exact ha
  · cases hH

/-- A round that a part holds is one of the chain's. -/
theorem addrOfRound_lt {S Cl : Type} : ∀ (bs : List (Block S Cl)) (i : ℕ) (a : Addr),
    addrOfRound bs i = some a → i < (bs.flatMap (·.rounds)).length
  | [], _, _, h => by
    unfold addrOfRound at h
    cases h
  | b :: bs, i, a, h => by
    unfold addrOfRound at h
    rw [List.flatMap_cons, List.length_append]
    split at h
    · rename_i hi
      omega
    · rename_i hi
      have := addrOfRound_lt bs _ a h
      omega

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.takeWhile_fst
#print axioms ProofFile.Honest.K12.AtProof.main_fresh
#print axioms ProofFile.Honest.K12.AtProof.maskStart_fresh
#print axioms ProofFile.Honest.K12.AtProof.mapM_mem
#print axioms ProofFile.Honest.K12.AtProof.mapM_back
#print axioms ProofFile.Honest.K12.AtProof.tie_facts
#print axioms ProofFile.Honest.K12.AtProof.spent_is_sent
#print axioms ProofFile.Honest.K12.AtProof.sent_is_spent
#print axioms ProofFile.Honest.K12.AtProof.carry_ties
#print axioms ProofFile.Honest.K12.AtProof.sent_round
#print axioms ProofFile.Honest.K12.AtProof.addrOfRound_lt
