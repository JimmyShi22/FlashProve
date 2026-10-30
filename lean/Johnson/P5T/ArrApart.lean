-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/ArrApart.lean: THE NUMBERING arr OF THE WITNESS's MESSAGES (arrOf, Johnson/P5T/PlanSeats.lean) TELLS THE TENANTS OF ONE LATER CHAIN APART. Definitions and theorems.
WHY. arrOf ps j t is the place of the seat's KEY among the keys of the list ps; at a seat outside ps it is the number of keys: ONE number for every such seat. So arr must be taken over the seats of ALL THREE CHAINS of the proof (planSeatsAll): else the shared chain's three sampled oracle messages would bear one number, and their three pins would pin one component of the witness. With that list the sentence that the shared chain's laws ask ("two tenants with one number are one": harr) holds BY THE MAKE of chainSeats: a seat of a later chain has the key (1, 1000 * chain + the sending's number, the place in the sending): one key a seat.
  arrOf_key: two seats that are found in the list and bear one number have one key.
  chainSeats_mem: what an entry of chainSeats is · chainSeats_one: two seats of one chainSeats list with one key are ONE entry of the list.
  arr_apart: so two seats (j, t), (j', t') at which the list's first entry is an entry of one chainSeats list, and which bear one number, are one seat.
  harr_of: THE SENTENCE ITSELF, general in the type of names M and in tenant : M → ℕ × ℕ: from "every name's tenant is found in the list at an entry of that chainSeats list" (hseat: a test on the plan) and "tenant is one to one" (hten).
  harr_of_test: THE SAME SENTENCE FROM ONE TEST WITH CODE (and hall: the list holds every name), general in arr: the numbers of the listed names' tenants are pairwise different (harrB): so that a run at a real plan can show that the sentence is met there.

Limits. Nothing says that the three tenants ARE seats of the list: hseat is a premise (a test with code on the plan's numbers). Nothing on the first chain's seats: there an original and its kept copies share a number on purpose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.PlanSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- Two seats that are found in the list and bear one number have one key. -/
theorem arrOf_key (ps : List PSeat) (j t j' t' : Nat) (p p' : PSeat)
    (hp : (ps.find? fun q => q.j == j && q.t == t) = some p)
    (hp' : (ps.find? fun q => q.j == j' && q.t == t') = some p')
    (h : arrOf ps j t = arrOf ps j' t') : keyOf p = keyOf p' := by
  unfold arrOf at h
  rw [hp, hp'] at h
  have hm : keyOf p ∈ (ps.map keyOf).eraseDups :=
    List.mem_eraseDups.2 (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp, rfl⟩)
  exact (List.idxOf_inj hm).1 h

/-- What an entry of chainSeats is. -/
theorem chainSeats_mem (chain base : Nat) (c : Johnson.G.ChainSends) (dl : List Fmt.DeclaredRound)
    (p : PSeat) (h : p ∈ chainSeats chain base c dl) :
    ∃ (s : Johnson.G.Sending × Nat) (lay : _) (i : Nat), s ∈ c.sends.zipIdx ∧
      OnBytes.layTrees c.codes s.1.sent.toArray = some lay ∧
      p = { label := s!"chain {chain}, {s.1.label}", send := 1000 * chain + s.2, seg := none, idx := i,
            j := base + rootsBefore dl (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
            shape := (s.1.sent.getD i default).shape, role := .other } := by
  unfold chainSeats at h
  obtain ⟨s, hs, hp⟩ := List.mem_flatMap.1 h
  cases hl : OnBytes.layTrees c.codes s.1.sent.toArray with
  | none => rw [hl] at hp; cases hp
  | some lay =>
    rw [hl] at hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
    exact ⟨s, lay, i, hs, hl, rfl⟩

/-- **Two entries of one chainSeats list with one key are one entry.** -/
theorem chainSeats_one (chain base : Nat) (c : Johnson.G.ChainSends) (dl : List Fmt.DeclaredRound)
    (p p' : PSeat) (h : p ∈ chainSeats chain base c dl) (h' : p' ∈ chainSeats chain base c dl)
    (hk : keyOf p = keyOf p') : p = p' := by
  obtain ⟨s, lay, i, hs, hl, rfl⟩ := chainSeats_mem chain base c dl p h
  obtain ⟨s', lay', i', hs', hl', rfl⟩ := chainSeats_mem chain base c dl p' h'
  have hk' : ((1 : Nat), 1000 * chain + s.2, i) = (1, 1000 * chain + s'.2, i') := hk
  have e1 : s.2 = s'.2 := by
    have := congrArg (fun x : Nat × Nat × Nat => x.2.1) hk'
    simp only at this
    omega
  have e2 : i = i' := congrArg (fun x : Nat × Nat × Nat => x.2.2) hk'
  have es : s = s' := by
    have a := List.mem_zipIdx hs
    have a' := List.mem_zipIdx hs'
    obtain ⟨s1, s2⟩ := s
    obtain ⟨s1', s2'⟩ := s'
    simp only at e1
    subst e1
    simp only [Nat.sub_zero] at a a'
    have : s1 = s1' := by rw [a.2.2, a'.2.2]
    rw [this]
  subst es
  subst e2
  rw [hl] at hl'
  obtain rfl := Option.some.inj hl'
  rfl

/-- **Two seats of one later chain that bear one number are one seat.** -/
theorem arr_apart (ps : List PSeat) (chain base : Nat) (c : Johnson.G.ChainSends)
    (dl : List Fmt.DeclaredRound) (j t j' t' : Nat) (p p' : PSeat)
    (hp : (ps.find? fun q => q.j == j && q.t == t) = some p)
    (hp' : (ps.find? fun q => q.j == j' && q.t == t') = some p')
    (hc : p ∈ chainSeats chain base c dl) (hc' : p' ∈ chainSeats chain base c dl)
    (h : arrOf ps j t = arrOf ps j' t') : (j, t) = (j', t') := by
  have e := chainSeats_one chain base c dl p p' hc hc' (arrOf_key ps j t j' t' p p' hp hp' h)
  have a := List.find?_some hp
  have a' := List.find?_some hp'
  simp only [Bool.and_eq_true, beq_iff_eq] at a a'
  rw [← a.1, ← a.2, ← a'.1, ← a'.2, e]

/-- **harr**: general in the names and in their tenants. -/
theorem harr_of {M : Type} (tenant : M → Nat × Nat) (ps : List PSeat) (chain base : Nat)
    (c : Johnson.G.ChainSends) (dl : List Fmt.DeclaredRound)
    (hseat : ∀ m, ∃ p, (ps.find? fun q => q.j == (tenant m).1 && q.t == (tenant m).2) = some p ∧
      p ∈ chainSeats chain base c dl)
    (hten : ∀ m m', tenant m = tenant m' → m = m') :
    ∀ m m' : M, arrOf ps (tenant m).1 (tenant m).2 = arrOf ps (tenant m').1 (tenant m').2 → m = m' := by
  intro m m' h
  obtain ⟨p, hp, hc⟩ := hseat m
  obtain ⟨p', hp', hc'⟩ := hseat m'
  exact hten m m' (Prod.ext_iff.2 (Prod.ext_iff.1
    (arr_apart ps chain base c dl _ _ _ _ p p' hp hp' hc hc' h)))

/-- A map without a repeat on a list is one to one on it. -/
theorem inj_of_nodup_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by cases hx
  | a :: l, h, x, hx, y, hy, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy', e.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx', e⟩) h.1
    · exact inj_of_nodup_map f l h.2 x hx' y hy' e

/-- THE TEST: the numbers of the listed names' tenants are pairwise different. -/
def harrB {M : Type} (arr : Nat → Nat → Nat) (tenant : M → Nat × Nat) (all : List M) : Bool :=
  decide ((all.map fun m => arr (tenant m).1 (tenant m).2).Nodup)

/-- **harr from the test.** -/
theorem harr_of_test {M : Type} (arr : Nat → Nat → Nat) (tenant : M → Nat × Nat) (all : List M)
    (hall : ∀ m, m ∈ all) (h : harrB arr tenant all = true) :
    ∀ m m' : M, arr (tenant m).1 (tenant m).2 = arr (tenant m').1 (tenant m').2 → m = m' :=
  fun m m' e => inj_of_nodup_map (fun m => arr (tenant m).1 (tenant m).2) all
    (of_decide_eq_true h) m (hall m) m' (hall m') e

/-- A CONTROL: at a numbering that gives every seat one number the test says no, as soon as two names are listed. -/
example : harrB (M := Bool) (fun _ _ => 7) (fun b => (if b then 1 else 0, 0)) [true, false] = false := by decide

end P5T

#print axioms P5T.harr_of_test
#print axioms P5T.arrOf_key
#print axioms P5T.chainSeats_one
#print axioms P5T.arr_apart
#print axioms P5T.harr_of
