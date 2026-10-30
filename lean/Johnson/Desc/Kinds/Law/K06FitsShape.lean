-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06FitsShape.lean: FROM Block.step'S OWN TEST ON THE ROUNDS TO THE SHAPE
ShapedNZ (Law/K06EveryList.lean): the converse of that file's roundsFit_shapedNZ.
WHAT IT IS NOT. No prover, no verifier's yes. Nothing on what the rounds hold, on soundness, on
completeness or on what a proof hides. Nothing on canonical writing: a word of a round may be at or
above the prime. CONDITIONAL: on the test's yes, and on names of rounds that the format knows, of
another kind than "seeds" (knownNoSeeds; rounds_noSeeds has it of the output head's table).
WHY. Law/K06EveryList.lean's tops take ShapedNZ as a premise. Who has rounds that pass roundsFit
(Johnson/Desc/Block.lean), or a challenge that passes drawsMarkedNonzeroHaveNonzeroWords with the three counts, wants that
premise from what is in hand. Block.step shows the decision its rounds without the sealed digest
(noDigest), and rvOf has none: so the shape is concluded of the rounds with the digest struck.
  isZeroE_false_of    three words not all 0: isZeroE says no (triple_ne_zero, Law/StepFits.lean, the
                      other way).
  vals_elems          a message whose items are n elements is the list of n elements' triples.
  mem_zip_replicate   a member of a list, zipped against at least as many copies of one mark.
  kind_of_known       what knownNoSeeds says.
  items_of_round      the items that a round of the table cuts, but for roots: R.sent elements (a
                      step of Law/StepFits.lean's roundFit_one, cut out).
  last_not_zero       ONE CHALLENGE: of as many elements as the round draws, passing drawsMarkedNonzeroHaveNonzeroWords: the last
                      drawNZ, as elements, are not (0,0,0).
  shaped_of_parts     ONE ROUND, FROM ITS PARTS: the sent scalars s and a challenge D with the three
                      counts and drawsMarkedNonzeroHaveNonzeroWords: the round with the digest struck is rvOf s d, with
                      ShapedNZ's three clauses.
  shaped_of_roundFit  ONE ROUND, from the clauses of roundsFit.
  shapedNZ_of_fit     THE ROUNDS: roundsFit at the table's declared rounds gives ShapedNZ of the
                      rounds with the digests struck.
  shapedNZ_of_blockFit   the same at the seated block's own declared rounds.
THE SEAM WITH Law/K06EveryList.lean. Its step_of_heard asks ShapedNZ of rs and concludes the step at
rs; roundsFit asks nothing of a round's digest. Two ways across:
  step_of_fit         FROM roundsFit AT rs AND THE HEARING AT THE ROUNDS WITH THE DIGESTS STRUCK:
                      Block.step says yes at rs (yes_of_heard at rs.map noDigest, then the library's
                      Came.decide_step).
  noDigest_of_none    where no round bears a digest, striking turns nothing.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06EveryList

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Part.MaskedSum (rvOf)
open VerifiableInference.Desc.First (S)

/-- Three words not all 0: isZeroE says no. -/
theorem isZeroE_false_of (x : E) (h : x.triple ≠ (0, 0, 0)) : OnBytes.isZeroE x = false := by
  cases hz : OnBytes.isZeroE x with
  | false => rfl
  | true =>
    exfalso
    apply h
    unfold OnBytes.isZeroE at hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨⟨h0, h1⟩, h2⟩ := hz
    show (x.c0, x.c1, x.c2) = _
    rw [h0, h1, h2]

/-- A message whose items are n elements is the list of n elements' triples. -/
theorem vals_elems : ∀ (vs : List Fmt.ItemValue) (n : Nat),
    vs.map itemOf = List.replicate n Fmt.Item.e →
    ∃ s : List E, s.length = n ∧ vs = s.map fun x => Fmt.ItemValue.e x.triple
  | [], 0, _ => ⟨[], rfl, rfl⟩
  | [], _ + 1, h => by simp [List.replicate_succ] at h
  | _ :: _, 0, h => by simp at h
  | v :: vs, n + 1, h => by
    rw [List.map_cons, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨s, hs, rfl⟩ := vals_elems vs n h2
    cases v with
    | e x => exact ⟨E.ofTriple x :: s, by rw [List.length_cons, hs], rfl⟩
    | f _ => simp [itemOf] at h1
    | word _ => simp [itemOf] at h1
    | root _ => simp [itemOf] at h1
    | answer _ => simp [itemOf] at h1

/-- A member of a list, zipped against at least as many copies of one mark. -/
theorem mem_zip_replicate {α β : Type} (c : α) : ∀ (n : Nat) (l : List β), l.length ≤ n →
    ∀ t ∈ l, (c, t) ∈ (List.replicate n c).zip l
  | _, [], _, _, h => by cases h
  | 0, _ :: _, hl, _, _ => by simp at hl
  | n + 1, b :: l, hl, t, h => by
    rw [List.replicate_succ, List.zip_cons_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_replicate c n l (by simpa using hl) t h)

/-- What knownNoSeeds says. -/
theorem kind_of_known (R : Round) (hk : knownNoSeeds R = true) :
    ∃ k, Fmt.kindOf R.name = some k ∧ k ≠ .seeds := by
  unfold knownNoSeeds at hk
  cases hq : Fmt.kindOf R.name with
  | none =>
    rw [hq] at hk
    cases hk
  | some k =>
    rw [hq] at hk
    exact ⟨k, rfl, by simpa using hk⟩

/-- The items that a round of the table cuts, but for roots. -/
theorem items_of_round (work : Nat) (R : Round) :
    (({ entry := R.entry work } : Fmt.DeclaredRound).items.filter (· != .root))
      = List.replicate R.sent Fmt.Item.e := by
  show ((R.entry work).cut.filter (· != .root)) = _
  unfold Fmt.Entry.cut Round.entry
  simp

/-- **One challenge.** vals: any: drawsMarkedNonzeroHaveNonzeroWords does not read them. -/
theorem last_not_zero (work : Nat) (R : Round) (hk : knownNoSeeds R = true) (vals : List Fmt.ItemValue)
    (D : Fmt.Drawn) (he : D.elems.length = R.drawn)
    (hn : drawsMarkedNonzeroHaveNonzeroWords ({ entry := R.entry work } : Fmt.DeclaredRound) ⟨vals, D⟩ = true) :
    ∀ x ∈ (D.elems.map E.ofTriple).drop (R.drawn - (if R.notZero then 1 else 0)),
      OnBytes.isZeroE x = false := by
  obtain ⟨k, hk', hks⟩ := kind_of_known R hk
  have hall : ∀ x ∈ (List.replicate (R.drawn - (if R.notZero then 1 else 0)) Fmt.Draw.elem ++
      List.replicate (if R.notZero then 1 else 0) Fmt.Draw.elemNZ).zip D.elems,
      (x.1 != .elemNZ || x.2 != (0, 0, 0)) = true := by
    have h1 : ((Fmt.kindOf R.name).any fun k =>
        ((Fmt.dsElems (R.entry work) k).zip D.elems).all fun x =>
          x.1 != .elemNZ || x.2 != (0, 0, 0)) = true := hn
    rw [hk'] at h1
    simp only [Option.any_some, List.all_eq_true] at h1
    unfold Fmt.dsElems at h1
    rw [if_neg hks] at h1
    exact h1
  intro y hy
  rw [← List.map_drop] at hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  apply isZeroE_false_of
  show t ≠ (0, 0, 0)
  have hle : ∀ n b : Nat, n - (n - b) ≤ b := fun n b => by omega
  have hmem : (Fmt.Draw.elemNZ, t) ∈
      (List.replicate (R.drawn - (if R.notZero then 1 else 0)) Fmt.Draw.elem ++
        List.replicate (if R.notZero then 1 else 0) Fmt.Draw.elemNZ).zip
        (D.elems.take (R.drawn - (if R.notZero then 1 else 0)) ++
          D.elems.drop (R.drawn - (if R.notZero then 1 else 0))) := by
    rw [List.zip_append (by
      rw [List.length_replicate, List.length_take, he, Nat.min_eq_left (Nat.sub_le _ _)])]
    exact List.mem_append_right _ (mem_zip_replicate _ _ _ (by
      rw [List.length_drop, he]
      exact hle _ _) t ht)
  rw [List.take_append_drop] at hmem
  have h3 := hall _ hmem
  have h4 : (Fmt.Draw.elemNZ != Fmt.Draw.elemNZ) = false := rfl
  have h5 : (t != ((0, 0, 0) : Fmt.Ext)) = true := by
    have h6 : ((Fmt.Draw.elemNZ != Fmt.Draw.elemNZ) || t != ((0, 0, 0) : Fmt.Ext)) = true := h3
    rw [h4, Bool.false_or] at h6
    exact h6
  intro e
  rw [e] at h5
  simp at h5

/-- **One round, from its parts.** -/
theorem shaped_of_parts (work : Nat) (R : Round) (hk : knownNoSeeds R = true) (s : List E)
    (D : Fmt.Drawn) (hs : s.length = R.sent) (he : D.elems.length = R.drawn) (hp : D.poss = [])
    (ht : D.trits = [])
    (hn : drawsMarkedNonzeroHaveNonzeroWords ({ entry := R.entry work } : Fmt.DeclaredRound) ⟨[], D⟩ = true) :
    ∃ s' d, noDigest ⟨s.map fun x => Fmt.ItemValue.e x.triple, D⟩ = rvOf s' d ∧ s'.length = R.sent ∧
      d.length = R.drawn ∧
      ∀ x ∈ d.drop (R.drawn - (if R.notZero then 1 else 0)), OnBytes.isZeroE x = false := by
  have hmap : (D.elems.map E.ofTriple).map (·.triple) = D.elems := by
    rw [List.map_map]
    have e : ((fun x : E => x.triple) ∘ E.ofTriple) = id := funext fun _ => rfl
    rw [e, List.map_id]
  refine ⟨s, D.elems.map E.ofTriple, ?_, hs, by rw [List.length_map, he],
    last_not_zero work R hk [] D he hn⟩
  obtain ⟨elems, poss, trits, digest⟩ := D
  have hp' : poss = [] := hp
  have ht' : trits = [] := ht
  subst hp' ht'
  show (⟨s.map fun x => Fmt.ItemValue.e x.triple, ⟨elems, [], [], none⟩⟩ : Fmt.RoundView) =
    ⟨s.map fun x => Fmt.ItemValue.e x.triple, ⟨(elems.map E.ofTriple).map (·.triple), [], [], none⟩⟩
  rw [hmap]

/-- **One round, from the clauses of roundsFit.** -/
theorem shaped_of_roundFit (work : Nat) (R : Round) (hk : knownNoSeeds R = true) (r : Fmt.RoundView)
    (hv : r.vals.map itemOf = List.replicate R.sent Fmt.Item.e)
    (he : r.drawn.elems.length = R.drawn) (hp : r.drawn.poss.length = 0)
    (ht : r.drawn.trits.length = 0)
    (hn : drawsMarkedNonzeroHaveNonzeroWords ({ entry := R.entry work } : Fmt.DeclaredRound) r = true) :
    ∃ s d, noDigest r = rvOf s d ∧ s.length = R.sent ∧ d.length = R.drawn ∧
      ∀ x ∈ d.drop (R.drawn - (if R.notZero then 1 else 0)), OnBytes.isZeroE x = false := by
  obtain ⟨s, hs, hvals⟩ := vals_elems r.vals R.sent hv
  obtain ⟨vals, D⟩ := r
  have hvals' : vals = s.map fun x => Fmt.ItemValue.e x.triple := hvals
  subst hvals'
  exact shaped_of_parts work R hk s D hs he (List.length_eq_zero_iff.mp hp)
    (List.length_eq_zero_iff.mp ht) hn

/-- **THE ROUNDS.** -/
theorem shapedNZ_of_fit (work : Nat) : ∀ (rs : List Fmt.RoundView) (Rs : List Round),
    (∀ R ∈ Rs, knownNoSeeds R = true) →
    roundsFit (Rs.map fun R => ({ entry := R.entry work } : Fmt.DeclaredRound)) rs = true →
    ShapedNZ (rs.map noDigest) Rs
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp [roundsFit] at h
  | _ :: _, [], _, h => by simp [roundsFit] at h
  | r :: rs, R :: Rs, hk, h => by
    rw [List.map_cons] at h
    unfold roundsFit at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, h7⟩, h8⟩ := h
    rw [List.map_cons]
    exact .cons
      (shaped_of_roundFit work R (hk R List.mem_cons_self) r (h1.trans (items_of_round work R)) h2
        h3 h4 h7)
      (shapedNZ_of_fit work rs Rs (fun R' h' => hk R' (List.mem_cons_of_mem _ h')) h8)

/-- **At the seated block's own declared rounds.** -/
theorem shapedNZ_of_blockFit (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (rs : List Fmt.RoundView)
    (hf : roundsFit (blockAt h iU3 work l).rounds rs = true) :
    ShapedNZ (rs.map noDigest) (@rounds (parOf h work).sizes) := by
  rw [blockAt_rounds] at hf
  exact shapedNZ_of_fit _ rs _ (@rounds_noSeeds (parOf h work).sizes) hf

/-- Where no round bears a sealed digest, striking it turns nothing. -/
theorem noDigest_of_none : ∀ rs : List Fmt.RoundView, (∀ r ∈ rs, r.drawn.digest = none) →
    rs.map noDigest = rs
  | [], _ => rfl
  | r :: rs, h => by
    have e : noDigest r = r := by
      have hd : r.drawn.digest = none := h r List.mem_cons_self
      obtain ⟨vals, ⟨elems, poss, trits, digest⟩⟩ := r
      have hd' : digest = none := hd
      subst hd'
      rfl
    rw [List.map_cons, e, noDigest_of_none rs fun r' h' => h r' (List.mem_cons_of_mem _ h')]

/-- **Block.step SAYS YES AT ROUNDS THAT PASS ITS TEST**, where the hearing takes them with the
digests struck. The letters of hear are g's, through the class Given. NO WORD ON WHAT THE ROUNDS
HOLD. -/
theorem step_of_fit (h : OnBytes.Model.Head.Shape) (iU3 work l firstTree : Nat) (cols : List OpenedColumn)
    (s : S) (rs : List Fmt.RoundView) (H : HeardAll) (G : OnBytes.Model.Fork)
    (hf : roundsFit (blockAt h iU3 work l).rounds rs = true)
    (hWL : WellLaid ((seatAt h iU3).ledger s)) (hfail : s.failed = none) (hopen : HeadOpen s)
    (R : ∃ g : Given, given (parOf h work) (seatAt h iU3) s = .ok g ∧
      Canonical (rs.map noDigest) ∧
      hear ((seatAt h iU3).ledger s) (rs.map noDigest) = some (H, G, [])) :
    ∃ s' : S, (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) ∧
      (blockAt h iU3 work l).decide s (rs.map noDigest) [] = .ok s' ∧
      (seatAt h iU3).ledger s' = G ∧ (seatAt h iU3).heard s' = some H ∧
      given (parOf h work) (seatAt h iU3) s' = given (parOf h work) (seatAt h iU3) s ∧
      (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
  have hsh := shapedNZ_of_blockFit h iU3 work l rs hf
  have R' : HeardK6 h iU3 work s (rs.map noDigest) H G := by
    obtain ⟨g, hg, hcan, hh⟩ := R
    obtain ⟨z, y, _, _, _, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
    exact ⟨_, hg, hcan, hsh, hh⟩
  obtain ⟨s', hd, a, b, c, e⟩ :=
    yes_of_heard h iU3 work l s (rs.map noDigest) H G hWL hfail hopen R'
  have hg0 : groupsOf firstTree (blockAt h iU3 work l).rounds (rs.map (·.drawn)) = [] := by
    rw [blockAt_rounds]
    exact groups_none firstTree _ _ _
  have hw : wantOf firstTree (blockAt h iU3 work l) rs = [] := by
    unfold wantOf
    rw [hg0]
    rfl
  -- hd stands at the empty list of opened leaves; decide_step asks it at the step's own list. The
  -- decision does not read that argument (Law/K06HonestStep.lean: decide_any_groups, by rfl).
  have key := Came.decide_step firstTree (blockAt h iU3 work l) s rs cols s' hf
    (by rw [hw]; rfl) (by exact hd)
  rw [hw] at key
  exact ⟨s', key, hd, a, b, c, e⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.isZeroE_false_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.vals_elems
#print axioms VerifiableInference.Desc.Kinds.Head.Law.mem_zip_replicate
#print axioms VerifiableInference.Desc.Kinds.Head.Law.kind_of_known
#print axioms VerifiableInference.Desc.Kinds.Head.Law.items_of_round
#print axioms VerifiableInference.Desc.Kinds.Head.Law.last_not_zero
#print axioms VerifiableInference.Desc.Kinds.Head.Law.shaped_of_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.shaped_of_roundFit
#print axioms VerifiableInference.Desc.Kinds.Head.Law.shapedNZ_of_fit
#print axioms VerifiableInference.Desc.Kinds.Head.Law.shapedNZ_of_blockFit
#print axioms VerifiableInference.Desc.Kinds.Head.Law.noDigest_of_none
#print axioms VerifiableInference.Desc.Kinds.Head.Law.step_of_fit
