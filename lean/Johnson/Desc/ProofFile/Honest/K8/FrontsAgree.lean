-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontsAgree.lean: THE VERIFIER's STATE IN FRONT OF A MEMBER OF THE
FIRST CHAIN, ALONG AN HONEST RUN (`frontsOf`, Johnson/Desc/ProofFile/Honest/Fall.lean, at `runC`'s
first view, Honest/Walk.lean), DOES NOT HANG ON THAT MEMBER's OWN CHALLENGES OR ON LATER ONES,
WHEREVER THE RUN RETURNS. Definitions, statements and proofs. General in the description, the book
and the prover: no kind and no plan is named. LEMMAS; NONE OF THE LIBRARY's GOALS.

  `rnds`, `rnds_take_succ`, `rnds_take_mono`   the number of rounds of a list of members
  **`frontsOf_fold`**   entry n of `frontsOf` holds the end of the verifier's own fold
      (`foldBlocks`) over the n members in front
  `frontsOf_local`   so it reads the rounds of these members and the columns that they are owed, and
      nothing behind them
  **`walk_front`**   one chain: behind the rounds in front of member K, which has a round, the walk
      stands at one place; all that is laid later is laid behind what lies there; and it has as many
      columns as the K members in front are owed
  **`fronts_agree`**   a file's first chain: two runs that return, at one input and at the same
      coins, at challenges that are alike in front of the first round of member K, which has a
      round: the two states in front of member K are one
  `frontAt`   that state, with the instance's public part, as a function of the challenges; nothing
      where the run refuses or no entry K is listed
  **`frontAt_agree`**, **`frontAt_reach`**   it meets `Agree`
      (Johnson/Desc/K8/Honest/FreeOfAgree.lean) at every round whose challenge is shown at or behind
      member K's first round; each of its values is a state that the chain's own blocks reach at
      number K
By: runC_parts, walk_append_ok (Honest/Law/Rule/WalkLaw.lean) · walk_len (Law/RunAtFile.lean) ·
start_tied, walk_tied (Law/WalkFold.lean) · walk_grows (Law/AcceptC.lean) · foldBlocks_eq,
foldBlocks_more (Law/Causal.lean) · seal_back, ready_ok, steps_decl (Honest/Law/Run.lean) ·
`frontsOf_reach₀` (Honest/K8/FrontsReach.lean).
Limits. The first chain alone. Nothing on whether a run returns. Nothing on which member bears which
place.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontsReach
import Johnson.Desc.ProofFile.Honest.Law.AcceptC
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile
import Johnson.Desc.ProofFile.Honest.Law.WalkFold
import Johnson.Desc.K8.Honest.FreeOfAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc
open VerifiableInference.Desc.First.K8.Honest (Agree)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {S Cl Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## The number of rounds -/

/-- The number of rounds of a list of members. -/
def rnds (l : List (Block S Cl)) : Nat := (l.flatMap (·.rounds)).length

theorem rnds_append (a b : List (Block S Cl)) : rnds (a ++ b) = rnds a + rnds b := by
  unfold rnds
  rw [List.flatMap_append, List.length_append]

theorem rnds_take_succ {bs : List (Block S Cl)} {i : Nat} {b : Block S Cl}
    (h : bs[i]? = some b) : rnds (bs.take (i + 1)) = rnds (bs.take i) + b.rounds.length := by
  rw [List.take_add_one, h, rnds_append]
  simp [rnds]

theorem rnds_take_mono (bs : List (Block S Cl)) {i j : Nat} (h : i ≤ j) :
    rnds (bs.take i) ≤ rnds (bs.take j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, rnds_append]
  exact Nat.le_add_right _ _

theorem rnds_take_le (bs : List (Block S Cl)) (i : Nat) : rnds (bs.take i) ≤ rnds bs := by
  conv_rhs => rw [← List.take_append_drop i bs, rnds_append]
  exact Nat.le_add_right _ _

/-! ## `frontsOf` and the fold -/

/-- **Entry n holds the fold's end over the n members in front.** -/
theorem frontsOf_fold (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (e : Place × S × List Fmt.Drawn),
    (frontsOf ft bs s rs cols)[n]? = some e →
    ∃ r c, foldBlocks ft (bs.take n) s rs cols = .ok (e.2.1, r, c)
  | [], _, _, _, _, _, he => by
    simp [frontsOf] at he
  | b :: l, s, rs, cols, n, e, he => by
    unfold frontsOf at he
    simp only at he
    split at he
    · simp at he
    · rename_i hg
      have hlen : (rs.take b.rounds.length).length = b.rounds.length := by simpa using hg
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        exact ⟨rs, cols, by rw [List.take_zero]; rfl⟩
      | succ n =>
        rw [List.getElem?_cons_succ] at he
        cases hst : b.step ft s (rs.take b.rounds.length) cols with
        | error e' =>
          rw [hst] at he
          simp at he
        | ok y =>
          obtain ⟨s', m⟩ := y
          rw [hst] at he
          obtain ⟨r, c, ih⟩ := frontsOf_fold ft l s' _ _ n e he
          refine ⟨r, c, ?_⟩
          rw [List.take_succ_cons, foldBlocks_eq, if_neg (not_not.2 hlen), hst]
          exact ih

/-- It reads nothing behind these members' rounds and owed columns. -/
theorem frontsOf_local (ft : Nat) (bs : List (Block S Cl)) (s : S) (r₁ r₂ r₂' : List Fmt.RoundView)
    (c₁ c₂ c₂' : List OpenedColumn) (n : Nat) (e e' : Place × S × List Fmt.Drawn)
    (hr : r₁.length = rnds (bs.take n)) (hc : c₁.length = owed ft (bs.take n) r₁)
    (he : (frontsOf ft bs s (r₁ ++ r₂) (c₁ ++ c₂))[n]? = some e)
    (he' : (frontsOf ft bs s (r₁ ++ r₂') (c₁ ++ c₂'))[n]? = some e') : e.2.1 = e'.2.1 := by
  obtain ⟨r, c, h1⟩ := frontsOf_fold ft bs s _ _ n e he
  obtain ⟨r', c', h2⟩ := frontsOf_fold ft bs s _ _ n e' he'
  rw [foldBlocks_more ft _ s r₁ r₂ c₁ c₂ hr hc] at h1
  rw [foldBlocks_more ft _ s r₁ r₂' c₁ c₂' hr hc] at h2
  cases hf : foldBlocks ft (bs.take n) s r₁ c₁ with
  | error x =>
    rw [hf] at h1
    cases h1
  | ok y =>
    rw [hf] at h1 h2
    have a1 : y.1 = e.2.1 := congrArg Prod.fst (Except.ok.inj h1)
    have a2 : y.1 = e'.2.1 := congrArg Prod.fst (Except.ok.inj h2)
    exact a1.symm.trans a2

/-! ## One chain -/

/-- **Where the walk stands behind the rounds in front of member K.** -/
theorem walk_front (L : Lay) (bs : List (Block S Cl)) (m₀ : Option (Mid W Y)) (v₀ : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {K : Nat} {b : Block S Cl}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m₀ v₀ front = .ok a) (hz : walk L ss ds a = .ok z)
    (hl : ss.length = rnds bs) (hb : bs[K]? = some b) (hpos : 0 < b.rounds.length) :
    ∃ zm, walk L (ss.take (rnds (bs.take K))) (ds.take (rnds (bs.take K))) a = .ok zm ∧
      (∃ ps cs, z.laid = zm.laid ++ ps ∧ z.cols = zm.cols ++ cs) ∧
      zm.laid.length = rnds (bs.take K) ∧
      zm.cols.length = owed L.firstTree (bs.take K) (roundsOf zm.laid) := by
  obtain ⟨m, hm⟩ : ∃ m, m = rnds (bs.take K) := ⟨_, rfl⟩
  rw [← hm]
  have hlen := walk_len L ss ds a z hz
  have hle : m ≤ ss.length := by
    rw [hl, hm]
    exact rnds_take_le bs K
  have hz' : walk L (ss.take m ++ ss.drop m) (ds.take m ++ ds.drop m) a = .ok z := by
    rw [List.take_append_drop, List.take_append_drop]
    exact hz
  obtain ⟨zm, h1, h2⟩ := walk_append_ok (ss.drop m) (ds.drop m) (ss.take m) (ds.take m) a z
    (by rw [List.length_take, List.length_take, hlen]) hz'
  obtain ⟨ps, cs, e1, e2⟩ := walk_grows L _ _ zm z h2
  obtain ⟨t1, t2, t3⟩ := start_tied L bs m₀ v₀ ha
  obtain ⟨⟨done, fore, g1, g2, g3, g4, -⟩, gO, gL⟩ := walk_tied L bs _ _ _ a zm t1 t2 h1
  have hlaid : zm.laid.length = m := by
    rw [gL, t3, List.length_take, List.length_nil, Nat.zero_add]
    exact Nat.min_eq_left hle
  have hdone : done = bs.take done.length := by
    rw [g1, List.take_left']
    rfl
  have hsum : rnds (bs.take done.length) + zm.own.length = m := by
    rw [← hdone]
    have e0 := congrArg List.length g2
    rw [List.length_append, g3, hlaid] at e0
    exact e0.symm
  have hK : K < bs.length := (List.getElem?_eq_some_iff.1 hb).1
  have hD : done.length = K := by
    rcases Nat.lt_trichotomy done.length K with hlt | heq | hgt
    · exfalso
      cases htd : zm.todo with
      | nil =>
        rw [htd, List.append_nil] at g1
        rw [g1] at hK
        omega
      | cons b' t =>
        have hb' : bs[done.length]? = some b' := by
          rw [g1, htd]
          simp
        have o1 := gO b' t htd
        have s1 := rnds_take_succ hb'
        have s2 := rnds_take_mono bs (show done.length + 1 ≤ K from hlt)
        omega
    · exact heq
    · exfalso
      have s1 := rnds_take_succ hb
      have s2 := rnds_take_mono bs (show K + 1 ≤ done.length from hgt)
      omega
  have hown : zm.own = [] := List.length_eq_zero_iff.1 (by
    rw [hD] at hsum
    omega)
  have hd2 : done = bs.take K := by
    rw [← hD]
    exact hdone
  refine ⟨zm, h1, ⟨ps, cs, e1, e2⟩, hlaid, ?_⟩
  rw [g4, g2, hown, List.append_nil, hd2]

/-! ## A file's first chain -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B}

/-- **The two states in front of member K are one.** -/
theorem fronts_agree {ρ ρ' : Draws} {r r' : RunC F} (h : runC F B H w₀ rc x c ρ = .ok r)
    (h' : runC F B H w₀ rc x c ρ' = .ok r') {K : Nat} {b : Block F.S₁ F.Cl}
    (hb : F.first.blocksInOrder[K]? = some b) (hpos : 0 < b.rounds.length)
    (hpre : ρ.first.take (rnds (F.first.blocksInOrder.take K)) =
      ρ'.first.take (rnds (F.first.blocksInOrder.take K)))
    {e e' : Place × F.S₁ × List Fmt.Drawn}
    (he : (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      (withEmptySealRound r.run.views.1).opened)[K]? = some e)
    (he' : (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r'.run.views.1).rounds
      (withEmptySealRound r'.run.views.1).opened)[K]? = some e') : e.2.1 = e'.2.1 := by
  obtain ⟨R, a₁, z₁, _, _, _, _, hR, ha₁, hz₁, hq, -, -, -, -, rfl⟩ := runC_parts h
  obtain ⟨R', a₁', z₁', _, _, _, _, hR', ha₁', hz₁', hq', -, -, -, -, rfl⟩ := runC_parts h'
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain rfl : a₁ = a₁' := Except.ok.inj (ha₁.symm.trans ha₁')
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  have hl : R.first.length = rnds F.first.blocksInOrder := by
    have e0 := congrArg List.length (steps_decl s1)
    rwa [List.length_map] at e0
  obtain ⟨zm, w1, ⟨ps, cs, e1, e2⟩, l1, c1⟩ := walk_front _ _ _ _ ha₁ hz₁ hl hb hpos
  obtain ⟨zm', w1', ⟨ps', cs', e1', e2'⟩, -, -⟩ := walk_front _ _ _ _ ha₁ hz₁' hl hb hpos
  rw [hpre] at w1
  obtain rfl : zm = zm' := Except.ok.inj (w1.symm.trans w1')
  have he2 : (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (roundsOf zm.laid ++ roundsOf ps)
      (zm.cols ++ cs))[K]? = some e := by
    rw [← roundsOf_append, ← e1, ← e2, ← seal_back hq]
    exact he
  have he2' : (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (roundsOf zm.laid ++ roundsOf ps')
      (zm.cols ++ cs'))[K]? = some e' := by
    rw [← roundsOf_append, ← e1', ← e2', ← seal_back hq']
    exact he'
  exact frontsOf_local 0 _ _ _ _ _ _ _ _ K e e' (by rw [roundsOf_length, l1]) c1 he2 he2'

/-- **The verifier's state in front of member K of the first chain, along an honest run**, with the
instance's public part: as a function of the challenges. -/
def frontAt (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (K : Nat) (ρ : Draws) : Option (F.XiPub × F.S₁) :=
  (runC F B H w₀ rc x c ρ).toOption.bind fun r =>
    ((frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      (withEmptySealRound r.run.views.1).opened)[K]?).map fun e => (F.pub x, e.2.1)

theorem frontAt_some {K : Nat} {ρ : Draws} {zs : F.XiPub × F.S₁}
    (h : frontAt F B H w₀ rc x c K ρ = some zs) :
    ∃ r e, runC F B H w₀ rc x c ρ = .ok r ∧
      (frontsOf 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
        (withEmptySealRound r.run.views.1).opened)[K]? = some e ∧ zs = (F.pub x, e.2.1) := by
  unfold frontAt at h
  cases hr : runC F B H w₀ rc x c ρ with
  | error e =>
    rw [hr] at h
    cases h
  | ok r =>
    rw [hr] at h
    obtain ⟨e, he, hz⟩ := Option.map_eq_some_iff.1 h
    exact ⟨r, e, rfl, he, hz.symm⟩

/-- **It meets `Agree`.** The letter shows: from a list, one value a round, to the challenges. -/
theorem frontAt_agree {ι : Type} [DecidableEq ι] {A : ι → Type} (j : ι)
    (shows : (∀ i, A i) → Draws) {K : Nat} {b : Block F.S₁ F.Cl}
    (hb : F.first.blocksInOrder[K]? = some b) (hpos : 0 < b.rounds.length)
    (hj : ∀ f a, (shows (Function.update f j a)).first.take (rnds (F.first.blocksInOrder.take K)) =
      (shows f).first.take (rnds (F.first.blocksInOrder.take K))) :
    Agree j fun f => frontAt F B H w₀ rc x c K (shows f) := by
  intro f a a' s s' hs hs'
  obtain ⟨r, e, hr, he, rfl⟩ := frontAt_some hs
  obtain ⟨r', e', hr', he', rfl⟩ := frontAt_some hs'
  rw [fronts_agree hr hr' hb hpos ((hj f a).trans (hj f a').symm) he he']

/-- **Each of its values is reached.** -/
theorem frontAt_reach {K : Nat} {ρ : Draws} {zs : F.XiPub × F.S₁}
    (h : frontAt F B H w₀ rc x c K ρ = some zs) : Reach 0 F.first.blocksInOrder F.start₁ K zs := by
  obtain ⟨r, e, -, he, rfl⟩ := frontAt_some h
  exact (frontsOf_reach₀ 0 F.first.blocksInOrder F.start₁ (F.pub x) _ _ K e he).1

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontsOf_fold
#print axioms ProofFile.Honest.K8.frontsOf_local
#print axioms ProofFile.Honest.K8.walk_front
#print axioms ProofFile.Honest.K8.fronts_agree
#print axioms ProofFile.Honest.K8.frontAt_agree
#print axioms ProofFile.Honest.K8.frontAt_reach
#print axioms ProofFile.Honest.K8.rnds
#print axioms ProofFile.Honest.K8.rnds_append
#print axioms ProofFile.Honest.K8.rnds_take_succ
#print axioms ProofFile.Honest.K8.rnds_take_mono
#print axioms ProofFile.Honest.K8.rnds_take_le
#print axioms ProofFile.Honest.K8.frontAt
#print axioms ProofFile.Honest.K8.frontAt_some
