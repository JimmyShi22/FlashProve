-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

-- Mends of typing and elaboration, pack c60df67f; no statement turned by them but mem_weave's.
/-
E2E/OfflineReady.lean: in scope, at the written book, the frame's `ready` returns at the offline
prover, at every coin, at every index in range and every instance. That is `chainSteps` at the three
chains, the tests of `readyTests`, and the trace that the key file's prover always has.

  `chainSteps_returns`   the frame's `chainSteps` returns where each half found is laid
  `rounds_full`, `half_rounds`   at the written book a cut adds up to the place's rounds (the kernel)
  `strays_nil`, `twice_eq`   the first two tests of `readyTests`
  `offline_chains_laid`   `chainSteps` returns at the three chains, at every coin
  `offline_ready`   THE STATEMENT

Conditional on `LookupsStated` (E2E/OfflineLaying.lean): the two lookups' parts state what the book has
for them; if that premise is false at the written book the statements over it are empty.
Conditional on `KeySourced`, scope, and two tests of the index: that the index is in range, and that
the prover's named member is. Where `ready` refuses at an index out of range it says so: that is the
statement's premise, no gap. It says that the rounds are prepared: no round has been played, and
nothing here says that a move returns. keyProver is E2E/KeyProver.lean's text with the owned lookups.
Nothing on any simulator or any property.
-/
import E2E.OfflineRowsAtValue
import E2E.KeyStartsBare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_second first_places)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull fullFirst fullShared fullSecond
  places_named book_passes foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.AtFiles (KeySourced KeyNamed keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

section General
variable {S Cl V W Y : Type}

/-- **`chainSteps` returns** where every sub-protocol has a list of oracle messages for each round,
and where a half is found it is laid. -/
theorem chainSteps_returns (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W Y)) : ∀ bs : List (Block S Cl),
    (∀ b ∈ bs, b.oracles.length = b.rounds.length) →
    (∀ b ∈ bs, ∀ g, (hs.find? fun h => h.place == b.place) = some g →
      g.rounds = b.rounds.length ∧
      B.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
      rows.any (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false ∧
      B.ahead.any (fun e =>
        e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = false ∧
      ∃ c, lendRow B rows look b.place g.parts 0 = .ok c) →
    ∃ l, chainSteps B rows look v bs hs = .ok l
  | [], _, _ => ⟨[], rfl⟩
  | b :: bs, ho, hg => by
    obtain ⟨l, hl⟩ := chainSteps_returns B rows look v hs bs
      (fun x hx => ho x (List.mem_cons_of_mem _ hx))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    have h0 : ¬ (b.oracles.length != b.rounds.length) = true := by
      simp [ho b List.mem_cons_self]
    unfold chainSteps
    rw [if_neg h0]
    cases hf : hs.find? fun g => g.place == b.place with
    | none =>
      show ∃ l', ((chainSteps B rows look v bs hs).map _) = .ok l'
      rw [hl]
      exact ⟨_, rfl⟩
    | some g =>
      obtain ⟨a1, a2, a3, a4, c, hc⟩ := hg b List.mem_cons_self g hf
      simp only
      have h1 : ¬ (g.rounds != b.rounds.length) = true := by simp [a1]
      have h2 : ¬ (B.cuts.lookup b.place != some (g.parts.map (·.moves.length))) = true := by
        simp [a2]
      have h3 : ¬ (rows.any fun r =>
          r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = true := by
        rw [a3]
        simp
      have h4 : ¬ (B.ahead.any fun e =>
          e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = true := by
        rw [a4]
        simp
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, hc]
      show ∃ l', ((chainSteps B rows look v bs hs).map fun l => g.steps b v c ++ l) = .ok l'
      rw [hl]
      exact ⟨_, rfl⟩

/-- No half stands outside its chain's places. -/
theorem strays_nil {bs : List (Block S Cl)} {hs : List (Placed V W Y)}
    (h : ∀ g ∈ hs, g.place ∈ bs.map (·.place)) : strays bs hs = [] := by
  unfold strays
  have e : (hs.filter fun h => !(bs.any fun b => b.place == h.place)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    obtain ⟨b, hb, e⟩ := List.mem_map.1 (h g hg)
    have hany : (bs.any fun b => b.place == g.place) = true :=
      List.any_eq_true.2 ⟨b, hb, beq_iff_eq.2 e⟩
    simp [hany]
  rw [e]
  rfl

/-- What `twice` reads of a list of halves is their places. -/
def twiceIn (l : List Place) : List Place :=
  (l.filter fun a => decide (1 < (l.filter fun b => b == a).length)).eraseDups

theorem twice_eq (hs : List (Placed V W Y)) : twice hs = twiceIn (hs.map (·.place)) := by
  unfold twice twiceIn
  congr 1
  apply List.filter_congr
  intro a _
  have e : (hs.filter fun h => h.place == a).length =
      ((hs.map (·.place)).filter fun b => b == a).length := by
    rw [List.filter_map, List.length_map]
    rfl
  rw [e]

end General

/-- **A cut adds up to its place's rounds**, at the written book. By evaluation. -/
theorem rounds_full : atFull (fun K =>
    (fullFirst ++ fullShared ++ fullSecond).all fun r =>
      match (keyBook K).cuts.lookup r.1 with
      | some c => c.foldl (· + ·) 0 == r.2
      | none => true) = true := by decide +kernel

section Laid
variable {S Cl V W Y : Type} {K₀ : KeyPub}

/-- A laid half has its place's rounds. -/
theorem half_rounds (hK : fullPub = some K₀) {ch : Nat} {g : Placed V W Y}
    (hl : RowLaid (keyBook K₀) ch g) {n : Nat}
    (hr : (g.place, n) ∈ fullFirst ++ fullShared ++ fullSecond) : g.rounds = n := by
  have h := List.all_eq_true.1 (of_atFull rounds_full hK) _ hr
  have h' : (match (keyBook K₀).cuts.lookup g.place with
    | some c => c.foldl (· + ·) 0 == n
    | none => true) = true := h
  rw [hl.cut] at h'
  have e : ((g.parts.map (·.moves.length)).foldl (· + ·) 0) = n := beq_iff_eq.1 h'
  unfold Placed.rounds
  rw [← e, List.foldl_map]

/-- **A chain whose halves are laid has its steps**, at the written book. -/
theorem chain_of_rows (hK : fullPub = some K₀) {ch : Nat} (bs : List (Block S Cl))
    (hs : List (Placed V W Y)) (v : Option V) (k : Coins (keyBook K₀))
    (hlaid : ∀ h ∈ hs, RowLaid (keyBook K₀) ch h)
    (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hrows : ∀ b ∈ bs, (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond) :
    ∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf ch) (k.look ch) v bs hs = .ok l := by
  refine chainSteps_returns _ _ _ _ _ _ ho ?_
  intro b hb g hf
  have hg := List.mem_of_find?_eq_some hf
  have hq : (g.place == b.place) = true :=
    List.find?_some (p := fun h : Placed V W Y => h.place == b.place) hf
  have hp : g.place = b.place := beq_iff_eq.1 hq
  have L := hlaid g hg
  have hr := hrows b hb
  rw [← hp] at hr
  rw [← hp]
  exact ⟨half_rounds hK L hr, L.cut, L.noRow, L.noEntry, L.lends k⟩

end Laid

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **At every coin `chainSteps` returns at the three chains.** -/
theorem offline_chains_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hL : LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first)) (k : Coins (keyBook K₀))
    (v : Option (Local W₀ Rc KeyInst Unit)) (v' : Option Empty) :
    (∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0) v
        (keyFileDescription Xs N Pl).first.blocksInOrder
        (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).first = .ok l) ∧
      (∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) v'
        (keyFileDescription Xs N Pl).shared.blocksInOrder
        (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).shared = .ok l) ∧
      ∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) v
        (keyFileDescription Xs N Pl).second.blocksInOrder
        (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).second = .ok l := by
  obtain ⟨r1, r2, r3⟩ := places_named scope hs.named
  obtain ⟨p1, p2, p3⟩ := planOk_all hs.named.plan
  have mem₁ : ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_left _ (List.mem_append_left _ (r1 ▸ List.mem_map.2 ⟨b, hb, rfl⟩))
  have mem₂ : ∀ b ∈ (keyFileDescription Xs N Pl).shared.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_left _ (List.mem_append_right _ (r2 ▸ List.mem_map.2 ⟨b, hb, rfl⟩))
  have mem₃ : ∀ b ∈ (keyFileDescription Xs N Pl).second.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_right _ (r3 ▸ List.mem_map.2 ⟨b, hb, rfl⟩)
  exact ⟨chain_of_rows hK _ _ v k (offline_first_laid K' Xs N Pl f g inR d ent groups first hs scope hK hL)
      (fun b hb => (Small.lists_of_shaped (p1 b hb).2).1.symm) mem₁,
    chain_of_rows hK _ _ v' k (offline_shared_laid K' Xs N Pl f g inR d ent groups first hs scope hK)
      (fun b hb => (Small.lists_of_shaped (p2 b hb).2).1.symm) mem₂,
    chain_of_rows hK _ _ v k (offline_second_laid K' Xs N Pl f g inR d ent groups first hs scope hK)
      (fun b hb => (Small.lists_of_shaped (p3 b hb).2).1.symm) mem₃⟩

/-- The halves stand at places of their chains, at no place twice. -/
theorem offline_tests {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (w₀ : W₀) (hin : inR w₀ = true) (hd : inR d = true)
    (hA : (offlineValue K' Xs N Pl f g inR d ent groups first).AtAll) :
    readyTests (keyFileDescription Xs N Pl) (keyBook K₀)
      (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)) w₀ = .ok () := by
  obtain ⟨r1, r2, r3⟩ := places_named scope hs.named
  let V := offlineValue K' Xs N Pl f g inR d ent groups first
  have s1 : strays (keyFileDescription Xs N Pl).first.blocksInOrder (keyProver V).first = [] := by
    refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver V).first.map (·.place) := List.mem_map_of_mem hq
    rw [first_places V hA.first] at hm
    rw [places_of_rows r1]
    have incl : ∀ p ∈ ([⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, some 0, 2, .K3⟩,
        ⟨1, some 1, 2, .K3⟩, ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩, ⟨1, none, 14, .K1⟩] :
        List Place), p ∈ fullFirst.map (·.1) := by decide
    exact incl _ hm
  have s2 : strays (keyFileDescription Xs N Pl).shared.blocksInOrder (keyProver V).shared = [] := by
    refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver V).shared.map (·.place) := List.mem_map_of_mem hq
    rw [AtPublicFiles.KeyFile.keyProver_shared V hA.splits, hA.onU, hA.onOmega] at hm
    rw [places_of_rows r2]
    have incl : ∀ p ∈ ([K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
        K14.place 8, foldedTestPlace, omegaTestPlace] : List Place),
        p ∈ fullShared.map (·.1) := by decide
    exact incl _ hm
  have s3 : strays (keyFileDescription Xs N Pl).second.blocksInOrder (keyProver V).second = [] := by
    refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver V).second.map (·.place) := List.mem_map_of_mem hq
    rw [keyProver_second, List.map_cons, List.map_nil, hA.own] at hm
    rw [places_of_rows r3]
    have incl : ∀ p ∈ ([ownTestPlace] : List Place), p ∈ fullSecond.map (·.1) := by decide
    exact incl _ hm
  have t1 : twice (keyProver V).first = [] := by
    rw [twice_eq, first_places V hA.first]
    decide
  have t2 : twice (keyProver V).shared = [] := by
    rw [twice_eq, AtPublicFiles.KeyFile.keyProver_shared V hA.splits, hA.onU, hA.onOmega]
    decide
  have t3 : twice (keyProver V).second = [] := by
    rw [twice_eq, keyProver_second, List.map_cons, List.map_nil, hA.own]
    decide
  unfold readyTests
  rw [s1, s2, s3, t1, t2, t3]
  have hp := AtPublicFiles.KeyThread.placesOk_of_plan hs.named.plan
  have hw := book_passes scope hs.named K₀ hK
  simp only [List.append_nil, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, hp]
  show (if (!inR d) = true then _ else if (!inR w₀) = true then _ else
    match (keyBook K₀).word (keyFileDescription Xs N Pl) with
    | some e => _
    | none => Except.ok ()) = _
  rw [hd, hin, hw]
  rfl

/-- **THE STATEMENT: at every coin, at every index in range and every instance, the rounds of the
offline prover are prepared.** hA: the sixteen places; it is `atAll_value` at public premises. -/
theorem offline_ready {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hL : LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first)) (w₀ : W₀) (rc : Rc) (x : KeyInst)
    (k : Coins (keyBook K₀)) (hin : inR w₀ = true) (hd : inR d = true)
    (hA : (offlineValue K' Xs N Pl f g inR d ent groups first).AtAll) :
    ∃ R, ready (keyFileDescription Xs N Pl) (keyBook K₀)
      (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)) w₀ rc x k = .ok R := by
  have hT := offline_tests K' Xs N Pl f g inR d ent groups first hs scope hK w₀ hin hd hA
  obtain ⟨⟨l₁, h₁⟩, ⟨l₂, h₂⟩, ⟨l₃, h₃⟩⟩ :=
    offline_chains_laid K' Xs N Pl f g inR d ent groups first hs scope hK hL k
      (Face.own.sees ⟨w₀, rc, x, ()⟩) (Face.shared.sees ⟨w₀, rc, x.key⟩)
  have hl : k.look 1 = sharedLook (keyBook K₀) k.shared := rfl
  rw [hl] at h₂
  unfold ready
  rw [hT]
  show ∃ R, ((unfit (chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
      (Face.own.sees ⟨w₀, rc, x, ()⟩) (keyFileDescription Xs N Pl).first.blocksInOrder _)).bind _) = .ok R
  rw [h₁]
  show ∃ R, ((sharedSteps (keyFileDescription Xs N Pl) (keyBook K₀) _ ⟨w₀, rc, x.key⟩ k.shared).bind _) = .ok R
  unfold sharedSteps
  rw [h₂]
  show ∃ R, ((unfit (chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2)
      (Face.own.sees ⟨w₀, rc, x, ()⟩) (keyFileDescription Xs N Pl).second.blocksInOrder _)).map _) = .ok R
  rw [h₃]
  exact ⟨_, rfl⟩

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.chainSteps_returns
#print axioms AtPublicFiles.OfflineRows.rounds_full
#print axioms AtPublicFiles.OfflineRows.chain_of_rows
#print axioms AtPublicFiles.OfflineRows.offline_chains_laid
#print axioms AtPublicFiles.OfflineRows.offline_tests
#print axioms AtPublicFiles.OfflineRows.offline_ready
