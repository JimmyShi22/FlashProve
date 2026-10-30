--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupLink.lean: A LOOKUP'S WHOLE LINK IN THE KEY FILE'S FIRST CHAIN IS PASSED: the fold over
the six sub-protocols of the link (laid · `caller` · the lookup · `layer` · behind the batching's
place · cleared: `Link.blocksInOrder`, Johnson/Desc/Block.lean) accepts, takes just the lookup's rounds and
no column, and leaves a state that is written out. General in the lookup, the setting and the
chain's public values. Statements and proofs; nothing is evaluated.

What is shown.
  `quiet_step`, `fold_quiet`: a sub-protocol without a round, as a step and in the fold.
  `groups_none`: rounds that open nothing are owed no column.
  **`link_fold`**: PREMISES, each by name: no ledger is open · i lookups lie behind · the index-mask
    message is not the lookups' own · `Room` in both messages' ledgers of mask entries · every part
    has a level · the planner makes the lookup's entries es · the view has so many rounds left, and
    they fit their entries (`roundsFit`) · `hearV` accepts them from the fresh ledger · the ten
    facts `Left` on what was heard. CONCLUSION: `foldBlocks` over the link's flat list accepts; the
    rounds left are those behind the lookup's; the columns are untouched; in the state the ledger,
    the hearing and the homes are cleared, the two messages' ledgers have handed out their entries
    (the two takings are named), and the lookup's rows and claims on keys are appended.
  `room_left`, `room_other`, **`room_behind`**: what both ledgers have left behind a link's two
    takings: so the premise `Room` of the next link follows from one count in front of the first.

Limits.
- All premises of E2E/KeyLookupAround.lean stay premises: `Room`, `Left`; and `hearV`'s accept and
  `roundsFit`, which are an honest side's to show.
- FORM ALONE: it says that the link is passed, not that what it writes holds of anything.
- One link. The two links in a row, and what stands in front and behind, are not chained here.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyLookupAround
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)

section General
variable {S Cl : Type}

/-- A sub-protocol without a round, as a step: it takes no column. -/
theorem quiet_step {b : Block S Cl} (hb : b.rounds = []) (ft : ℕ) {s s' : S} (cols : List OpenedColumn)
    (h : b.decide s [] [] = .ok s') : b.step ft s [] cols = .ok (s', 0) := by
  rw [Block.step_ok, hb]
  exact ⟨rfl, rfl, h, rfl⟩

/-- In the fold it takes no round. -/
theorem fold_quiet {b : Block S Cl} (hb : b.rounds = []) (ft : ℕ) {l : List (Block S Cl)}
    {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn}
    (h : b.decide s [] [] = .ok s') (hl : foldBlocks ft l s' rs cols = .ok r) :
    foldBlocks ft (b :: l) s rs cols = .ok r := by
  rw [foldBlocks_cons_ok, hb]
  exact ⟨rfl, s', 0, quiet_step hb ft cols h, hl⟩

/-- Rounds that open nothing are owed no column. -/
theorem groups_none (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → groupsOf ft ds Rs = []
  | [], _, _ => by simp [groupsOf]
  | _ :: _, [], _ => by simp [groupsOf]
  | d :: ds, R :: Rs, h => by
    obtain ⟨h1, h2⟩ := h d (List.mem_cons_self ..)
    rw [groupsOf, h1, h2, groups_none ft ds Rs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    rfl

/-- A sub-protocol whose rounds open nothing, in the fold: it takes its rounds and no column. -/
theorem fold_plain {b : Block S Cl} {es : List Fmt.Entry}
    (hb : b.rounds = es.map fun e => { entry := e }) (ft : ℕ) {l : List (Block S Cl)} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn}
    (hlen : es.length ≤ rs.length)
    (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
    (h : b.decide s ((rs.take es.length).map noDigest) [] = .ok s')
    (hl : foldBlocks ft l s' (rs.drop es.length) cols = .ok r) :
    foldBlocks ft (b :: l) s rs cols = .ok r := by
  rw [foldBlocks_cons_ok, hb, List.length_map]
  refine ⟨by rw [List.length_take, Nat.min_eq_left hlen], s', 0, ?_, hl⟩
  rw [Block.step_ok, hb, groups_none ft _ _ (by
    intro d hd
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
    exact ⟨rfl, rfl⟩)]
  exact ⟨hfit, rfl, h, rfl⟩

end General

/-! ## What the ledgers have left behind a link -/

section Left
variable {L : Type}

theorem takeInto_left {o : ℕ} : ∀ (n m : ℕ) (d : DState L) (acc : Array ℕ), Room d o (n + m) →
    ∃ l d', takeMasksInto o n d acc = some (l, d') ∧ Room d' o m
  | 0, m, d, acc, h => ⟨acc.toList, d, rfl, by simpa using h⟩
  | n + 1, m, d, acc, h => by
    have h' : Room d o (n + m + 1) := by rwa [Nat.add_right_comm] at h
    obtain ⟨i, d₁, h1, r1, -⟩ := takeMask_of_room h'
    obtain ⟨l, d', h2, r2⟩ := takeInto_left n m d₁ (acc.push i) r1
    refine ⟨l, d', ?_, r2⟩
    unfold takeMasksInto
    rw [h1]
    exact h2

/-- A ledger with n + m entries left has m left behind the taking of n. -/
theorem room_left {d d' : DState L} {o n m : ℕ} {l : List ℕ} (h : Room d o (n + m))
    (e : takeMasksP d o n = some (l, d')) : Room d' o m := by
  obtain ⟨l', d'', e', r⟩ := takeInto_left n m d #[] h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (e.symm.trans e'))
  exact r

/-- The other messages' ledgers stay. -/
theorem room_other {d d' : DState L} {o o' n m : ℕ} {l : List ℕ} (hne : o' ≠ o)
    (hn : Room d o n) (h : Room d o' m) (e : takeMasksP d o n = some (l, d')) : Room d' o' m := by
  obtain ⟨l', d'', e', -, k⟩ := takeMasks_of_room hn
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (e.symm.trans e'))
  exact k o' m hne h

theorem Room.mono {d : DState L} {o n m : ℕ} (h : Room d o (n + m)) : Room d o n := by
  obtain ⟨x, l, h1, h2, h3, h4⟩ := h
  exact ⟨x, l, h1, h2, h3, by omega⟩

/-- **Behind the two takings of a link**: what both ledgers have left. -/
theorem room_behind {d d₁ d₂ : DState L} {msg idx n₁ n₂ a b : ℕ} {o k : List ℕ} (hne : idx ≠ msg)
    (h1 : Room d msg (n₁ + a)) (h2 : Room d idx (n₂ + b))
    (e1 : takeMasksP d msg n₁ = some (o, d₁)) (e2 : takeMasksP d₁ idx n₂ = some (k, d₂)) :
    Room d₂ msg a ∧ Room d₂ idx b := by
  have r1 : Room d₁ msg a := room_left h1 e1
  have r2 : Room d₁ idx (n₂ + b) := room_other hne h1.mono h2 e1
  exact ⟨room_other (fun e => hne e.symm) r2.mono r1 e2, room_left r2 e2⟩

end Left

/-- **The fold over a lookup's link accepts.** -/
theorem link_fold (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) (ft : ℕ)
    {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {es : List Fmt.Entry} {gV : HeardV}
    {G G₂ : Fork} {cl : List PlaneClaim}
    (hf : s.base.fork = none) (hk : s.base.keys.length = i)
    (hne : s.idx ≠ one.ranges.messageId)
    (h1 : Room s.d one.ranges.messageId
      ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
    (h2 : Room s.d s.idx (2 * (faceOfLkp x).parts.length))
    (hv : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
    (hes : (lookupPlace set i x).entries = some es) (hlen : es.length ≤ rs.length)
    (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
    (hh : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots)
      ((rs.take es.length).map noDigest) = some (gV, G))
    (hL : Left (lookupPlace set i x) (toHeardG gV) G cl G₂) :
    ∃ o d₁ k d₂ rows keys,
      takeMasksP s.d one.ranges.messageId
        ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) = some (o, d₁) ∧
      takeMasksP d₁ s.idx (2 * (faceOfLkp x).parts.length) = some (k, d₂) ∧
      rowsInOrder (Wf.planesAt one.ranges one.codes i)
        (layerOrder (toHeardG gV).rows.toList.length) (G₂.paid (toHeardG gV).owedPlanes)
        (homes (faceOfLkp x) (o.map fun j => ⟨one.ranges.messageId, j⟩)
          (k.map fun j => ⟨s.idx, j⟩))
        ((toHeardG gV).rows.toList.map Sum.inl ++ cl.map Sum.inr) = some rows ∧
      foldBlocks ft (lookupLink one set i x).blocksInOrder s rs cols = .ok
        ({ s with
            d := d₂
            base := { s.base with
              fork := none, heard := none, home := #[]
              rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } },
          rs.drop es.length, cols) := by
  obtain ⟨o, d₁, k, d₂, e1, e2, hc⟩ := caller_decide one i x [] [] hv hf hk hne h1 h2
  -- every hidden value has a home
  obtain ⟨o', d₁', e1', l1, k1⟩ := takeMasks_of_room h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (e1.symm.trans e1'))
  obtain ⟨k', d₂', e2', l2, -⟩ := takeMasks_of_room (k1 s.idx _ hne h2)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (e2.symm.trans e2'))
  have hs : (homes (faceOfLkp x) (o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
      (k.map fun j => (⟨s.idx, j⟩ : Slot))).size = (faceOfLkp x).slots :=
    homes_size hv (by rw [List.length_map, l1]) (by rw [List.length_map, l2])
  -- the lookup's own sub-protocol
  have hd := key_decide set i x (s := { s with
      d := d₂
      base := { s.base with
        fork := some (({} : Fork).slots (faceOfLkp x).slots), heard := none
        home := homes (faceOfLkp x) (o.map fun j => ⟨one.ranges.messageId, j⟩)
          (k.map fun j => ⟨s.idx, j⟩) } }) [] (by rw [hes]; rfl) rfl hh
  -- the sub-protocol behind it
  obtain ⟨rows, keys, hrows, -, hy⟩ := layer_decide one set i x (s := lookupSeat.put { s with
      d := d₂
      base := { s.base with
        fork := some (({} : Fork).slots (faceOfLkp x).slots), heard := none
        home := homes (faceOfLkp x) (o.map fun j => ⟨one.ranges.messageId, j⟩)
          (k.map fun j => ⟨s.idx, j⟩) } } (toHeardG gV) G) [] [] rfl rfl hs hL
  refine ⟨o, d₁, k, d₂, rows, keys, e1, e2, hrows, ?_⟩
  refine fold_quiet rfl ft (link_lay one set i x hf) ?_
  refine fold_quiet rfl ft hc ?_
  refine fold_plain (by
    show ((lookupPlace set i x).entries.getD []).map _ = _
    rw [hes]
    rfl) ft hlen hfit hd ?_
  refine fold_quiet rfl ft hy ?_
  refine fold_quiet rfl ft (link_behind one set i x _) ?_
  refine fold_quiet rfl ft (link_clear one set i x _) ?_
  rfl

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.fold_quiet
#print axioms AtPublicFiles.KeyLookup.fold_plain
#print axioms AtPublicFiles.KeyLookup.room_behind
#print axioms AtPublicFiles.KeyLookup.link_fold
