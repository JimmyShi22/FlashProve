-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontMembers.lean: two clauses of the front's test on a
group, as a sentence on the statement that every function of the ground keeps: the members of every
group rise, and every member knows the group.

  MembersFacts, MembersStay   the sentence, with "every member is sampled" beside it; the relation
  pairwise_insert, members_joined   a message joins a group
  groundKeeps_members, stKeeps_members   it meets all that the library asks of a relation on the
                   statement
  membersFacts_reached   under the head AtMgA at the older hash, at every state that a fold over the
                   first chain's members reaches
  membersFacts_second    the block "K14, second part" keeps it

Limits.
- It says nothing where a statement has no group.
- Nothing on a group's rows, on a message's pad or on the book.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Ground (GroundKeeps ok rowL)
open VerifiableInference.Desc.K13.Law (StKeeps)
open OnBytes.Means (SampledMembers)

/-- **Every member is sampled, the members of every group rise, and a member knows its group.** -/
def MembersFacts (T : Statement) : Prop :=
  SampledMembers T ∧ ∀ (g : ℕ) (G : Group), T.groups[g]? = some G →
    G.members.toList.Pairwise (· < ·) ∧
      ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, T.oracles[o]? = some x → g ∈ x.groups

/-- If it holds in front, it holds behind. -/
def MembersStay (A B : Statement) : Prop := MembersFacts A → MembersFacts B

/-- A step that leaves each group's members, or lays an empty group, and each message's groups. -/
theorem members_later {A B : Statement} (hM : SampledMembers A → SampledMembers B)
    (hg : ∀ (g : ℕ) (G' : Group), B.groups[g]? = some G' → G'.members = #[] ∨
      ∃ G : Group, A.groups[g]? = some G ∧ G'.members = G.members)
    (ho : ∀ (o : ℕ) (y : OnBytes.Oracle), A.oracles[o]? = some y →
      ∃ x : OnBytes.Oracle, B.oracles[o]? = some x ∧ x.groups = y.groups) : MembersStay A B := by
  intro hA
  refine ⟨hM hA.1, fun g G' hG' => ?_⟩
  rcases hg g G' hG' with e | ⟨G, hG, e⟩
  · rw [e]
    exact ⟨List.Pairwise.nil, fun o h => by cases h⟩
  · obtain ⟨h1, h2⟩ := hA.2 g G hG
    refine ⟨by rw [e]; exact h1, fun o hm x hx => ?_⟩
    rw [e] at hm
    obtain ⟨y, hy, -⟩ := hA.1 g G hG o hm
    obtain ⟨x', hx', e'⟩ := ho o y hy
    obtain rfl := Option.some.inj (hx.symm.trans hx')
    rw [e']
    exact h2 o hm y hy

/-- One message is turned, and keeps its groups. -/
theorem keepsGroups_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).groups = x.groups) (j : ℕ) (y : OnBytes.Oracle)
    (hy : S.oracles[j]? = some y) :
    ∃ x : OnBytes.Oracle, (S.oracles.modify o f)[j]? = some x ∧ x.groups = y.groups := by
  rw [Array.getElem?_modify]
  by_cases c : o = j
  · subst c
    exact ⟨f y, by rw [if_pos rfl, hy]; rfl, hf y⟩
  · exact ⟨y, by rw [if_neg c]; exact hy, rfl⟩

theorem members_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).groups = x.groups)
    (hM : SampledMembers S → SampledMembers { S with oracles := S.oracles.modify o f }) :
    MembersStay S { S with oracles := S.oracles.modify o f } :=
  members_later hM (fun _ G' h => Or.inr ⟨G', h, rfl⟩) (keepsGroups_modify S o f hf)

theorem members_sent (S : Statement) (sent : Array OracleNotice)
    (hM : SampledMembers S → SampledMembers (stSent S sent)) : MembersStay S (stSent S sent) := by
  refine members_later hM (fun _ G' h => Or.inr ⟨G', h, rfl⟩) fun o y hy => ⟨y, ?_, rfl⟩
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hy
  show (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some y
  rw [Array.getElem?_append_left hlt]
  exact hy

/-- Closing ledgers turns ledgers alone. -/
theorem closeLedgers_keepsGroups : ∀ (l : List ℕ) (S : Statement) (o : ℕ) (y : OnBytes.Oracle),
    S.oracles[o]? = some y →
    ∃ x : OnBytes.Oracle, (closeLedgers S l).oracles[o]? = some x ∧ x.groups = y.groups
  | [], _, _, y, hy => ⟨y, hy, rfl⟩
  | a :: l, S, o, y, hy => by
    have e : closeLedgers S (a :: l) = closeLedgers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } l := rfl
    rw [e]
    obtain ⟨x₁, h₁, e₁⟩ := keepsGroups_modify S a
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      (fun _ => rfl) o y hy
    obtain ⟨x₂, h₂, e₂⟩ := closeLedgers_keepsGroups l { S with oracles := S.oracles.modify a fun x =>
      { x with ledger := x.ledger.map fun l => { l with closed := true } } } o x₁ h₁
    exact ⟨x₂, h₂, e₂.trans e₁⟩

/-- A new number put behind the smaller ones of a rising list leaves it rising. -/
theorem pairwise_insert : ∀ (l : List ℕ) (o : ℕ), l.Pairwise (· < ·) → o ∉ l →
    (l.insertIdx (l.filter (· < o)).length o).Pairwise (· < ·)
  | [], o, _, _ => by simp
  | a :: l, o, hp, hn => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 hp
    have hne : o ≠ a := fun e => hn (e ▸ List.mem_cons_self)
    have hn' : o ∉ l := fun hm => hn (List.mem_cons_of_mem _ hm)
    by_cases c : a < o
    · have e : ((a :: l).filter (· < o)).length = (l.filter (· < o)).length + 1 := by
        simp [List.filter_cons, c]
      rw [e, List.insertIdx_succ_cons]
      refine List.pairwise_cons.2 ⟨fun b hb => ?_, pairwise_insert l o hl hn'⟩
      have hpos : (l.filter (· < o)).length ≤ l.length := List.length_filter_le _ _
      rcases (List.mem_insertIdx hpos).1 hb with rfl | hb'
      · exact c
      · exact ha b hb'
    · have hoa : o < a := by omega
      have hf : (a :: l).filter (· < o) = [] := by
        refine List.filter_eq_nil_iff.2 fun b hb => ?_
        rcases List.mem_cons.1 hb with rfl | hb'
        · simpa using c
        · have := ha b hb'
          simp only [decide_eq_true_eq]
          omega
      rw [hf]
      simp only [List.length_nil, List.insertIdx_zero]
      refine List.pairwise_cons.2 ⟨fun b hb => ?_, hp⟩
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact hoa
      · exact Nat.lt_trans hoa (ha b hb')

/-- **A message joins a group.** It is put in its place among the members, and it is a new member. -/
theorem members_joined {S : Statement} {g o : ℕ} {kept : Bool} {G : Group} {x : OnBytes.Oracle}
    (hG : S.groups[g]? = some G) (hx : S.oracles[o]? = some x) (hs : x.sampled = true)
    (hn : G.members.contains o = false) (hA : MembersFacts S) :
    MembersFacts (withMessageInGroup S g o kept G) := by
  have hnew : ∀ (j : ℕ) (y : OnBytes.Oracle), S.oracles[j]? = some y →
      (S.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[j]? =
        some (if o = j then { y with groups := y.groups ++ [g] } else y) := by
    intro j y hy
    rw [Array.getElem?_modify]
    by_cases c : o = j
    · subst c
      rw [if_pos rfl, if_pos rfl, hy]
      rfl
    · rw [if_neg c, if_neg c]
      exact hy
  refine ⟨hA.1.withMessageInGroup g o kept G x hG hx hs, fun g' G' hG' => ?_⟩
  have hG'' : (S.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[g']? = some G' :=
    hG'
  rw [Array.getElem?_modify] at hG''
  by_cases c : g = g'
  · subst c
    rw [if_pos rfl, hG] at hG''
    obtain rfl := Option.some.inj hG''
    obtain ⟨h1, h2⟩ := hA.2 g G hG
    have hno : o ∉ G.members.toList := by
      intro hm
      rw [Array.contains_eq_true_of_mem (Array.mem_toList_iff.1 hm)] at hn
      cases hn
    have hsize : (G.members.filter (· < o)).size = (G.members.toList.filter (· < o)).length := by
      rw [← Array.length_toList, Array.toList_filter]
    have hpos : (G.members.filter (· < o)).size ≤ G.members.toList.length := by
      rw [Array.length_toList]
      exact Array.size_filter_le
    refine ⟨?_, fun a ha y hy => ?_⟩
    · show (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList.Pairwise _
      rw [OnBytes.Means.toList_insertIdxIfInBounds, hsize]
      exact pairwise_insert _ o h1 hno
    · have ha' : a ∈ (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList := ha
      rw [OnBytes.Means.toList_insertIdxIfInBounds] at ha'
      have hy' : (S.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[a]? = some y := hy
      rcases (List.mem_insertIdx hpos).1 ha' with rfl | hm
      · rw [hnew _ x hx, if_pos rfl] at hy'
        obtain rfl := Option.some.inj hy'
        exact List.mem_append_right _ List.mem_cons_self
      · obtain ⟨z, hz, -⟩ := hA.1 g G hG a hm
        rw [hnew a z hz] at hy'
        obtain rfl := Option.some.inj hy'
        split
        · exact List.mem_append_left _ (h2 a hm z hz)
        · exact h2 a hm z hz
  · rw [if_neg c] at hG''
    obtain ⟨h1, h2⟩ := hA.2 g' G' hG''
    refine ⟨h1, fun a ha y hy => ?_⟩
    obtain ⟨z, hz, -⟩ := hA.1 g' G' hG'' a ha
    have hy' : (S.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[a]? = some y := hy
    rw [hnew a z hz] at hy'
    obtain rfl := Option.some.inj hy'
    split
    · exact List.mem_append_left _ (h2 a ha z hz)
    · exact h2 a ha z hz

/-- **The ground's functions keep it.** -/
theorem groundKeeps_members : GroundKeeps MembersStay where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := by
    intro L d d' code maskCode n h hA
    have hM := OnBytes.Means.newGroupP_members h hA.1
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have st : MembersStay d.st (VerifiableInference.Desc.Ground.withGroup d.st code maskCode) := by
        refine members_later (fun _ => hM) (fun j G' hG => ?_) (fun _ y hy => ⟨y, hy, rfl⟩)
        have hG' : (d.st.groups.push { code := code, maskCode := maskCode })[j]? = some G' := hG
        rw [Array.getElem?_push] at hG'
        split at hG'
        · obtain rfl := Option.some.inj hG'
          exact Or.inl rfl
        · exact Or.inr ⟨G', hG', rfl⟩
      exact st hA
    · cases h
  recv := by
    intro L ft d d' sent ids h hA
    have hM := OnBytes.Means.recvP_members h hA.1
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact members_sent _ _ (fun _ => hM) hA
    · cases h
  admit := by
    intro L d d' o rows h hA
    have hM := OnBytes.Means.admitP_members h hA.1
    unfold VerifiableInference.Desc.Ground.admitP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.admitL d.st o rows) = true
    · rw [if_pos c] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, places, _, rfl⟩ := h
      exact members_modify d.st o (fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape }) (fun _ => rfl) (fun _ => hM) hA
    · rw [if_neg c] at h
      cases h
  join := by
    intro L d d' g o kept h hA
    unfold VerifiableInference.Desc.Ground.joinP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.joinL d.st g o kept) = true
    · rw [if_pos c] at h
      obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [ok, VerifiableInference.Desc.Ground.joinL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, c2, c3, _, _, _, c7, _⟩ := c
      cases hx : d.st.oracles[o]? with
      | none =>
        rw [hx] at c2
        cases c2
      | some x =>
        rw [hx, OnBytes.Means.has_some] at c3
        rw [hG, OnBytes.Means.has_some] at c7
        exact members_joined hG hx c3 (by simpa using c7) hA
    · rw [if_neg c] at h
      cases h
  addRow := by
    intro L d d' g row h hA
    have hM := OnBytes.Means.addRowP_members h hA.1
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · obtain rfl := Option.some.inj h
      have st : MembersStay d.st (withRow d.st g row) := by
        refine members_later (fun _ => hM) (fun j G' hG => Or.inr ?_) (fun _ y hy => ⟨y, hy, rfl⟩)
        have hG' : (d.st.groups.modify g fun G => { G with rows := G.rows.push row })[j]? =
            some G' := hG
        rw [Array.getElem?_modify] at hG'
        by_cases c : g = j
        · subst c
          rw [if_pos rfl] at hG'
          obtain ⟨G₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hG'
          exact ⟨G₀, h₀, rfl⟩
        · rw [if_neg c] at hG'
          exact ⟨G', hG', rfl⟩
      exact st hA
    · cases h
  takeMask := by
    intro L d d' o n h hA
    have hM := OnBytes.Means.takeMaskP_members h hA.1
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact members_modify d.st o (fun x => { x with ledger := some { l with
        next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
        (fun _ => rfl) (fun _ => hM) hA
    · cases h
  closeLedger := by
    intro L d d' o h hA
    have hM := OnBytes.Means.closeLedgerP_members h hA.1
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact members_later (fun _ => hM)
        (fun _ G' hG => Or.inr ⟨G', by
          rw [← OnBytes.Means.closeLedgers_groups [o] d.st]
          exact hG, rfl⟩) (closeLedgers_keepsGroups [o] d.st) hA
    · cases h
  spendAsMask := by
    intro L d d' o h hA
    have hM := OnBytes.Means.spendAsMaskP_members h hA.1
    unfold VerifiableInference.Desc.Ground.spendAsMaskP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact members_modify d.st o (fun x => { x with spentAsMask := true }) (fun _ => rfl)
        (fun _ => hM) hA
    · cases h
  adopt := by
    intro L d d' sent given ids h hA
    have hM := OnBytes.Means.adoptP_members h hA.1
    unfold VerifiableInference.Desc.Ground.adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact members_sent _ _ (fun _ => hM) hA
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h hA
    have hM := OnBytes.Means.elsewhereP_members h hA.1
    unfold VerifiableInference.Desc.Ground.elsewhereP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.elsewhereL d.st mine other theirs) = true
    · rw [if_pos c] at h
      obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact members_modify d.st mine (fun x => { x with
        sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad })
        (fun _ => rfl) (fun _ => hM) hA
    · rw [if_neg c] at h
      cases h

/-- **The sentence meets all that the library asks of a relation on the statement.** -/
theorem stKeeps_members : StKeeps MembersStay where
  ground := groundKeeps_members
  begun := by
    intro T g G hA
    refine members_later (fun h => h.begun g G) (fun j G' hG => ?_)
      (fun o y hy => ?_) hA
    · have e : (begun T g G).groups = T.groups.modify g
          (fun G => { G with inRun := true, rows := #[] }) := by
        have e₀ := OnBytes.Means.closeLedgers_groups G.members.toList T
        simp only [begun, e₀]
      rw [e, Array.getElem?_modify] at hG
      by_cases c : g = j
      · subst c
        rw [if_pos rfl] at hG
        obtain ⟨G₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hG
        exact Or.inr ⟨G₀, h₀, rfl⟩
      · rw [if_neg c] at hG
        exact Or.inr ⟨G', hG, rfl⟩
    · exact closeLedgers_keepsGroups G.members.toList T o y hy
  row := by
    intro lay im o n lin T r os' h hA
    obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
      (VerifiableInference.Desc.First.Pend.pendingRowO_iff lay im o n lin T.oracles _ _).1 h
    exact members_modify T im (fun x => { x with ledger := some l' }) (fun _ => rfl)
      (fun h => h.onOracle im (fun x => { x with ledger := some l' }) rfl rfl fun _ hs => hs) hA

section Head
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open VerifiableInference.Desc (Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At every state that a fold over the first k members reaches from the chain's own start.** -/
theorem membersFacts_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : ℕ)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) :
    MembersFacts y.1.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : (ProofFile.startS Zp p).st.groups = #[] := by
    unfold ProofFile.startS
    dsimp only
    split
    · show Zp.s₀.st.groups = #[]
      rw [Meaning.K2.s0_first O.pub]
      rfl
    · rfl
  have h0 : MembersFacts (ProofFile.startS Zp p).st := by
    refine ⟨fun g G hG => ?_, fun g G hG => ?_⟩ <;> · rw [e] at hG; simp at hG
  exact Meaning.K2.open_fold_all (Meaning.K2.seatKeeps_by stKeeps_members)
    (Meaning.K2.seatBack_by stKeeps_members) O trivial (fun _ _ _ => trivial)
    (Johnson.AtFull.Shape.plans_at h) k hf h0

end Head

/-- **The block "K14, second part" keeps it.** -/
theorem membersFacts_second {Cl : Type} (p : VerifiableInference.Desc.Third.P₁₄)
    (s s' : VerifiableInference.Desc.Third.S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hA : MembersFacts s.st) : MembersFacts s'.st := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := VerifiableInference.Desc.Third.Law.k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨_, _, _, a', d₁, _, _, _, ha', _, h1, h2⟩ :=
    VerifiableInference.Desc.Third.Law.takeOver_inv _ _ _ _ _ ha
  exact groundKeeps_members.addRow _ _ _ _ hb (groundKeeps_members.join _ _ _ _ _ h2
    (groundKeeps_members.elsewhere _ _ _ _ _ h1 (groundKeeps_members.adopt _ _ _ _ _ ha' hA)))

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.pairwise_insert
#print axioms ProofFile.Honest.K12.AtFile.members_joined
#print axioms ProofFile.Honest.K12.AtFile.stKeeps_members
#print axioms ProofFile.Honest.K12.AtFile.membersFacts_reached
#print axioms ProofFile.Honest.K12.AtFile.membersFacts_second
