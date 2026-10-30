--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyListed.lean: "A MEMBER OF A GROUP HAS THAT GROUP IN ITS OWN LIST" IS KEPT BY EVERY PLAIN
FUNCTION OF THE GROUND, the beginning of a proximity test among them; so it is kept by every
sub-protocol of the key file's three chains. A property of a statement, a relation between
statements, and theorems. On what the verifier's steps WRITE: nothing on whether
a step accepts; NOTHING IS SHOWN OF ANY PROVER.

WHY. The tests at a chain's end read a sampled message's own LIST OF GROUPS; the book-keeping of a
chain's state holds the groups' lists of MEMBERS. E2E/KeyEnds.lean takes the tie from members to
lists as a named premise (`Joined`). The library has the tie in the other direction (`Linked`,
Johnson/Desc/Ground/Linked.lean: a message's list names only groups that hold it), with the laws
that the ground's functions keep it. Here the same for this direction, in that file's order.

  `Listed T`: every member of every group is a message that is there and has the group in its list.
  `KeepsListed T T'`: if it holds in front it holds behind.
  `listed_start`: it holds of a statement without a group.
  `listed_modOracle`, `listed_modGroup`, `listed_stSent`, `listed_withGroup`, `listed_joined`,
    `listed_closeLedgers`, `listed_begun`: each plain change of a statement keeps it: a message's
    change that loses no entry of its list; a group's that gains no member; messages sent; a new
    group; a joining of a message THAT IS THERE, which writes both sides; ledgers closed; a test
    begun.
  **`groundKeeps_listed`**: `KeepsListed` meets the library's `GroundKeeps`
    (Johnson/Desc/GroundKeeps.lean): all ten functions. A joining keeps it BY ITS OWN CLAUSE "the
    message is there", which the proof reads out of the function's acceptance.
  `beginRun_listed`: the eleventh function, which `GroundKeeps` leaves out, keeps it too.
  **`three_listed`**: THE KEY FILE's THREE CHAINS KEEP IT. NO PREMISE. A call of the library's walk
    along the three chains, which is general in the relation (Johnson/RunOne/KeyWalkAny.lean: every
    relation that the ground's ten functions and the beginning of a proximity test keep is kept by
    every sub-protocol of the three chains, the four proximity tests in their seats among them).
  **`desc_listed`**: at the key file's IOP as written in Lean (`Key.descriptionFromSource X N P`): every sub-protocol
    of each chain's flat list keeps it. `start₁_listed`, `start₂_listed`: the first two chains'
    first states have it. **`listed_reached₁`**, `listed_reached₂`, `listed_reached₃`: it holds at
    every state that a chain reaches, in the library's own sense of "reached"; the third across the
    seam from the first chain's end. `fold_listed`: and behind every fold over such sub-protocols
    that has accepted.

Limits.
- "Keeps" speaks of a step that has accepted: nothing on whether a step accepts.
- The third chain's first state holds the first chain's last statement as it is: that tie is
  E2E/KeyStartThird.lean's `thirdFirst_listed`.
- The library's files that are called are not reviewed.


-/
import Johnson.Desc.Ground.LinkedKeeps
import Johnson.RunOne.KeyWalkAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps (Decides ChainKeeps)

/-- **Every member of every group is there and has the group in its own list.** -/
def Listed (T : Statement) : Prop :=
  ∀ (g : Nat) (G : OnBytes.Group) (o : Nat), T.groups[g]? = some G → o ∈ G.members →
    ∃ x : OnBytes.Oracle, T.oracles[o]? = some x ∧ g ∈ x.groups

/-- The relation of the invariant. -/
def KeepsListed (T T' : Statement) : Prop := Listed T → Listed T'

theorem KeepsListed.refl (T : Statement) : KeepsListed T T := id

theorem KeepsListed.trans {A B C : Statement} (h : KeepsListed A B) (k : KeepsListed B C) :
    KeepsListed A C := fun a => k (h a)

/-- It holds of a statement without a group. -/
theorem listed_start (T : Statement) (h : T.groups = #[]) : Listed T := by
  intro g G o hG _
  rw [h] at hG
  cases hG

/-! ## The plain changes of a statement -/

/-- A change of one message that loses no entry of its list of groups. -/
theorem listed_modOracle (T : Statement) (k : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x g, g ∈ x.groups → g ∈ (f x).groups) :
    KeepsListed T { T with oracles := T.oracles.modify k f } := by
  intro h g G o hG hm
  obtain ⟨x, hx, hgx⟩ := h g G o hG hm
  show ∃ x', (T.oracles.modify k f)[o]? = some x' ∧ g ∈ x'.groups
  rw [Array.getElem?_modify]
  split
  · exact ⟨f x, by rw [hx]; rfl, hf x g hgx⟩
  · exact ⟨x, hx, hgx⟩

/-- A change of one group that gains no member. -/
theorem listed_modGroup (T : Statement) (k : Nat) (f : OnBytes.Group → OnBytes.Group)
    (hf : ∀ G o, o ∈ (f G).members → o ∈ G.members) :
    KeepsListed T { T with groups := T.groups.modify k f } := by
  intro h g G' o hG' hm
  have hG : (T.groups.modify k f)[g]? = some G' := hG'
  rw [Array.getElem?_modify] at hG
  split at hG
  · obtain ⟨G, hG₀, rfl⟩ := Option.map_eq_some_iff.1 hG
    exact h g G o hG₀ (hf G o hm)
  · exact h g G' o hG hm

theorem listed_stSent (T : Statement) (sent : Array OracleNotice) :
    KeepsListed T (stSent T sent) := by
  intro h g G o hG hm
  obtain ⟨x, hx, hgx⟩ := h g G o hG hm
  refine ⟨x, ?_, hgx⟩
  show (T.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x
  rw [Array.getElem?_append, if_pos (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

theorem listed_withGroup (T : Statement) (code maskCode : Nat) :
    KeepsListed T (Ground.withGroup T code maskCode) := by
  intro h g G o hG hm
  have hG' : (T.groups.push { code := code, maskCode := maskCode })[g]? = some G := hG
  rw [Array.getElem?_push] at hG'
  split at hG'
  · obtain rfl := Option.some.inj hG'
    exact absurd hm (Array.not_mem_empty o)
  · exact h g G o hG' hm

/-- A message THAT IS THERE joins the group G: BOTH SIDES ARE WRITTEN. -/
theorem listed_joined (T : Statement) (g o : Nat) (kept : Bool) (G : OnBytes.Group)
    (x : OnBytes.Oracle) (hx : T.oracles[o]? = some x) : KeepsListed T (withMessageInGroup T g o kept G) := by
  intro h g' G' o' hG' hm
  have orc : ∀ (a : Nat) (y : OnBytes.Oracle) (b : Nat), T.oracles[a]? = some y → b ∈ y.groups →
      ∃ y', (T.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[a]? = some y' ∧
        b ∈ y'.groups := by
    intro a y b hy hb
    rw [Array.getElem?_modify]
    split
    · exact ⟨{ y with groups := y.groups ++ [g] }, by rw [hy]; rfl,
        List.mem_append.2 (Or.inl hb)⟩
    · exact ⟨y, hy, hb⟩
  show ∃ y', (T.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[o']? = some y' ∧
    g' ∈ y'.groups
  have hG : (withMessageInGroup T g o kept G).groups[g']? = some G' := hG'
  unfold withMessageInGroup at hG
  simp only [Array.getElem?_modify] at hG
  split at hG
  · rename_i e
    subst e
    obtain ⟨G₁, hG₁, rfl⟩ := Option.map_eq_some_iff.1 hG
    have hm' : o' ∈ G₁.members.insertIdxIfInBounds (G.members.filter (· < o)).size o := hm
    unfold Array.insertIdxIfInBounds at hm'
    split at hm'
    · rcases Array.mem_insertIdx.1 hm' with e | e
      · subst e
        refine ⟨{ x with groups := x.groups ++ [g] }, ?_,
          List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))⟩
        rw [Array.getElem?_modify, if_pos rfl, hx]
        rfl
      · obtain ⟨y, hy, hb⟩ := h g G₁ o' hG₁ e
        exact orc o' y g hy hb
    · obtain ⟨y, hy, hb⟩ := h g G₁ o' hG₁ hm'
      exact orc o' y g hy hb
  · obtain ⟨y, hy, hb⟩ := h g' G' o' hG hm
    exact orc o' y g' hy hb

theorem listed_closeLedgers (l : List Nat) : ∀ T : Statement, KeepsListed T (closeLedgers T l) := by
  induction l with
  | nil => exact KeepsListed.refl
  | cons o l ih =>
    intro T
    exact (listed_modOracle T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ _ k => k).trans (ih _)

/-- The beginning of a proximity test: ledgers closed, the mark laid, the open rows taken. -/
theorem listed_begun (T : Statement) (g : Nat) (G : OnBytes.Group) :
    KeepsListed T (begun T g G) :=
  (listed_closeLedgers G.members.toList T).trans
    (listed_modGroup (closeLedgers T G.members.toList) g
      (fun G => { G with inRun := true, rows := #[] }) fun _ _ k => k)

/-! ## The ground's functions -/

/-- **The relation meets the library's structure of what a relation on statements owes**: all ten
functions. -/
theorem groundKeeps_listed : GroundKeeps KeepsListed where
  refl := KeepsListed.refl
  trans := KeepsListed.trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact listed_withGroup d.st code maskCode
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact listed_stSent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · cases hx : d.st.oracles[o]? with
      | none => simp [hx] at h
      | some x =>
        cases hp : Own.padMade d.st.codes x.shape with
        | none => simp [hx, hp] at h
        | some places =>
          simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          exact listed_modOracle d.st o _ fun _ _ k => k
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · rename_i hok
      have hthere := clause_of_ok _ hok ("join: the message is there", (d.st.oracles[o]?).isSome)
        (by simp [joinL])
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hthere
      cases hg : d.st.groups[g]? with
      | none => simp [hg] at h
      | some G =>
        simp only [hg, Option.map_some, Option.some.injEq] at h
        subst h
        exact listed_joined d.st g o kept G x hx
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact listed_modGroup d.st g (fun G => { G with rows := G.rows.push row }) fun _ _ k => k
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact listed_modOracle d.st o _ fun _ _ k => k
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact listed_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact listed_modOracle d.st o _ fun _ _ k => k
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact listed_stSent d.st sent
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · cases hy : other.oracles[theirs]? with
      | none => simp [hy] at h
      | some y =>
        simp only [hy, Option.map_some, Option.some.injEq] at h
        subst h
        exact listed_modOracle d.st mine _ fun _ _ k => k
    · cases h

/-- **The eleventh function**, the beginning of a proximity test, keeps it too. -/
theorem beginRun_listed {L : Type} (d d' : DState L) (g : Nat) (r : RunInput)
    (h : beginRunP d g = some (r, d')) : KeepsListed d.st d'.st := by
  unfold beginRunP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact listed_begun d.st g G
  · cases h

/-! ## Along the key file's chains: calls -/

section Chains
open Johnson.RunOne.KeyKeeps (st₁ st₂ st₃)
open Johnson.RunOne.KeyWalk (BeginKeeps)

/-- The eleventh function, in the library's own form of that premise. -/
theorem begin_listed : BeginKeeps KeepsListed := fun d d' g r h => beginRun_listed d d' g r h

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- **THE KEY FILE's THREE CHAINS KEEP IT.** No premise. By the library's walk along the three
chains, which is general in the relation. -/
theorem three_listed :
    ChainKeeps (By KeepsListed (st₁ (β := Key.LookupRecord))) (Key.descriptionFromSource X N P).first ∧
      ChainKeeps (By KeepsListed st₂) (Key.descriptionFromSource X N P).shared ∧
      ChainKeeps (By KeepsListed st₃) (Key.descriptionFromSource X N P).second :=
  Johnson.RunOne.KeyWalk.three_keeps groundKeeps_listed begin_listed

/-- **Every sub-protocol of each of the three chains' flat lists keeps it**: where its decision
accepts at a state whose statement has the property, the state behind has it. -/
theorem desc_listed :
    (∀ b ∈ (Key.descriptionFromSource X N P).first.blocksInOrder, Decides (By KeepsListed (st₁ (β := Key.LookupRecord))) b) ∧
      (∀ b ∈ (Key.descriptionFromSource X N P).shared.blocksInOrder, Decides (By KeepsListed st₂) b) ∧
      ∀ b ∈ (Key.descriptionFromSource X N P).second.blocksInOrder, Decides (By KeepsListed st₃) b :=
  ⟨Johnson.RunOne.KeyWalk.flat_keeps₁' groundKeeps_listed begin_listed,
    Johnson.RunOne.KeyWalk.flat_keeps₂' groundKeeps_listed begin_listed,
    Johnson.RunOne.KeyWalk.flat_keeps₃' groundKeeps_listed begin_listed⟩

/-- The first chain's first state has it: no group. -/
theorem start₁_listed (x : Key.Xi) :
    Listed (st₁ ((Key.descriptionFromSource X N P).start₁ ((Key.descriptionFromSource X N P).pub x))) := listed_start _ rfl

/-- The shared chain's first state has it: no group. -/
theorem start₂_listed (x : Key.Xi) :
    Listed (st₂ ((Key.descriptionFromSource X N P).start₂ ((Key.descriptionFromSource X N P).pub x))) := listed_start _ rfl

variable {X N P}

/-- **It holds at every state that the first chain reaches** (the library's `LPFD.Hist₁`). -/
theorem listed_reached₁ (D : OnBytes.Maker.WholeD) (k : Nat)
    (a : (Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) (h : LPFD.Hist₁ (Key.descriptionFromSource X N P) D k a) :
    Listed (st₁ (show Key.FirstState from a.2)) :=
  Johnson.RunOne.KeyWalk.inv_at_reached₁ (I := Listed) groundKeeps_listed begin_listed
    (fun _ => listed_start _ rfl) D k a h

/-- **At every state that the shared chain reaches.** -/
theorem listed_reached₂ (D : OnBytes.Maker.WholeD) (k : Nat)
    (a : ((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) × (Key.descriptionFromSource X N P).S₂)
    (h : LPFD.Hist₂ (Key.descriptionFromSource X N P) D k a) :
    Listed (st₂ (show _root_.Desc.K14.St from a.2)) :=
  Johnson.RunOne.KeyWalk.inv_at_reached₂ (I := Listed) groundKeeps_listed begin_listed
    (fun _ => listed_start _ rfl) D k a h

/-- **At every state that the third chain reaches**: across the seam from the first chain's end. -/
theorem listed_reached₃ (D : OnBytes.Maker.WholeD) (k : Nat)
    (a : ((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂) ×
      (Key.descriptionFromSource X N P).S₃) (h : LPFD.Hist₃ (Key.descriptionFromSource X N P) D k a) :
    Listed (st₃ (show Third.S₃ from a.2)) :=
  Johnson.RunOne.KeyWalk.inv_at_reached₃ (I := Listed) groundKeeps_listed begin_listed
    (fun _ => listed_start _ rfl) D k a h

/-- **It holds behind every fold over sub-protocols that keep it, where the fold has accepted.** -/
theorem fold_listed {S Cl : Type} (st : S → Statement) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, Decides (By KeepsListed st) b) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft bs s rs cols = .ok r)
    (h0 : Listed (st s)) : Listed (st r.1) :=
  Keeps.foldBlocks_keeps (By KeepsListed st) (fun _ => KeepsListed.refl _)
    (fun _ _ _ a b => KeepsListed.trans a b) ft bs hb s rs cols r h h0

end Chains

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.KeepsListed.refl
#print axioms AtPublicFiles.AtFiles.KeepsListed.trans
#print axioms AtPublicFiles.AtFiles.listed_start
#print axioms AtPublicFiles.AtFiles.listed_modOracle
#print axioms AtPublicFiles.AtFiles.listed_modGroup
#print axioms AtPublicFiles.AtFiles.listed_stSent
#print axioms AtPublicFiles.AtFiles.listed_withGroup
#print axioms AtPublicFiles.AtFiles.listed_joined
#print axioms AtPublicFiles.AtFiles.listed_closeLedgers
#print axioms AtPublicFiles.AtFiles.listed_begun
#print axioms AtPublicFiles.AtFiles.groundKeeps_listed
#print axioms AtPublicFiles.AtFiles.beginRun_listed
#print axioms AtPublicFiles.AtFiles.begin_listed
#print axioms AtPublicFiles.AtFiles.three_listed
#print axioms AtPublicFiles.AtFiles.desc_listed
#print axioms AtPublicFiles.AtFiles.start₁_listed
#print axioms AtPublicFiles.AtFiles.start₂_listed
#print axioms AtPublicFiles.AtFiles.listed_reached₁
#print axioms AtPublicFiles.AtFiles.listed_reached₂
#print axioms AtPublicFiles.AtFiles.listed_reached₃
#print axioms AtPublicFiles.AtFiles.fold_listed
