-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnMarks.lean: three marks on a statement go along the key
file's three chains, whoever plays: every member of a group is sampled; every tensor of every open row
passes `Tensor.ok`; every open row of every group passes the five clauses of the adding that read its
summands. So at a stand in front of the own test the verifier's statement has all three. Steps of the
verifier's: nothing is shown of any prover.

  `Marked`          the three marks
  `marked_empty`    a statement without a group has them
  `sampled_of_members`   the first mark in the form that `notMember_of_sampled` reads
  `groundKeeps_marked`, `begin_marked`   the ground's ten functions and the beginning of a proximity
                    test keep them: at the admitting and at the copying of a sample the first mark pays
                    the premise of the third
  `fold_marked₁`, `fold_marked₃`   a fold over blocks of the first, of the last chain keeps them
  `marked_of_made`  at a stand in front of the own test the statement has them, where the thread began
                    at what the two earlier chains' folds return (`EndsAre`, K12/AtFile/WDoor.lean)
  `claims_of_marked`   the front's named test on the open rows (`claimsB`), at a state on entry whose
                    group is there and has not begun

By what. `groundKeeps_members` (Johnson/Desc/Means/FrameKeeps.lean), `groundKeeps_ord`, `stKeeps_ord`
(Johnson/AtFull/Shape/OpenRowsOrder.lean), the laws `X_claims`, `rowsPass_of_claims`
(Johnson/Desc/Ground/Shape/Claims.lean), `flat_keeps₁'`, `flat_keeps₃'` (Johnson/RunOne/KeyWalkAny.lean),
`start₃_same` (Johnson/RunOne/KeySmpStay.lean), `foldBlocks_keeps`.

Limits.
- What the marks say of a row is its form at the statement: that a row holds of anything is not touched.
- They say nothing of a message's sample rows.
- `marked_of_made` stands on `EndsAre`: the first chain's fold from its own start. At a stand at which
  that is false it says nothing.
- NOT IN FRONT OF A LAW OVER COINS: `marked_of_made` stands behind `Thread.Made`.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WDoor
import Johnson.AtFull.Shape.OpenRowsOrder
import Johnson.Desc.Ground.Shape.Claims
import Johnson.Desc.Means.FrameKeeps
import Johnson.RunOne.KeyWalkAny
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Means
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Ground.Sh (claimsAtB claimsAt_iff membersSampledS notMember_of_sampled
  stSh orc_get grp_get rowsPass_of_claims)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState LookupRecord descriptionFromSource)
open ProofFile.Honest.K12.AtFile (EndsAre)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.AtFull.Shape (OpenOrd OrdStays openOrd_none groundKeeps_ord stKeeps_ord)
open Johnson.RunOne.KeyKeeps (st₁ st₃)
open Johnson.RunOne.KeySmp (start₃_same)
open Johnson.RunOne.KeyWalk (BeginKeeps flat_keeps₁' flat_keeps₃')
open ProofFile.Honest.Sh (claimsB)

/-- **The three marks.** -/
def Marked (S : Statement) : Prop :=
  SampledMembers S ∧ OpenOrd S ∧ ∀ g, claimsAtB S g = true

/-- A statement without a group has them. -/
theorem marked_empty {S : Statement} (h : S.groups = #[]) : Marked S := by
  refine ⟨fun g G hG => ?_, openOrd_none h, fun g => claimsAt_iff.2 fun G hG => ?_⟩ <;>
    · rw [h] at hG
      simp at hG

/-- Every member is sampled, as the test on a shape reads it. -/
theorem sampled_of_members {S : Statement} (h : SampledMembers S) (g : Nat) :
    membersSampledS (stSh S) g = true := by
  unfold membersSampledS
  rw [grp_get]
  cases hG : S.groups[g]? with
  | none => rfl
  | some G =>
    show (G.members.toList.all fun o => ((stSh S).oracles[o]?).any (·.sampled)) = true
    refine List.all_eq_true.2 fun o ho => ?_
    obtain ⟨x, hx, hs⟩ := h g G hG o ho
    rw [orc_get, hx]
    exact hs

open VerifiableInference.Desc.Ground.Sh (newGroup_claims recv_claims admit_claims join_claims
  addRow_claims takeMask_claims closeLedger_claims spend_claims adopt_claims elsewhere_claims
  beginRun_claims admit_unsampled elsewhere_unsampled) in
/-- **The ground's ten functions keep the three marks.** -/
theorem groundKeeps_marked : GroundKeeps fun a b => Marked a → Marked b where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := fun d d' code maskCode n h x =>
    ⟨groundKeeps_members.newGroup d d' code maskCode n h x.1,
      groundKeeps_ord.newGroup d d' code maskCode n h x.2.1,
      fun g => newGroup_claims d d' code maskCode n h g (x.2.2 g)⟩
  recv := fun ft d d' sent ids h x =>
    ⟨groundKeeps_members.recv ft d d' sent ids h x.1, groundKeeps_ord.recv ft d d' sent ids h x.2.1,
      fun g => recv_claims ft d d' sent ids h g (x.2.2 g)⟩
  admit := fun d d' o rows h x =>
    ⟨groundKeeps_members.admit d d' o rows h x.1, groundKeeps_ord.admit d d' o rows h x.2.1,
      fun g => admit_claims d d' o rows h g
        (notMember_of_sampled (sampled_of_members x.1 g) (admit_unsampled d d' o rows h))
        (x.2.2 g)⟩
  join := fun d d' g' o kept h x =>
    ⟨groundKeeps_members.join d d' g' o kept h x.1, groundKeeps_ord.join d d' g' o kept h x.2.1,
      fun g => join_claims d d' g' o kept h g (x.2.2 g)⟩
  addRow := fun d d' g' row h x =>
    ⟨groundKeeps_members.addRow d d' g' row h x.1, groundKeeps_ord.addRow d d' g' row h x.2.1,
      fun g => addRow_claims d d' g' row h g (x.2.2 g)⟩
  takeMask := fun d d' o n h x =>
    ⟨groundKeeps_members.takeMask d d' o n h x.1, groundKeeps_ord.takeMask d d' o n h x.2.1,
      fun g => takeMask_claims d d' o n h g (x.2.2 g)⟩
  closeLedger := fun d d' o h x =>
    ⟨groundKeeps_members.closeLedger d d' o h x.1, groundKeeps_ord.closeLedger d d' o h x.2.1,
      fun g => closeLedger_claims d d' o h g (x.2.2 g)⟩
  spendAsMask := fun d d' o h x =>
    ⟨groundKeeps_members.spendAsMask d d' o h x.1, groundKeeps_ord.spendAsMask d d' o h x.2.1,
      fun g => spend_claims d d' o h g (x.2.2 g)⟩
  adopt := fun d d' sent given ids h x =>
    ⟨groundKeeps_members.adopt d d' sent given ids h x.1,
      groundKeeps_ord.adopt d d' sent given ids h x.2.1,
      fun g => adopt_claims d d' sent given ids h g (x.2.2 g)⟩
  elsewhere := fun d d' mine other theirs h x =>
    ⟨groundKeeps_members.elsewhere d d' mine other theirs h x.1,
      groundKeeps_ord.elsewhere d d' mine other theirs h x.2.1,
      fun g => elsewhere_claims d d' mine other theirs h g
        (notMember_of_sampled (sampled_of_members x.1 g)
          (elsewhere_unsampled d d' mine other theirs h))
        (x.2.2 g)⟩

/-- **The beginning of a proximity test keeps them.** -/
theorem begin_marked : BeginKeeps fun a b => Marked a → Marked b := by
  intro d d' g run h x
  obtain ⟨G, hG, -, e⟩ := beginRunP_inv h
  refine ⟨?_, ?_, fun g' => VerifiableInference.Desc.Ground.Sh.beginRun_claims d d' g run h g'
    (x.2.2 g')⟩
  · rw [e]
    exact x.1.begun g G
  · rw [e]
    exact stKeeps_ord.begun _ _ _ x.2.1

section
variable {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- A fold over blocks of the first chain keeps them. -/
theorem fold_marked₁ (ft : Nat) (s : FirstState) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : FirstState × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (descriptionFromSource Xs Nr Pl).first.blocksInOrder s rs cols = .ok r) (h0 : Marked (st₁ s)) :
    Marked (st₁ r.1) :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps (By (fun a b => Marked a → Marked b) st₁)
    (fun _ x => x) (fun _ _ _ p q x => q (p x)) ft _
    (flat_keeps₁' groundKeeps_marked begin_marked) s rs cols r h h0

/-- A fold over blocks of the last chain keeps them. -/
theorem fold_marked₃ (ft n : Nat) (s : S₃) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : S₃ × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take n) s rs cols = .ok r)
    (h0 : Marked (st₃ s)) : Marked (st₃ r.1) :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps (By (fun a b => Marked a → Marked b) st₃)
    (fun _ x => x) (fun _ _ _ p q x => q (p x)) ft _
    (fun b hb => flat_keeps₃' groundKeeps_marked begin_marked b (List.mem_of_mem_take hb)) s rs cols
    r h h0

variable {Bk : ProverCoinCounts} {V Pb W₀ Rc Tr X : Type}

/-- **At a stand in front of the own test the statement has the three marks.** -/
theorem marked_of_made (T : Thread Bk S₃ Claim V (Local W₀ Rc Xi Tr) X Pb)
    (hbs : T.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hM : T.Made 2 k st m E) {base : List OpenedColumn}
    {e₁ : (descriptionFromSource Xs Nr Pl).S₁} {e₂ : (descriptionFromSource Xs Nr Pl).S₂} (hE : EndsAre (descriptionFromSource Xs Nr Pl) m base e₁ e₂)
    (hs : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub m.st.input.x) e₁ e₂ = .ok s₀) :
    Marked st.st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hM
  obtain ⟨r₁, r₂, rest, c₁, c₂, -, -, -, -, -, -, f₁, -⟩ := hE
  have a₁ : Marked (st₁ (show FirstState from e₁)) :=
    fold_marked₁ (Xs := Xs) (Nr := Nr) (Pl := Pl) 0 _ _ _ _ f₁ (marked_empty rfl)
  have a₂ : Marked (st₃ s₀) := by
    rw [start₃_same (hs s₀ hbeg)]
    exact a₁
  have hf : foldBlocks T.ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀
      (m.seen.drop T.front) cols = .ok (st, [], []) := by
    rw [← hbs]
    exact hfold
  exact fold_marked₃ (Xs := Xs) (Nr := Nr) (Pl := Pl) T.ft 2 s₀ _ _ _ hf a₂

end

/-- **The front's named test on the open rows**, at a state on entry whose group is there and has not
begun. -/
theorem claims_of_marked {t : T12} (h : Marked t.st) {G : Group} (hG : t.st.groups[t.g]? = some G)
    (hrun : G.inRun = false) : claimsB t = true :=
  rowsPass_of_claims hG hrun (h.2.2 t.g)

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.Marked
#print axioms ProofFile.Honest.K12.AtKey.marked_empty
#print axioms ProofFile.Honest.K12.AtKey.sampled_of_members
#print axioms ProofFile.Honest.K12.AtKey.groundKeeps_marked
#print axioms ProofFile.Honest.K12.AtKey.begin_marked
#print axioms ProofFile.Honest.K12.AtKey.fold_marked₁
#print axioms ProofFile.Honest.K12.AtKey.fold_marked₃
#print axioms ProofFile.Honest.K12.AtKey.marked_of_made
#print axioms ProofFile.Honest.K12.AtKey.claims_of_marked
