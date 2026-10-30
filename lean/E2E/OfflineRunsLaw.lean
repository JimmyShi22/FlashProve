-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsLaw.lean: "every run returns" from what each sub-protocol owes along the invariant of form
(E2E/OfflineRunsForm.lean). General in the description, the book and the prover. Conditional lemmas on the
frame's own functions.

  `hear_form`, `play_form`   what a round, and a list of rounds, does to the challenges heard and to the columns
  `playsOn_of_blockPlays`   `PlaysOn` (Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean) at one sub-protocol, from the
                            invariant of form to the next, from `BlockPlays`. The columns are paid here, once:
                            what `play` yields fits the declared oracle messages (`tablesFit_play`), and where
                            the tables produced are those declared so far a sub-protocol's columns are
                            available (`member_served`, Honest/Law/RunsC.lean)
  `runs_of_blocks`          `RunsOfBlocks`: the call of `runC_returns` (Honest/Law/RunsFile.lean)

No acceptance is spent or shown. Nothing on any property.
-/
import E2E.OfflineRunsForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

section Chain
variable {S Cl V W Y Pb : Type}

/-- After a round's challenge the state has heard it, and the columns stay. -/
theorem hear_form {s : Step W Y} {x : Told} {d : Fmt.Drawn} {m m' : Mid W Y}
    (h : s.hear x d m = .ok m') : m'.st.heard = m.st.heard ++ [d] ∧ m'.opened = m.opened := by
  unfold Step.hear at h
  cases hmv : s.move with
  | none =>
    simp only [hmv] at h
    cases h
    exact ⟨rfl, rfl⟩
  | some mv =>
    simp only [hmv] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩

/-- After a list of rounds the state has heard their challenges, and the columns stay. -/
theorem play_form : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W Y)
    (y : List Played × Mid W Y), play ss ds back m = .ok y →
    y.2.st.heard = m.st.heard ++ ds ∧ y.2.opened = m.opened
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    exact ⟨(List.append_nil _).symm, rfl⟩
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, hm, hz, rfl⟩ := play_cons_ok h
    obtain ⟨a1, a2⟩ := hear_form hm
    obtain ⟨b1, b2⟩ := play_form ss ds back.tail m' z hz
    exact ⟨by rw [b1, a1, List.append_assoc]; rfl, b2.trans a2⟩

/-- The list up to and with number j. -/
theorem take_succ_of {α : Type} {l : List α} {j : Nat} {b : α} (h : l[j]? = some b) :
    l.take (j + 1) = l.take j ++ [b] := by
  rw [List.take_add_one, h]
  rfl

/-- The list, cut at number j. -/
theorem cut_at {α : Type} {l : List α} {j : Nat} {b : α} (h : l[j]? = some b) :
    l = l.take j ++ ([b] ++ l.drop (j + 1)) := by
  have e := List.take_append_drop (j + 1) l
  rw [take_succ_of h, List.append_assoc] at e
  exact e.symm

/-- The oracle messages of a list of steps, off the declared rows. -/
theorem oracles_of_pairs {l : List (Step W Y)} {rows : List (Fmt.DeclaredRound × List Oracle)}
    (h : l.map (fun s => (s.decl, s.oracles)) = rows) :
    l.flatMap (·.oracles) = rows.flatMap (·.2) := by
  rw [← h, List.flatMap_map]

/-- **`PlaysOn` at one sub-protocol along the invariant of form, from `BlockPlays`.** `all`: the chain's steps as
`ready` has prepared them, at whatever coins and input. -/
theorem playsOn_of_blockPlays {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat}
    {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {all : List (Step W Y)}
    {look₀ : Addr → (d : Due) × Cs d} {v₀ : Option V}
    (hall : chainSteps Bk (Bk.rowsOf chain) look₀ v₀ bs hs = .ok all)
    (hshape : ∀ b ∈ bs, b.planOk = true ∧ b.shaped = true) (hroot : rooted bs hs = true)
    (stored : Nat → Nat → Option (List UInt64))
    (Taken : (Nat → Nat → Option (Place × Table)) → Prop)
    (Start : List Fmt.Drawn → List Fmt.Drawn → Prop) (w : W) (hI : InTime all)
    (hS : ∀ taken, Taken taken →
      Served ⟨chain, ft, stored, fun ps => (envOf stored taken ps).tree⟩ taken all)
    {j : Nat} {b : Block S Cl} (hb : bs[j]? = some b)
    (hP : BlockPlays φ Bk chain hs b (MidForm Start (roundsIn bs j) w)) :
    PlaysOn φ Bk chain ft hs b (formAt stored Taken Start w bs j)
      (formAt stored Taken Start w bs (j + 1)) := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨hM, taken, laid, hT, rfl, hF⟩ := hA
  obtain ⟨y, hy⟩ := hP k m ds l hM hd hst hl
  have hbm : b ∈ bs := List.mem_of_getElem? hb
  -- the tables that the sub-protocol's rounds have produced
  have o_l := steps_shaped hl (fun b' hb' => by
    obtain rfl := List.mem_singleton.1 hb'
    exact hshape _ hbm)
  have hroot1 : rooted [b] hs = true := by
    unfold rooted at hroot ⊢
    rw [List.all_eq_true] at hroot
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact hroot b hbm
  have r_l := steps_noRoot hl hroot1
  have hTy : TablesFit (l.flatMap (·.oracles)) y.1 :=
    tablesFit_play l ds y.1 (play_yields l ds [] m y hy) o_l r_l
  have el : l.flatMap (·.oracles) = (rowsOfChain [b]).flatMap (·.2) := oracles_of_pairs (steps_pairs hl)
  have hnext : oraclesIn bs (j + 1) = oraclesIn bs j ++ (rowsOfChain [b]).flatMap (·.2) := by
    unfold oraclesIn rowsOfChain
    rw [take_succ_of hb, List.flatMap_append, List.flatMap_append]
  have hF' : TablesFit (oraclesIn bs (j + 1)) (laid ++ y.1) := by
    rw [hnext, ← el]
    exact tablesFit_append hF hTy
  -- the chain's steps, cut at the sub-protocol
  have hall' : chainSteps Bk (Bk.rowsOf chain) look₀ v₀ (bs.take j ++ ([b] ++ bs.drop (j + 1))) hs =
      .ok all := by
    rw [← cut_at hb]
    exact hall
  rw [chainSteps_append] at hall'
  obtain ⟨pre, hpre, hall'⟩ := exBind_ok hall'
  obtain ⟨l₂, hl₂, e₂⟩ := exMap_ok hall'
  rw [chainSteps_append] at hl₂
  obtain ⟨cur, hcur, hl₂⟩ := exBind_ok hl₂
  obtain ⟨post, -, e₃⟩ := exMap_ok hl₂
  have hsplit : all = pre ++ cur ++ post := by
    rw [← e₂, ← e₃, List.append_assoc]
  have epre : pre.flatMap (·.oracles) = oraclesIn bs j := oracles_of_pairs (steps_pairs hpre)
  have ecur : cur.flatMap (·.oracles) = (rowsOfChain [b]).flatMap (·.2) :=
    oracles_of_pairs (steps_pairs hcur)
  have hlen : b.oracles.length = b.rounds.length := (chainSteps_rows [b] hs cur hcur).1 b List.mem_cons_self
  have edecl : cur.map (·.decl) = b.rounds := by
    have g := congrArg (List.map (·.1)) (steps_pairs hcur)
    rw [List.map_map] at g
    refine g.trans ?_
    unfold rowsOfChain
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.map_fst_zip (by rw [hlen])
  obtain ⟨cols, hcols⟩ := member_served ⟨chain, ft, stored, fun ps => (envOf stored taken ps).tree⟩
    taken (fun _ => rfl) pre cur post (hsplit ▸ hI) (hsplit ▸ hS taken hT) (laid ++ y.1)
    (by rw [List.flatMap_append, epre, ecur, ← hnext]; exact hF') ds
  rw [edecl] at hcols
  refine ⟨y, cols, hy, ?_, fun s' n _ => ⟨?_, taken, laid ++ y.1, hT, envOf_add _ _ _ _, hF'⟩⟩
  · rw [envOf_add]
    exact hcols
  · -- the state's form behind the sub-protocol
    obtain ⟨i1, i2, i3⟩ := play_mid l ds [] m y hy
    obtain ⟨f1, f2⟩ := play_form l ds [] m y hy
    obtain ⟨h₀, l₀, ds₀, hs₀, hd₀, eh, eloc⟩ := hM.heard
    have hlen₀ := drawsFit_length _ _ hd₀
    refine ⟨i1.trans hM.input, ⟨h₀, l₀, ds₀ ++ ds, hs₀, ?_, ?_, ?_⟩, ?_, ?_⟩
    · unfold roundsIn at hd₀ hlen₀ ⊢
      rw [take_succ_of hb, List.flatMap_append, drawsFit_append, ← hlen₀, List.take_left',
        List.drop_left', hd₀]
      · simpa using hd
      · rfl
      · rfl
    · show y.2.st.heard = _
      rw [f1, eh, List.append_assoc]
    · show y.2.loc = _
      rw [i2, eloc, List.append_assoc]
    · show y.2.seen.map (·.drawn) = y.2.st.heard
      rw [i3, List.map_append, hM.seen, f1, yields_drawn _ _ _ _ (play_yields l ds [] m y hy)]
    · show (y.2.opened.map (· ++ cols)).isSome = true
      rw [f2]
      have := hM.opened
      cases ho : m.opened with
      | none => rw [ho] at this; cases this
      | some c => rfl

end Chain

section File
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **Every run returns, from what each sub-protocol owes along the invariant of form.** -/
theorem runs_of_blocks (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    RunsOfBlocks F Bk H := by
  intro w₀ rc x k ρ R hR plan hq hroot hP hB hρ hsil
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have P := (F.planOk_ok).1 plan
  simp only [rootedAll, Bool.and_eq_true] at hroot
  obtain ⟨⟨r1, r2⟩, r3⟩ := hroot
  have e1 : R.first.flatMap (·.oracles) = (rowsOfChain F.first.blocksInOrder).flatMap (·.2) :=
    oracles_of_pairs (steps_pairs s1)
  have e2 : R.shared.flatMap (·.oracles) = (rowsOfChain F.shared.blocksInOrder).flatMap (·.2) :=
    oracles_of_pairs (steps_pairs s2)
  refine runC_returns hR hq hρ hsil hP
    (formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder)
    (formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder)
    (formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder)
    (fun j b hb => playsOn_of_blockPlays s1 P.blocks₁ r1 _ _ _ _ hP.first.inTime
      (fun taken _ u hu => ⟨hP.first.stored u hu, fun o ho ch i e => absurd e (hP.own₁ u hu o ho ch i)⟩)
      hb (hB.first j b hb))
    (fun j b hb => playsOn_of_blockPlays s2 P.blocks₂ r2 _ _ _ _ hP.shared.inTime
      (fun taken _ u hu => ⟨hP.shared.stored u hu, fun o ho ch i e => absurd e (hP.own₂ u hu o ho ch i)⟩)
      hb (hB.shared j b hb))
    (fun j b hb => playsOn_of_blockPlays s3 P.blocks₃ r3 _ _ _ _ hP.second.inTime
      (fun taken hT u hu => ⟨hP.second.stored u hu, fun o ho ch i e => ?_⟩) hb (hB.second j b hb))
    ?_ ?_ ?_
  · -- what the second chain takes over is at hand
    obtain ⟨l₁, l₂, t1, t2, rfl⟩ := hT
    rcases hP.taken u hu o ho ch i e with ⟨rfl, orc, h1, h2⟩ | ⟨rfl, orc, h1, h2⟩
    · rw [e1] at h1
      obtain ⟨pt, g1, g2⟩ := t1.2 i orc h1
      exact ⟨pt, by simp [taken₃, g1], g2.trans h2⟩
    · rw [e2] at h1
      obtain ⟨pt, g1, g2⟩ := t2.2 i orc h1
      exact ⟨pt, by simp [taken₃, g1], g2.trans h2⟩
  · exact ⟨⟨rfl, ⟨[], [], [], ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩,
      fun _ _ => none, [], rfl, rfl, tablesFit_nil⟩
  · exact ⟨⟨rfl, ⟨[], [], [], ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩,
      fun _ _ => none, [], rfl, rfl, tablesFit_nil⟩
  · intro v₁ m₁ E₁ v₂ m₂ E₂ s₃ o₁ o₂ hI₁ hI₂ _ _ _
    obtain ⟨M₁, tk₁, l₁, rfl, rfl, t1⟩ := hI₁
    obtain ⟨M₂, tk₂, l₂, rfl, rfl, t2⟩ := hI₂
    obtain ⟨a₀, b₀, d₁, ⟨rfl, rfl⟩, f1, g1, g1'⟩ := M₁.heard
    obtain ⟨a₀', b₀', d₂, ⟨rfl, rfl⟩, f2, g2, -⟩ := M₂.heard
    have w1 : roundsIn F.first.blocksInOrder F.first.blocksInOrder.length = F.roundsDeclaredByBlocks.1 := by
      unfold roundsIn
      rw [List.take_length]
      rfl
    have w2 : roundsIn F.shared.blocksInOrder F.shared.blocksInOrder.length = F.roundsDeclaredByBlocks.2.1 := by
      unfold roundsIn
      rw [List.take_length]
      rfl
    have u1 : oraclesIn F.first.blocksInOrder F.first.blocksInOrder.length =
        (rowsOfChain F.first.blocksInOrder).flatMap (·.2) := by
      unfold oraclesIn
      rw [List.take_length]
    have u2 : oraclesIn F.shared.blocksInOrder F.shared.blocksInOrder.length =
        (rowsOfChain F.shared.blocksInOrder).flatMap (·.2) := by
      unfold oraclesIn
      rw [List.take_length]
    rw [w1] at f1
    rw [w2] at f2
    rw [u1] at t1
    rw [u2] at t2
    refine ⟨⟨rfl, ⟨m₁.st.heard ++ m₂.st.heard, m₁.loc, [], ⟨d₁, d₂, f1, f2, ?_, ?_⟩, rfl,
      (List.append_nil _).symm, (List.append_nil _).symm⟩, ?_, rfl⟩,
      taken₃ l₁ l₂, [], ⟨l₁, l₂, t1, t2, rfl⟩, envThird_eq _ _ _, tablesFit_nil⟩
    · rw [g1, g2]
      rfl
    · rw [g1']
      rfl
    · show (m₁.seen ++ m₂.seen).map (·.drawn) = m₁.st.heard ++ m₂.st.heard
      rw [List.map_append, M₁.seen, M₂.seen]

end File

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.play_form
#print axioms AtPublicFiles.OfflineRows.playsOn_of_blockPlays
#print axioms AtPublicFiles.OfflineRows.runs_of_blocks
