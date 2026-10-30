-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OwedThru.lean: Owed read through: Owed at a prover and its rows, at the index and randomness read through maps g and rd,
gives Owed at the prover read through (Prover.thru, Honest/ThruRun.lean) and its rows read through. Conditional lemmas on this library's
definitions: the end is a record of premises; nothing here shows Owed.

1.  Lettered.thru, Sides.thru: each list's row by rowThru; bud, place and the falls stay. Its On is onRowReadThrough (Honest/ThruRow.lean): the row's
    own On at the narrowed stand, at the member that the row holds at that number.
2.  owedThru_midAtW_thru, owedThru_midSharedAtW_thru: the walk's state before an address, read through, is the walk's own.
3.  owed_thru: the rule.
-/
import Johnson.Desc.ProofFile.Honest.ThruRow
import Johnson.Desc.ProofFile.Honest.ThruRows
import Johnson.Desc.ProofFile.Honest.Thread.RowsMute
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {S Cl V V' W W' Y Pb Xi W₀ W₀' Rc Rc' Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-! ## 1 A member is the row's at its number -/

theorem member_row : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)),
    ∀ u ∈ membersOf row j rs, ∃ i, u.number = j + i ∧ row[i]? = some (u.part, u.sim)
  | [], _, _, _, hu => by cases hu
  | x :: row, j, rs, u, hu => by
    have hu' : u ∈ (⟨j, rs.take x.1.moves.length, x.1, x.2⟩ : Member V W Y Pb) ::
        membersOf row (j + 1) (rs.drop x.1.moves.length) := hu
    rcases List.mem_cons.1 hu' with rfl | g
    · exact ⟨0, rfl, rfl⟩
    · obtain ⟨i, hi, he⟩ := member_row row (j + 1) _ u g
      exact ⟨i + 1, by omega, by simpa using he⟩

theorem member_row₀ (σ : Side S Cl V W Y Pb) {u : Member V W Y Pb} (h : u ∈ σ.members) :
    σ.row[u.number]? = some (u.part, u.sim) := by
  obtain ⟨i, hi, he⟩ := member_row σ.row 0 _ u h
  rw [hi]
  simpa using he

/-- Two members of one row that read to one member are one. -/
theorem member_unique {see : V' → V} {wit : W' → W} {row : List (Part V W Y × Sim Pb)}
    {u u₂ : Member V W Y Pb} (h : u.thru see wit = u₂.thru see wit)
    (h₁ : row[u.number]? = some (u.part, u.sim)) (h₂ : row[u₂.number]? = some (u₂.part, u₂.sim)) :
    u₂ = u := by
  have hn : u.number = u₂.number := congrArg (fun m : Member V' W' Y Pb => m.number) h
  have hr : u.rounds = u₂.rounds := congrArg (fun m : Member V' W' Y Pb => m.rounds) h
  rw [hn] at h₁
  have e := Option.some.inj (h₁.symm.trans h₂)
  obtain ⟨n, rs, p, s⟩ := u
  obtain ⟨n₂, rs₂, p₂, s₂⟩ := u₂
  cases hn
  cases hr
  cases e
  rfl

/-! ## 2 A list read through -/

/-- **A list read through.** -/
def Lettered.thru (see : V' → V) (wit : W' → W) (L : Lettered Bk S Cl V W Y Pb) :
    Lettered Bk S Cl V' W' Y Pb :=
  ⟨L.place, rowThru see wit L.row, fun k s m E => L.A k s (m.narrow wit) E,
    fun k s m E => L.B k s (m.narrow wit) E, onRowReadThrough see wit L.row L.On, L.bud⟩

theorem side_thru (see : V' → V) (wit : W' → W) (L : Lettered Bk S Cl V W Y Pb)
    (bs : List (Block S Cl)) (fs : List (Fall S)) :
    (L.thru see wit).side bs fs = (L.side bs fs).map (Side.thru see wit) :=
  seated_thru see wit bs L.place L.row fs

theorem side_row {L : Lettered Bk S Cl V W Y Pb} {bs : List (Block S Cl)} {fs : List (Fall S)}
    {σ : Side S Cl V W Y Pb} (h : L.side bs fs = some σ) : σ.row = L.row := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **Rows read through.** -/
def Sides.thru {F : FileDescription Xi} (g : W₀' → W₀) (rd : Rc' → Rc) (G : Sides F Bk W₀ Rc Ky Tr X₀ X) :
    Sides F Bk W₀' Rc' Ky Tr X₀ X :=
  { first := G.first.map (Lettered.thru (Local.thru g rd) (Local.thru g rd))
    shared := G.shared.map (Lettered.thru id (Common.thru g rd))
    second := G.second.map (Lettered.thru (Local.thru g rd) (Local.thru g rd))
    falls₁ := G.falls₁
    falls₂ := G.falls₂
    falls₃ := G.falls₃ }

theorem half_of_thru (see : V' → V) (wit : W' → W) (L : Lettered Bk S Cl V W Y Pb) :
    (⟨(L.thru see wit).place, (L.thru see wit).row.map (·.1)⟩ : Placed V' W' Y) =
      Placed.thru see wit ⟨L.place, L.row.map (·.1)⟩ := by
  unfold Lettered.thru Placed.thru rowThru
  simp

/-- **The prover of the rows read through is the prover of the rows, read through.** -/
theorem prover_thru {F : FileDescription Xi} (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀')
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    (G.thru g rd).prover (H.thru g rd d) = (G.prover H).thru g rd d := by
  have e₁ : (G.thru g rd).first.map (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)) =
      (G.first.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
    simp only [Sides.thru, List.map_map]
    exact List.map_congr_left fun L _ => half_of_thru _ _ L
  have e₂ : (G.thru g rd).shared.map (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)) =
      (G.shared.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map
        (Placed.thru id (Common.thru g rd)) := by
    simp only [Sides.thru, List.map_map]
    exact List.map_congr_left fun L _ => half_of_thru _ _ L
  have e₃ : (G.thru g rd).second.map (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)) =
      (G.second.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map
        (Placed.thru (Local.thru g rd) (Local.thru g rd)) := by
    simp only [Sides.thru, List.map_map]
    exact List.map_congr_left fun L _ => half_of_thru _ _ L
  unfold Sides.prover
  rw [e₁, e₂, e₃]
  rfl

theorem seated_sides_thru {F : FileDescription Xi} (g : W₀' → W₀) (rd : Rc' → Rc)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : (G.thru g rd).seated = G.seated := by
  have a : ∀ {S' V₁ V₂ W₁ W₂ Y₁ Pb₁ : Type} (see : V₂ → V₁) (wit : W₂ → W₁)
      (L : Lettered Bk S' F.Cl V₁ W₁ Y₁ Pb₁) (bs : List (Block S' F.Cl)),
      ((L.thru see wit).side bs).isSome = (L.side bs).isSome := fun see wit L bs => by
    rw [side_thru, Option.isSome_map]
  unfold Sides.seated Sides.thru
  simp only [List.all_map, Function.comp_def, a]

/-! ## 3 The state before an address, read through -/

theorem owedThru_map_bind_when_read {ε α β γ δ : Type} {e' : Except ε α} {e : Except ε β} (n : α → β)
    (h : e'.map n = e) {k' : α → Except ε γ} {k : β → Except ε δ} {f : γ → δ}
    (hk : ∀ a, (k' a).map f = k (n a)) : (e'.bind k').map f = e.bind k := by
  subst h
  cases e' with
  | error x => rfl
  | ok a => exact hk a

theorem takeWhile_thru_length (wit : W' → W) (a : Addr) : ∀ ss : List (Step W Y),
    ((ss.map (Step.thru wit)).takeWhile fun s => s.addr != a).length =
      (ss.takeWhile fun s => s.addr != a).length
  | [] => rfl
  | s :: ss => by
    have e : (Step.thru wit s).addr = s.addr := rfl
    simp only [List.map_cons, List.takeWhile_cons, e]
    split
    · simp only [List.length_cons, takeWhile_thru_length wit a ss]
    · rfl

theorem any_thru (wit : W' → W) (a : Addr) (ss : List (Step W Y)) :
    (ss.map (Step.thru wit)).any (·.addr == a) = ss.any (·.addr == a) := by
  simp only [List.any_map, Function.comp_def]
  rfl

theorem owedThru_midInW_thru (wit : W' → W) (L : Lay) (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z : ChainProgress S Cl W' Y) (a : Addr) :
    (midInW L (ss.map (Step.thru wit)) ds z a).map (Option.map (Mid.narrow wit)) =
      midInW L ss ds (ChainProgress.narrow wit z) a := by
  unfold midInW
  simp only [any_thru, takeWhile_thru_length]
  by_cases h : (!ss.any (·.addr == a)) = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, ← List.map_take,
      ← walk_thru wit L (ss.take (ss.takeWhile fun s => s.addr != a).length)
        (ds.take (ss.takeWhile fun s => s.addr != a).length) z]
    cases walk L ((ss.take (ss.takeWhile fun s => s.addr != a).length).map (Step.thru wit))
      (ds.take (ss.takeWhile fun s => s.addr != a).length) z <;> rfl

/-- **The state before an address of the first or the second chain, read through, is the prover's.** -/
theorem owedThru_midAtW_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)
    (a : Addr) (hd : H.inRange (g d) = H.inRange H.dummy) :
    (midAtW F B (H.thru g rd d) w rc x c ρ a).map (Option.map (Mid.narrow (Local.thru g rd))) =
      midAtW F B H (g w) (rd rc) x c ρ a := by
  simp only [midAtW, storedWords_thru]
  rw [ready_thru g rd d F B H w rc x c hd]
  cases hR : ready F B H (g w) (rd rc) x c with
  | error e => rfl
  | ok R =>
    have h := Ready.reads_thru g rd hR
    show ((ChainProgress.start _ F.first.blocksInOrder (some ((Ready.thru g rd w rc R).start₁ (H.thru g rd d))) _ []).bind _).map _ =
      (ChainProgress.start _ F.first.blocksInOrder (some (R.start₁ H)) _ []).bind _
    refine owedThru_map_bind_when_read (ChainProgress.narrow (Local.thru g rd))
      (ChainProgress.start_of_narrow (m' := some ((Ready.thru g rd w rc R).start₁ (H.thru g rd d))) _ _ _
        (congrArg some (Ready.start₁_narrow g rd d H h)) _ _)
      fun a₁ => ?_
    have ef : (Ready.thru g rd w rc R).first.any (·.addr == a) = R.first.any (·.addr == a) := by
      rw [h.first]
      exact any_thru _ _ _
    by_cases hb : R.first.any (·.addr == a) = true
    · rw [if_pos (ef.trans hb), if_pos hb, h.first]
      exact owedThru_midInW_thru _ _ _ _ _ _
    · rw [if_neg (fun e => hb (ef.symm.trans e)), if_neg hb]
      refine owedThru_map_bind_when_read (ChainProgress.narrow (Local.thru g rd)) (walk_of_thru _ _ h.first _ _)
        fun z₁ => ?_
      by_cases hs : (!sealQuiet z₁.laid) = true
      · exact (congrArg (Except.map _) (if_pos hs)).trans (Eq.trans rfl (if_pos hs).symm)
      · refine (congrArg (Except.map _) (if_neg hs)).trans (Eq.trans ?_ (if_neg hs).symm)
        refine owedThru_map_bind_when_read (ChainProgress.narrow (Common.thru g rd))
          (ChainProgress.start_of_narrow (m' := some ((Ready.thru g rd w rc R).start₂ (H.thru g rd d))) _ _ _
            (congrArg some (Ready.start₂_narrow g rd d H h)) _ _)
          fun a₂ => ?_
        refine owedThru_map_bind_when_read (ChainProgress.narrow (Common.thru g rd)) (walk_of_thru _ _ h.shared _ _)
          fun z₂ => ?_
        refine owedThru_map_bind_when_read (ChainProgress.narrow (Local.thru g rd))
          (ChainProgress.start_of_narrow _ _ _ (meet_read g rd d H h z₁.mid z₂.mid) _ _) fun a₃ => ?_
        rw [h.second]
        exact owedThru_midInW_thru _ _ _ _ _ _

/-- The like at an address of the shared chain. -/
theorem owedThru_midSharedAtW_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)
    (a : Addr) (hd : H.inRange (g d) = H.inRange H.dummy) :
    (midSharedAtW F B (H.thru g rd d) w rc x c ρ a).map (Option.map (Mid.narrow (Common.thru g rd))) =
      midSharedAtW F B H (g w) (rd rc) x c ρ a := by
  simp only [midSharedAtW, storedWords_thru]
  rw [ready_thru g rd d F B H w rc x c hd]
  cases hR : ready F B H (g w) (rd rc) x c with
  | error e => rfl
  | ok R =>
    have h := Ready.reads_thru g rd hR
    show ((ChainProgress.start _ F.shared.blocksInOrder (some ((Ready.thru g rd w rc R).start₂ (H.thru g rd d))) _ []).bind _).map _ =
      (ChainProgress.start _ F.shared.blocksInOrder (some (R.start₂ H)) _ []).bind _
    refine owedThru_map_bind_when_read (ChainProgress.narrow (Common.thru g rd))
      (ChainProgress.start_of_narrow (m' := some ((Ready.thru g rd w rc R).start₂ (H.thru g rd d))) _ _ _
        (congrArg some (Ready.start₂_narrow g rd d H h)) _ _)
      fun a₂ => ?_
    rw [h.shared]
    exact owedThru_midInW_thru _ _ _ _ _ _

theorem orRefused_read {e' : Except Refusal (Option (Mid W' Y))} {e : Except Refusal (Option (Mid W Y))}
    (n : Mid W' Y → Mid W Y) (h : e'.map (Option.map n) = e) {m : Mid W Y} (he : orRefused e = .ok m) :
    ∃ m', orRefused e' = .ok m' ∧ n m' = m := by
  subst h
  cases e' with
  | error x => cases he
  | ok o =>
    cases o with
    | none => cases he
    | some m' => exact ⟨m', rfl, Except.ok.inj he⟩

/-! ## 4 One list at one run -/

theorem carriedAt_thru (see : V' → V) (wit : W' → W) (k : Coins Bk) (chain : Nat) (a : Addr)
    (p : Part V W Y) : carriedAt Bk k chain a (p.thru see wit) = carriedAt Bk k chain a p := by
  unfold carriedAt
  rw [lendPart_thru]
  rfl

theorem owedAt_thru (see : V' → V) (wit : W' → W) (L : Lettered Bk S Cl V W Y Pb)
    (bs : List (Block S Cl)) (k : Coins Bk) (chain : Nat) (mid : Addr → Except Refusal (Mid W Y))
    (mid' : Addr → Except Refusal (Mid W' Y)) (r : Run) (st : List (Nat × Nat × List UInt64))
    (called : Addr → Bool)
    (hmid : ∀ a m, mid a = .ok m → ∃ m', mid' a = .ok m' ∧ m'.narrow wit = m)
    (h : L.mute.owedAt bs k chain mid r st called) :
    (L.thru see wit).mute.owedAt bs k chain mid' r st called := by
  intro σ' hσ' u' hu'
  have e : (L.thru see wit).side bs = (L.side bs).map (Side.thru see wit) := side_thru see wit L bs []
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 (e ▸ hσ')
  rw [members_thru] at hu'
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
  have hb := h σ hσ u hu
  refine ⟨hb.1, fun hc => ?_⟩
  obtain ⟨ca, m, h₁, h₂, hOn⟩ := hb.2 hc
  obtain ⟨m', h₃, rfl⟩ := hmid _ _ h₂
  refine ⟨ca, m', (carriedAt_thru see wit k chain _ u.part).trans h₁, h₃, fun u₂ hu₂ hrow => ?_⟩
  have hr := member_row₀ σ hu
  rw [side_row hσ] at hr
  obtain rfl := member_unique hu₂ hr hrow
  exact hOn

/-! ## 5 The rule -/

/-- **The base's relation: the image of a relation under the two maps**: the narrowest at which owed_thru can be asked. Too narrow a base relation fails
in sight here: all that owed_thru carries is at this image. -/
def imageRel (g : W₀' → W₀) (rd : Rc' → Rc) (Rel : W₀' → Rc' → Xi → Prop) : W₀ → Rc → Xi → Prop :=
  fun w₀ rc₀ x => ∃ w rc, Rel w rc x ∧ g w = w₀ ∧ rd rc = rc₀

theorem imageRel_of (g : W₀' → W₀) (rd : Rc' → Rc) {Rel : W₀' → Rc' → Xi → Prop} (w : W₀') (rc : Rc')
    (x : Xi) (h : Rel w rc x) : imageRel g rd Rel (g w) (rd rc) x := ⟨w, rc, h, rfl, rfl⟩

/-- **Owed read through.** -/
theorem owed_thru {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel₀ : W₀ → Rc → Xi → Prop} {Rel : W₀' → Rc' → Xi → Prop}
    (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (o : Owed F Bk H G.mute Rel₀)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hRel : ∀ w rc x, Rel w rc x → Rel₀ (g w) (rd rc) x) :
    Owed F Bk (H.thru g rd d) (G.thru g rd).mute Rel where
  plan := o.plan
  book := o.book
  places := o.places
  seats := by
    rw [seated_mute, seated_sides_thru, ← seated_mute]
    exact o.seats
  good := by
    refine ⟨fun L' hL' => ?_, fun L' hL' => ?_, fun L' hL' base skip => ?_⟩
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      refine goodAt_mute fun σ' hσ' => ?_
      obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 ((side_thru _ _ L _ _) ▸ hσ')
      have b := o.good.1 L.mute (List.mem_map_of_mem hL) σ hσ
      have b' : Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0
          (fun _ _ _ _ => False) (fun _ _ _ _ => False) L.On L.bud :=
        ⟨b.fits, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, b.exact, b.fresh⟩
      exact ⟨_, _, good_thru (faces_own g rd) (B' := fun _ _ _ _ => False)
        (fun u hu ca m f h => h u rfl ((side_row hσ) ▸ member_row₀ σ hu)) b'⟩
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      refine goodAt_mute fun σ' hσ' => ?_
      obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 ((side_thru _ _ L _ _) ▸ hσ')
      have b := o.good.2.1 L.mute (List.mem_map_of_mem hL) σ hσ
      have b' : Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
          (fun _ _ _ _ => False) (fun _ _ _ _ => False) L.On L.bud :=
        ⟨b.fits, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, b.exact, b.fresh⟩
      exact ⟨_, _, good_thru (faces_shared g rd) (B' := fun _ _ _ _ => False)
        (fun u hu ca m f h => h u rfl ((side_row hσ) ▸ member_row₀ σ hu)) b'⟩
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      refine goodAt_mute fun σ' hσ' => ?_
      obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 ((side_thru _ _ L _ _) ▸ hσ')
      have b := o.good.2.2 L.mute (List.mem_map_of_mem hL) [] 0 σ hσ
      have b' : Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk (orderOf F)
          2 F.lastChainFirstTreeNumber (fun _ _ _ _ => False) (fun _ _ _ _ => False) L.On L.bud :=
        ⟨b.fits, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, b.exact, b.fresh⟩
      exact ⟨_, _, good_thru (faces_own g rd) (B' := fun _ _ _ _ => False)
        (fun u hu ca m f h => h u rfl ((side_row hσ) ▸ member_row₀ σ hu)) b'⟩
  input := fun w rc x h => o.input (g w) (rd rc) x (hRel w rc x h)
  runs := by
    rw [prover_mute, prover_thru]
    intro w rc x h k ρ hρ hs
    rw [silentAt_thru] at hs
    rw [runC_thru g rd d F Bk (G.prover H) w rc x k ρ hd]
    have b := o.runs (g w) (rd rc) x (hRel w rc x h) k ρ hρ (by rw [prover_mute]; exact hs)
    rw [prover_mute] at b
    exact b
  owed := by
    rw [prover_mute, prover_thru]
    intro w rc x h k ρ r hρ hs hr
    rw [silentAt_thru] at hs
    rw [runC_thru g rd d F Bk (G.prover H) w rc x k ρ hd] at hr
    have b := o.owed (g w) (rd rc) x (hRel w rc x h) k ρ r hρ (by rw [prover_mute]; exact hs)
      (by rw [prover_mute]; exact hr)
    rw [prover_mute] at b
    obtain ⟨b₁, b₂, b₃⟩ := b
    refine ⟨fun L' hL' => ?_, fun L' hL' => ?_, fun L' hL' => ?_⟩
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      exact owedAt_thru _ _ L _ k 0 _ _ r.run _ r.called
        (fun a m hm => orRefused_read _ (owedThru_midAtW_thru g rd d F Bk (G.prover H) w rc x k ρ a hd) hm)
        (b₁ L.mute (List.mem_map_of_mem hL))
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      exact owedAt_thru _ _ L _ k 1 _ _ r.run _ r.called
        (fun a m hm => orRefused_read _ (owedThru_midSharedAtW_thru g rd d F Bk (G.prover H) w rc x k ρ a hd) hm)
        (b₂ L.mute (List.mem_map_of_mem hL))
    · obtain ⟨L₁, h₁, rfl⟩ := List.mem_map.1 hL'
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 h₁
      exact owedAt_thru _ _ L _ k 2 _ _ r.run _ r.called
        (fun a m hm => orRefused_read _ (owedThru_midAtW_thru g rd d F Bk (G.prover H) w rc x k ρ a hd) hm)
        (b₃ L.mute (List.mem_map_of_mem hL))

theorem addrsOf_thru (see : V' → V) (wit : W' → W) (l : List (Lettered Bk S Cl V W Y Pb)) :
    addrsOf (l.map (Lettered.thru see wit)) = addrsOf l := by
  unfold addrsOf
  simp [List.flatMap_map, Lettered.thru, rowThru]

/-- The test on the owners reads the rows' places and lengths alone. -/
theorem owns_thru {F : FileDescription Xi} (g : W₀' → W₀) (rd : Rc' → Rc)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : (G.thru g rd).owns = G.owns := by
  unfold Sides.owns Sides.thru
  simp only [addrsOf_thru]

/-! ## 6 Other columns with the same words -/

theorem midAtW_withStored (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B)
    (ρ : Draws) (a : Addr) (hs : (H.withStored s).storedWords w rc = H.storedWords w rc) :
    midAtW F B (H.withStored s) w rc x c ρ a = midAtW F B H w rc x c ρ a := by
  simp only [midAtW]
  rw [hs]
  rfl

theorem midSharedAtW_withStored (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B)
    (ρ : Draws) (a : Addr) (hs : (H.withStored s).storedWords w rc = H.storedWords w rc) :
    midSharedAtW F B (H.withStored s) w rc x c ρ a = midSharedAtW F B H w rc x c ρ a := by
  simp only [midSharedAtW]
  rw [hs]
  rfl

/-- **Owed at other columns with the same words, at Rel's inputs.** -/
theorem owed_withStored {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F))
    (hw : ∀ w rc x, Rel w rc x → (H.withStored s).storedWords w rc = H.storedWords w rc)
    (o : Owed F Bk H G Rel) : Owed F Bk (H.withStored s) G Rel where
  plan := o.plan
  book := o.book
  places := o.places
  seats := o.seats
  good := o.good
  input := o.input
  runs := fun w rc x h k ρ hρ hs => by
    have e : runC F Bk (G.prover (H.withStored s)) w rc x k ρ = runC F Bk (G.prover H) w rc x k ρ :=
      runC_withStored F Bk (G.prover H) s w rc x k ρ (hw w rc x h)
    rw [e]
    exact o.runs w rc x h k ρ hρ hs
  owed := fun w rc x h k ρ r hρ hs hr => by
    have e : runC F Bk (G.prover (H.withStored s)) w rc x k ρ = runC F Bk (G.prover H) w rc x k ρ :=
      runC_withStored F Bk (G.prover H) s w rc x k ρ (hw w rc x h)
    rw [e] at hr
    have b := o.owed w rc x h k ρ r hρ hs hr
    have e₁ : ∀ a, midAtW F Bk (G.prover (H.withStored s)) w rc x k ρ a =
        midAtW F Bk (G.prover H) w rc x k ρ a := fun a =>
      midAtW_withStored F Bk (G.prover H) s w rc x k ρ a (hw w rc x h)
    have e₂ : ∀ a, midSharedAtW F Bk (G.prover (H.withStored s)) w rc x k ρ a =
        midSharedAtW F Bk (G.prover H) w rc x k ρ a := fun a =>
      midSharedAtW_withStored F Bk (G.prover H) s w rc x k ρ a (hw w rc x h)
    simp only [e₁, e₂]
    rw [hw w rc x h]
    exact b

/-- **Owed at a committer's prover**, where it has the prover's key and the same words at Rel's inputs. -/
theorem owed_atCommitter {Sd Xc : Type} {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (Cm : Committer W₀ Rc Sd Xc Xi Ky) (item : Nat) (hk : Cm.key = H.key)
    (hw : ∀ w rc x, Rel w rc x →
      (H.withStored (Cm.columnsAt item)).storedWords w rc = H.storedWords w rc)
    (o : Owed F Bk H G Rel) : Owed F Bk (Cm.proverAt item H) G Rel := by
  have e : Cm.proverAt item H = H.withStored (Cm.columnsAt item) := by
    unfold Committer.proverAt Prover.withStored Committer.columnsAt
    rw [hk]
  rw [e]
  exact owed_withStored _ hw o

end ProofFile.Honest

#print axioms ProofFile.Honest.member_unique
#print axioms ProofFile.Honest.prover_thru
#print axioms ProofFile.Honest.owedThru_midAtW_thru
#print axioms ProofFile.Honest.owedThru_midSharedAtW_thru
#print axioms ProofFile.Honest.owedAt_thru
#print axioms ProofFile.Honest.owed_thru
#print axioms ProofFile.Honest.owns_thru
#print axioms ProofFile.Honest.imageRel
#print axioms ProofFile.Honest.owed_withStored
#print axioms ProofFile.Honest.owed_atCommitter
