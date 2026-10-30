-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PubNear.lean: the part of a state that `ManyJob.layFits`
(RunMany.lean) reads, and that this part, at the state on entry to each of the shared chain's two
proximity tests, is a term made from the plan alone, wherever the blocks before the test return.

  `pubNear`        the codes; the group under test without its rows; its members' shapes
  `fitsBy`, `layFitsNear`   `layFits` as a function of that part
  `layFits_near` `A.layFits t = layFitsNear A (pubNear t)`, for every job and every state: `layFits`
                   reads no more than `pubNear`
  `nearOf`, `pubNear_of_pub`   `pubNear` is a function of `pubOf` (FitShared.lean)
  `near_at_U`      at the test on G_u: `pubNear t = nearOf (pubBehind Q sentU) 0`
  `near_at_Omega`  at the test on G_omega, behind the eight and the test on G_u:
                   `pubNear t = nearOf (pubBehind Q sentU) 1`
  `pubNear_stateOfPub`   that part of `stateOfPub P` (FitShared.lean)
  `pubNear_doorOf`, `layFits_allNear`, `layFits_atDoorNear`   `pubOf_doorOf`, `layFits_all` and
                   `layFits_atDoor` (FitSharedLaw.lean) at `pubNear`
  `nearDoor_U`, `nearDoor_Omega`   `pubNear (doorOf ..)` is the plan's for every input and whatever
                   precedes the test, without a hypothesis on the run

By what. `layFits` and `Statement.layout` (OnBytes/Iop/Ground.lean) are unfolded; of a message they
read the shape alone, and only at the group's members. At G_u: PubAtDoor.lean. Through the test on
G_u: the library's `onGu_leaves` (Johnson/Desc/K12/Coin/SamplesThrough.lean): the codes, every other
group and every elder message's shape but the first mask's stay.

Limits. The wider statement, that all of `pubOf` is the plan's, does not hold at the test on G_omega
with this fall-back: wherever the fold returns, the state also holds the groups and messages that
the test on G_u has added (by reading of the library's statements on that test; PubAtSmall.lean and
PubAtSmallDoor.lean evaluate it at the small example). The theorems here do not name their shapes,
code numbers, members and kept marks; the library has them as a function of the shape of the state
in front (`testCore`, `k12_core_sh`, Johnson/Desc/K12/Honest/Shape/TestCore.lean), which is not
called here. So `pubOf` of that state can take two values; `pubNear` has one. The two public
premises of PubAtDoor.lean; at G_omega also that the block of the test on G_u passes its test on the
plan. The fold is over the eight and the test on G_u, without the chain's front block
(`door_U_front`, PubAtDoor.lean, has it for `pubOf` at G_u). Statements of the form "where it
returns". `doorOf` returns its parameter `fall` where the fold or `enter` fails, so `nearDoor_U` and
`nearDoor_Omega` are also true of that fall-back: they do not tell a fold that failed from one that
returned. At the test on G_omega `doorOf` returns `fall` at every honest run, as long as a part is
handed no opened column: the blocks before that test hold the test on G_u, which reads opened
columns. So these statements are no statement that the state on entry is the verifier's. Nothing on
completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PubAtDoor
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.K12.Law.Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape OracleNotice TableKey ceilLog2 layBlocks noId)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St blocks first withU withOmega)

variable {W X : Type}

/-! ## 1 What `layFits` reads -/

/-- The codes; the group under test without its rows, with its members' shapes in the members'
order; none where there is no such group. -/
abbrev Near : Type := Codes × Option (PubGroup × Array OracleShape)

/-- **The part of a state that `layFits` reads.** -/
def pubNear (t : T12) : Near :=
  (t.st.codes, (t.st.groups[t.g]?).map fun G =>
    (pubG G, G.members.map fun o => (t.st.oracles.getD o default).shape))

/-- `layFits` at the codes c, the group G without its rows, and the shape of member number i. -/
def fitsBy (A : ManyJob W X) (c : Codes) (G : PubGroup) (at_ : ℕ → OracleShape) : Bool :=
  let sizes (part : OnBytes.Part) : Array (Option ℕ) :=
    (Array.range G.members.size).map fun i =>
      if decide (0 < (at_ i).rows part) && !(part == .main && G.kept.getD i false) then
        some (ceilLog2 ((at_ i).rows part))
      else none
  let mask := layBlocks (sizes .mask)
  let main := layBlocks (sizes .main)
  let h := ceilLog2 mask.2
  max (max (ceilLog2 main.2) h) 1 == A.s₀.k && h == A.s₀.h &&
    G.members.size == A.mems.length &&
    sameCode (c.base.getD G.code default) A.s₀.C &&
    sameCode (c.mask.getD G.maskCode default) A.s₀.Z &&
    A.mems.zipIdx.all fun m =>
      let o := at_ m.2
      !G.kept.getD m.2 false && o.mainRows == m.1.shape.mainRows &&
        o.maskRows == m.1.shape.maskRows &&
        (o.mainRows == 0 || (o.mainDeg == 1) == m.1.shape.base) &&
        main.1.getD m.2 none == firstOr m.1.shape.mainRows m.1.shape.mainFirst &&
        mask.1.getD m.2 none == firstOr m.1.shape.maskRows m.1.shape.maskFirst

/-- **`layFits` as a function of `pubNear`.** -/
def layFitsNear (A : ManyJob W X) (N : Near) : Bool :=
  match N.2 with
  | some x => fitsBy A N.1 x.1 fun i => x.2.getD i default
  | none => false

theorem has_shape (S : OnBytes.Statement) (o : ℕ) (part : OnBytes.Part) :
    S.has o part = decide (0 < (S.oracles.getD o default).shape.rows part) := by
  unfold OnBytes.Statement.has
  rw [Array.getD_eq_getD_getElem?]
  cases S.oracles[o]? with
  | some x => rfl
  | none => cases part <;> rfl

theorem rowBits_shape (S : OnBytes.Statement) (o : ℕ) (part : OnBytes.Part) :
    S.rowBits o part = ceilLog2 ((S.oracles.getD o default).shape.rows part) := by
  unfold OnBytes.Statement.rowBits
  rw [Array.getD_eq_getD_getElem?]
  cases S.oracles[o]? with
  | some x => rfl
  | none => cases part <;> rfl

/-- `layFits`, with the layout written out. -/
theorem layFits_by (A : ManyJob W X) (t : T12) :
    A.layFits t = match t.st.groups[t.g]? with
      | some G => fitsBy A t.st.codes (pubG G) fun i =>
          (t.st.oracles.getD (G.members.getD i noId) default).shape
      | none => false := by
  unfold ManyJob.layFits OnBytes.Statement.layout
  cases t.st.groups[t.g]? with
  | none => rfl
  | some G =>
    simp only [Option.map_some, has_shape, rowBits_shape]
    rfl

/-- An index of `zipIdx` lies below the start plus the length. -/
theorem idx_below {α : Type} : ∀ (l : List α) (k : ℕ) (x : α × ℕ), x ∈ l.zipIdx k →
    x.2 < k + l.length
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := idx_below l (k + 1) x h
      simp only [List.length_cons]
      omega

theorem all_same {α : Type} (f g : α → Bool) : ∀ l : List α, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_same f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- `fitsBy` reads the shapes of the members alone. -/
theorem fitsBy_congr (A : ManyJob W X) (c : Codes) (G : PubGroup) (f g : ℕ → OracleShape)
    (h : ∀ i < G.members.size, f i = g i) : fitsBy A c G f = fitsBy A c G g := by
  have hs : ∀ part : OnBytes.Part,
      ((Array.range G.members.size).map fun i =>
        if decide (0 < (f i).rows part) && !(part == .main && G.kept.getD i false) then
          some (ceilLog2 ((f i).rows part))
        else none) =
      (Array.range G.members.size).map fun i =>
        if decide (0 < (g i).rows part) && !(part == .main && G.kept.getD i false) then
          some (ceilLog2 ((g i).rows part))
        else none := by
    intro part
    refine Array.map_congr_left fun i hi => ?_
    rw [h i (Array.mem_range.1 hi)]
  unfold fitsBy
  simp only [hs]
  by_cases hm : (G.members.size == A.mems.length) = true
  · congr 1
    refine all_same _ _ _ fun m hmem => ?_
    have hlt : m.2 < G.members.size := by
      have := idx_below A.mems 0 m hmem
      rw [beq_iff_eq.1 hm]
      omega
    simp only [h m.2 hlt]
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.and_false, Bool.false_and]

/-- **`layFits` reads no more than `pubNear`.** -/
theorem layFits_near (A : ManyJob W X) (t : T12) : A.layFits t = layFitsNear A (pubNear t) := by
  rw [layFits_by]
  unfold layFitsNear pubNear
  cases t.st.groups[t.g]? with
  | none => rfl
  | some G =>
    show fitsBy A t.st.codes (pubG G) _ = fitsBy A t.st.codes (pubG G) _
    refine fitsBy_congr A _ _ _ _ fun i hi => ?_
    have hi' : i < G.members.size := hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi',
      Option.map_some, Option.getD_some]

/-! ## 2 `pubNear` is a function of `pubOf` -/

/-- That part of a public part P, at the group number g. -/
def nearOf (P : PubState) (g : ℕ) : Near :=
  (P.codes, (P.groups[g]?).map fun G => (G, G.members.map fun o => P.shapes.getD o default))

theorem pubNear_of_pub (t : T12) : pubNear t = nearOf (pubSt t.st) t.g := by
  unfold pubNear nearOf pubSt
  simp only [Array.getElem?_map, Option.map_map]
  congr 1
  cases t.st.groups[t.g]? with
  | none => rfl
  | some G =>
    show some (pubG G, _) = some (pubG G, _)
    congr 2
    refine Array.map_congr_left fun o _ => ?_
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases t.st.oracles[o]? <;> rfl

/-! ## 3 At the two tests -/

/-- **At the test on G_u.** -/
theorem near_at_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : TableKey)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (x : St × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks 0 bs (first Q.codes key) rs cols = .ok x)
    (he : VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) x.1 = .ok t) :
    pubNear t = nearOf (pubBehind Q sentU) 0 := by
  have e := pub_at_U Q bs hb hS hM sentU hw key rs cols x t h he
  have e1 : pubSt t.st = pubBehind Q sentU := congrArg Prod.fst e
  have e2 : t.g = 0 := congrArg Prod.snd e
  rw [pubNear_of_pub, e1, e2]

/-- What goes out with o_u is two messages, where masks are sent ahead. -/
theorem withU_two {S : OnBytes.Params.LinShape} {sentU : Array OracleNotice}
    (hM : S.masksAhead = true) (hw : withU S = some sentU) : sentU.size = 2 := by
  unfold withU OnBytes.linWithU at hw
  rw [if_pos hM] at hw
  simp only [Option.bind_eq_bind, Option.pure_def, Option.map_eq_some_iff,
    Option.bind_eq_some_iff, Option.some.injEq] at hw
  obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hw
  rfl

/-- What goes out with o_omega is two messages, where the shape splits. -/
theorem withOmega_two {S : OnBytes.Params.LinShape} (hS : S.sharedSplitNeeded = true) :
    (withOmega S).size = 2 := by
  unfold withOmega OnBytes.linMessageOmega
  rw [if_pos hS]
  rfl

/-- **At the test on G_omega**, behind the eight and the test on G_u. p: the parameters of the test
on G_u. -/
theorem near_at_Omega (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (key : TableKey)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (x : St × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks 0 (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
      (first Q.codes key) rs cols = .ok x)
    (he : VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) x.1 = .ok t) :
    pubNear t = nearOf (pubBehind Q sentU) 1 := by
  obtain ⟨d8, rs', cols', h8, h9⟩ :=
    (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  have B := behind_fold Q bs hb hS hM sentU hw key rs cols _ h8
  obtain ⟨_, d9, k9, s9, h9⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h9
  simp only [foldBlocks, Except.ok.injEq] at h9
  subst h9
  obtain ⟨_, _, e9⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s9
  obtain ⟨c9, m9, g9, l9, _⟩ := VerifiableInference.Desc.K12.Coin.onGu_leaves p
    (H2K.JointK.early_of_planOk p hp) (H2K.JointK.answers_of_planOk p hp) d8 d9 _ _ e9
  have hn := withU_two hM hw
  have hno := withOmega_two hS
  have hsz : d8.st.oracles.size = 4 := by
    have := congrArg Array.size B.mid.shapes
    rw [Array.size_map, Array.size_map, Array.size_append, hn, hno] at this
    exact this
  -- the group
  have hg : d9.st.groups[1]? = d8.st.groups[1]? :=
    g9 1 (by rw [B.mid.groups]; decide) (by rw [B.gU]; decide)
  -- the members' shapes
  have hsh : ∀ o, o < 4 → o ≠ 1 →
      (d9.st.oracles.getD o default).shape = (d8.st.oracles.getD o default).shape := by
    intro o ho h1
    have a := m9 o (by rw [hsz]; exact ho)
      (by rw [B.mask]; intro q; exact h1 (Option.some.inj q).symm)
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    cases h9' : d9.st.oracles[o]? with
    | none =>
      cases h8' : d8.st.oracles[o]? with
      | none => rfl
      | some y =>
        rw [h9', h8'] at a
        cases a
    | some z =>
      cases h8' : d8.st.oracles[o]? with
      | none =>
        rw [h9', h8'] at a
        cases a
      | some y =>
        rw [h9', h8'] at a
        exact congrArg Prod.fst (Option.some.inj a)
  unfold VerifiableInference.Desc.K12.Seat.enter at he
  cases he
  have e8 : pubNear (⟨d8.st, d8.book, d8.roots, 1, .nothing, none⟩ : T12) =
      nearOf (pubBehind Q sentU) 1 := by
    rw [pubNear_of_pub]
    show nearOf (pubSt d8.st) 1 = _
    rw [B.pub]
  rw [← e8]
  unfold pubNear
  show (d9.st.codes, (d9.st.groups[d9.loc.gOmega]?).map _) =
    (d8.st.codes, (d8.st.groups[1]?).map _)
  rw [l9, B.gOmega, c9, hg]
  congr 1
  obtain ⟨G, hG, eG⟩ :
      ∃ G, d8.st.groups[1]? = some G ∧ G.members = #[sentU.size, sentU.size + 1] := by
    have a := B.mid.g1
    cases hq : d8.st.groups[1]? with
    | none => rw [hq] at a; cases a
    | some G =>
      rw [hq] at a
      exact ⟨G, rfl, congrArg PubGroup.members (Option.some.inj a)⟩
  rw [hG]
  show some (pubG G, _) = some (pubG G, _)
  congr 2
  rw [eG, hn]
  refine Array.map_congr_left fun o ho => ?_
  have ho' : o = 2 ∨ o = 3 := by simpa using ho
  rcases ho' with rfl | rfl
  · exact hsh 2 (by decide) (by decide)
  · exact hsh 3 (by decide) (by decide)

/-! ## 4 The state on entry -/

theorem pubNear_stateOfPub (P : PubState × ℕ) : pubNear (stateOfPub P) = nearOf P.1 P.2 := by
  have e := pubOf_stateOfPub P
  have e1 : pubSt (stateOfPub P).st = P.1 := congrArg Prod.fst e
  have e2 : (stateOfPub P).g = P.2 := rfl
  rw [pubNear_of_pub, e1, e2]

section Door
variable {S₀ : Type} (bs : List (Block S₀ Unit)) (s₀ : W → S₀)
  (enter : S₀ → Except String T12) (cols : W → Front X → List OpenedColumn)

/-- `pubOf_doorOf` at `pubNear`: the part that `layFits` reads of the state on entry is N for every
input and whatever precedes the test, if it is N at `fall` and wherever the fold and `enter` return.
-/
theorem pubNear_doorOf (N : Near) (fall : T12) (hf : pubNear fall = N)
    (h : ∀ w fr x t, foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) = .ok x →
      enter x.1 = .ok t → pubNear t = N) (w : W) (fr : Front X) :
    pubNear (doorOf bs s₀ enter cols fall w fr) = N := by
  unfold doorOf
  cases hx : foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) with
  | error _ => exact hf
  | ok x =>
    show pubNear ((enter x.1).toOption.getD fall) = N
    cases ht : enter x.1 with
    | error _ => exact hf
    | ok t => exact h w fr x t hx ht

end Door

/-- `layFits_all` at `pubNear`: one evaluation of `layFitsNear` gives `layFits` at every input and
whatever precedes the test. -/
theorem layFits_allNear (A : ManyJob W X) (N : Near)
    (hP : ∀ (w : W) (fr : Front X), pubNear (A.rec₀ w fr) = N) (h : layFitsNear A N = true) (w : W)
    (fr : Front X) : A.layFits (A.rec₀ w fr) = true := by
  rw [layFits_near, hP, h]

/-- `layFits_atDoor` at `pubNear`. -/
theorem layFits_atDoorNear {S₀ : Type} (bs : List (Block S₀ Unit)) (s₀ : W → S₀)
    (enter : S₀ → Except String T12) (cols : W → Front X → List OpenedColumn) (A : ManyJob W X) (N : Near)
    (fall : T12) (hf : pubNear fall = N) (hA : A.rec₀ = doorOf bs s₀ enter cols fall)
    (h : ∀ w fr x t, foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) = .ok x →
      enter x.1 = .ok t → pubNear t = N)
    (hP : layFitsNear A N = true) (w : W) (fr : Front X) : A.layFits (A.rec₀ w fr) = true :=
  layFits_allNear A N
    (fun w fr => by rw [hA]; exact pubNear_doorOf bs s₀ enter cols N fall hf h w fr) hP w fr

/-- **At the test on G_u: the part that `layFits` reads of the state on entry is the plan's, for
every input and whatever precedes the test.** No hypothesis on the run. The state is `doorOf`'s,
whose fall-back is made from that same term: where the fold or `enter` fails, the equation holds by
that choice. No statement that this state is the verifier's. -/
theorem nearDoor_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubNear (doorOf bs (fun w => first Q.codes (key w))
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask)) cols
      (stateOfPub (pubBehind Q sentU, 0)) w fr) = nearOf (pubBehind Q sentU) 0 :=
  pubNear_doorOf bs _ _ cols _ _ (pubNear_stateOfPub _)
    (fun w _ x t hx ht => near_at_U Q bs hb hS hM sentU hw (key w) _ _ x t hx ht) w fr

/-- **At the test on G_omega: the same**, behind the eight and the test on G_u. At every honest run
this is the fall-back, as long as a part is handed no opened column (see the head's limits). No
statement that this state is the verifier's. -/
theorem nearDoor_Omega (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubNear (doorOf (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
      (fun w => first Q.codes (key w))
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) cols
      (stateOfPub (pubBehind Q sentU, 1)) w fr) = nearOf (pubBehind Q sentU) 1 :=
  pubNear_doorOf _ _ _ cols _ _ (pubNear_stateOfPub _)
    (fun w _ x t hx ht => near_at_Omega Q bs hb hS hM sentU hw p hp (key w) _ _ x t hx ht) w fr

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.has_shape
#print axioms ProofFile.Honest.K12.Light.rowBits_shape
#print axioms ProofFile.Honest.K12.Light.layFits_by
#print axioms ProofFile.Honest.K12.Light.idx_below
#print axioms ProofFile.Honest.K12.Light.all_same
#print axioms ProofFile.Honest.K12.Light.fitsBy_congr
#print axioms ProofFile.Honest.K12.Light.layFits_near
#print axioms ProofFile.Honest.K12.Light.pubNear_of_pub
#print axioms ProofFile.Honest.K12.Light.near_at_U
#print axioms ProofFile.Honest.K12.Light.withU_two
#print axioms ProofFile.Honest.K12.Light.withOmega_two
#print axioms ProofFile.Honest.K12.Light.near_at_Omega
#print axioms ProofFile.Honest.K12.Light.pubNear_stateOfPub
#print axioms ProofFile.Honest.K12.Light.pubNear_doorOf
#print axioms ProofFile.Honest.K12.Light.layFits_allNear
#print axioms ProofFile.Honest.K12.Light.layFits_atDoorNear
#print axioms ProofFile.Honest.K12.Light.nearDoor_U
#print axioms ProofFile.Honest.K12.Light.nearDoor_Omega
#print axioms ProofFile.Honest.K12.Light.Near
#print axioms ProofFile.Honest.K12.Light.pubNear
#print axioms ProofFile.Honest.K12.Light.fitsBy
#print axioms ProofFile.Honest.K12.Light.layFitsNear
#print axioms ProofFile.Honest.K12.Light.nearOf
