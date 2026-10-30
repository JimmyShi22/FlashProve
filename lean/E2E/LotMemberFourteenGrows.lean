-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotMemberFourteenGrows.lean: the five debts at member 14 of the key file's first chain ("rng.0.rows"),
at the thread `laid₁` (E2E/KeyRest.lean), general in the filling L, the halves and the tables.

  `two_of`: a list of two, by its members.
  `grows_of_rows`: on sentences and states alone: where the ground's adding has laid the two lookups' rows onto
    the ranges' group, which was empty, "rows 0", "rows 1" and "srow 1" in front give "grows" behind, at one witness.
  `open14`: these three items are open at border 14: by evaluation of the table.
  `grows_behind`: so the item that row 14 makes anew holds behind the step.
  `exchange14`, `plays14`, `behind14`, `rides14`, `accepted14`: the five, from the thread alone.
  `five14`: the five asked from `ThrS`, at every letter Said and every fall.

By calls of the library but for `grows_of_rows`: `plays_quiet₁` (E2E/KeyPlaysQuiet.lean), `behind₁` (E2E/KeyBehind.lean),
`exchange_of_anew₁` (E2E/KeyOwedAgain.lean), `ridesPast₁` (E2E/KeyRides.lean), `accepted_quiet₁` (E2E/KeyQuietFirst.lean) at
`first_of_sourced` (E2E/KeyShapeFullSourced.lean).

Limits.
- `Thr … 14`, the premise inside all five, IS MET BY NOTHING YET: nothing here, and nothing that this file stands on, shows that
  the thread stands at border 14 at any run. It hangs on the chain's start (`Enters₁`) and on the debts at members 0 to 13.
  Where the thread stands nowhere the five are empty.
- `MembersS` asks `SaidNext` at 14 beside the five: it is not among them and not here.
- FOUR OF THE FIVE ARE CALLS of the library. The new content is `grows_of_rows` and `grows_behind` alone.
- The written sizes alone: in scope, at a sourced description; `accepted14` rests on the library's run of the guards on shapes
  at the written codes.
- `ReadsL` of the filling's reading is a premise here.
- E2E/KeyRowsLater.lean imports E2E/KeyBehind.lean, that E2E/KeyLaid.lean, that E2E/KeyProver.lean: no
  name of that file is read here.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyRowsLater
import E2E.KeyShapeFullSourced

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Block OpenedColumn Strs Wit)
open VerifiableInference.Desc.Key (Xi FirstState PlainState KItem KRead Source LaterPlaces core₁ shape₁_iff
  groupB_some rowHolds_congr start₁)
open Johnson.RunOne.KeyRows1 (meaning₁At plan₁ readers₁ book₁ slots₁ withD RowsGround c_14_parts grp_eq ReadsL)
open AtPublicFiles.KeyThread (KeyFill laid₁ D one₀ rowsFirst anew behind₁ exchange_of_anew₁ ridesPast₁ plays_quiet₁
  seat_behind)
open AtPublicFiles.AtFiles (KeySourced KeyNamed keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- A list of two, by its members. -/
theorem two_of {α : Type} (l : List α) (a b : α) (h : l.length = 2) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) : l = [a, b] := by
  cases l with
  | nil =>
    have h' : 0 = 2 := h
    omega
  | cons x t =>
    cases t with
    | nil =>
      have h' : 1 = 2 := h
      omega
    | cons y u =>
      cases u with
      | nil =>
        obtain rfl : x = a := Option.some.inj h0
        obtain rfl : y = b := Option.some.inj h1
        rfl
      | cons z v =>
        have h' : v.length + 3 = 2 := h
        omega

/-- **The rows on the ranges' group, behind "rng.0.rows".** On sentences and states alone. -/
theorem grows_of_rows {Cells M : Type} (one : OnBytes.Params.OneTime) (R : KRead Cells M) (p : Xi)
    (s : FirstState) (d' : PlainState) (y y' : Strs) (w : Wit Cells Unit M) (H : RowsGround s d')
    (h2 : s.base.rows.length = 2)
    (hc : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 14 s = true)
    (r0 : (meaning₁At one R).rows 0 (p, s) y w) (r1 : (meaning₁At one R).rows 1 (p, s) y w)
    (sr : (meaning₁At one R).srow 1 (p, s) y w) :
    (meaning₁At one R).grows (p, withD s d') y' w := by
  obtain ⟨-, -, -, -, -, f, -, -⟩ := c_14_parts one s hc
  obtain ⟨g₀, G₀, hg₀, hG₀, -, hz⟩ := groupB_some (readers₁ one) s false 0 f
  have eg := grp_eq one s g₀ hg₀
  subst eg
  obtain ⟨Gr', hGr', hrows, -, -⟩ := H.group G₀ hG₀
  obtain ⟨rs0, e0, n0, q0⟩ := r0
  obtain ⟨rs1, e1, -, q1⟩ := r1
  obtain ⟨o, x, ho, hx, -, -, qs⟩ := sr
  have hG0 : G₀.rows.toList = [] :=
    List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact hz)
  have hl : s.base.rows = [rs0, rs1] := two_of _ _ _ h2 e0 e1
  rw [hG0, List.nil_append, hl] at hrows
  have hx' : d'.st.oracles[o]? = some x := by
    rw [H.oracles]
    exact hx
  refine ⟨s.grp, Gr', o, x, hg₀, hGr', ho, hx', fun h0 => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · have e : Gr'.rows.toList = [] :=
      List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
    rw [e] at hrows
    cases rs0 with
    | nil => exact n0 rfl
    | cons a t => cases hrows
  · rw [hrows] at hr
    obtain ⟨l, hl', hr'⟩ := List.mem_flatten.1 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    rcases hl' with rfl | rfl
    · exact (rowHolds_congr _ H.tables _ r).2 (q0 r hr')
    · exact (rowHolds_congr _ H.tables _ r).2 (q1 r hr')
  · exact (rowHolds_congr _ H.tables _ r).2 (qs r hr)

/-- The three items that the row spends are open at border 14. -/
theorem open14 : KItem.rows 0 ∈ fwdOpen (start₁ 2) rowsFirst 14 ∧
    KItem.rows 1 ∈ fwdOpen (start₁ 2) rowsFirst 14 ∧
    KItem.srow 1 ∈ fwdOpen (start₁ 2) rowsFirst 14 := by decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : PublicFiles}

/-- **What row 14 makes anew holds behind the step.** -/
theorem grows_behind (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    ∀ blk, (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[14]? = some blk → ∀ k s m E ds y cols s',
      Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 14 k s m E → drawsFit blk.rounds ds = true →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Items (anew 14) k s' y.2 (E.add y.1) := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  obtain ⟨-, -, hk⟩ := behind₁ Xs N Pl L w₀ rc x hs scope 14 (by decide) blk hblk k s m E ds y cols
    s' hT hd hS
  obtain ⟨d', rfl, H, h2⟩ : ∃ d', s' = withD s d' ∧ RowsGround s d' ∧ s.base.rows.length = 2 := hk
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hc : core₁ (plan₁ (one₀ Xs)) (readers₁ (one₀ Xs)) (book₁ (one₀ Xs)) 2 (slots₁ (one₀ Xs)) 14
      s = true := ((shape₁_iff _ _ _ _ _ _ _).1 hT.2.2.1.1).2
  intro ds' i hi
  obtain rfl : i = KItem.grows := List.mem_singleton.1 hi
  have r0 := hT.2.2.2.1 (ds ++ ds') (KItem.rows 0) open14.1
  have r1 := hT.2.2.2.1 (ds ++ ds') (KItem.rows 1) open14.2.1
  have sr := hT.2.2.2.1 (ds ++ ds') (KItem.srow 1) open14.2.2
  rw [seat_behind (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) hT.2.1 hy, (play_mid _ _ _ _ _ hy).1,
    play_heard _ _ _ _ _ hy, List.append_assoc]
  exact grows_of_rows (one₀ Xs) L.R _ s d' ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs E)
    ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs (E.add y.1)) _ H h2 hc r0 r1 sr

/-- **It plays.** -/
theorem plays14 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    Plays (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 14 :=
  plays_quiet₁ scope hs.named (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl 14 (by decide)

/-- **Behind its yes.** -/
theorem behind14 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    Behind (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 14 :=
  behind₁ Xs N Pl L w₀ rc x hs scope 14 (by decide)

/-- **The exchange.** -/
theorem exchange14 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hG : ReadsL L.base.h₁) : Exchange (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 14 :=
  exchange_of_anew₁ Xs N Pl L w₀ rc x hs scope hG 14 (by decide)
    (grows_behind Xs N Pl L w₀ rc x hs scope)

/-- **What rides past.** -/
theorem rides14 (hG : ReadsL L.base.h₁) : RidesPast (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 14 :=
  ridesPast₁ Xs N Pl L w₀ rc x hG 14 (by decide)

/-- **It is accepted**, at every fall. -/
theorem accepted14 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Accepted (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) fall 14 := by
  obtain ⟨-, -, -, hlen, hT0, -, hyes, -⟩ :=
    AtPublicFiles.AtFiles.Full.first_of_sourced hs scope (fun _ _ _ _ => true)
  obtain ⟨blk, hblk, hr, -⟩ := AtPublicFiles.KeyThread.quiet_of_rows (keyFileDescription Xs N Pl).first.blocksInOrder
    AtPublicFiles.KeyBook.fullFirst (AtPublicFiles.KeyBook.places_named scope hs.named).1
    (fun b hb => ((planOk_all hs.named.plan).1 b hb).2) (b := 14) (by decide)
  exact AtPublicFiles.AtFiles.accepted_quiet₁ Xs N Pl AtPublicFiles.AtFiles.CF (fun _ _ _ _ => true)
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) rfl (AtPublicFiles.AtFiles.Full.public_first_sourced hs scope)
    (n := 19) (Nat.le_of_eq hlen.symm) (by rw [hT0]; exact hyes)
    (fun _ w _ s₀ _ hb => ⟨_, hb⟩) (fun _ _ _ _ _ _ _ => rfl) 14 (by decide) blk hblk hr

/-- **The five, asked from `ThrS`**, at every letter for what is said of the run and every fall. -/
theorem five14 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hG : ReadsL L.base.h₁)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    PlaysS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said 14 ∧
      BehindS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said 14 ∧
      ExchangeS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said 14 ∧
      RidesPastS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said 14 ∧
      AcceptedS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) Said fall 14 :=
  ⟨playsS_of _ _ (plays14 Xs N Pl L w₀ rc x hs scope),
    behindS_of _ _ (behind14 Xs N Pl L w₀ rc x hs scope),
    exchangeS_of _ _ (exchange14 Xs N Pl L w₀ rc x hs scope hG),
    ridesPastS_of _ _ (rides14 Xs N Pl L w₀ rc x hG),
    acceptedS_of _ _ (accepted14 Xs N Pl L w₀ rc x hs scope fall)⟩

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.two_of
#print axioms AtPublicFiles.FirstH.Lots.grows_of_rows
#print axioms AtPublicFiles.FirstH.Lots.open14
#print axioms AtPublicFiles.FirstH.Lots.grows_behind
#print axioms AtPublicFiles.FirstH.Lots.plays14
#print axioms AtPublicFiles.FirstH.Lots.behind14
#print axioms AtPublicFiles.FirstH.Lots.exchange14
#print axioms AtPublicFiles.FirstH.Lots.rides14
#print axioms AtPublicFiles.FirstH.Lots.accepted14
#print axioms AtPublicFiles.FirstH.Lots.five14
