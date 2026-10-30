-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamGroups.lean: if the prover's algorithm and the simulator's algorithm
disclose the same rounds and groups, the two runs of the link's protocol disclose the same.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. What an algorithm discloses (shownOf, SpecShift.lean) is its rounds and its
groups (Johnson/LinkSim/AtText/Defs.lean's terms). What the protocol's verifier reads is given by
tree and position (wanted, OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean). Between the two stands the schedule of
the proximity test (sched): which round sends a stage's tree, which round's challenges open it, and
the tree's depth. Both statements hold for all parameters.
  Spec.sameOfShown, sameOfShown    suppose the plan has a first stage and WantTie holds. If linkAll
               at data X and coins C, and simAll at data X' and coins C', disclose the same (equal
               shownOf), then they satisfy SameAt (SeamOfOut.lean).
  Spec.showsOfShown, showsOfShown    the same, down to the two runs. Under the same premises and
               equal shownOf, at the challenges of a verifier message ρ, the run of the prover's
               strategy and the run of the simulator's strategy against ρ disclose the same (Shows,
               Johnson/LinkSim/SpecForm.lean).

How it fits. showsOfShown is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean):
Exact.lean uses it to pass from the two algorithms to the two runs of the protocol.

The other names (namespace OnBytes.LinkSim.Seam).
  sched rest cur o r    the schedule, as a list of (the round that sent the tree, the round whose
               positions open it, the tree's depth), by the recursion of bodyAll
               (Johnson/Prover/Link/BodyAll.lean). A tree of depth d has 2^d positions, and a
               sampled position is read modulo 2^d.
  grpOf D TR e   one group: the column of the tree of round e.1 in the list TR, at the positions
               that round e.2.1 sampled.
  gs_body, gs_link    the groups are the trees' columns at these lists: of bodyAll, of linkAll.
  simAll_tr, simAll_gs    the simulator's algorithm has the trees and the groups of the prover's
               algorithm at the data 0.
  WantTie ds sch Ds    a public premise: every position that the challenges ask of a tree of the
               prover is in the schedule sch.
  wantOkL, wantTie_of_ok    a Boolean test on the rounds' description that gives WantTie at every
               list of challenges.

Limits.
- WantTie is a premise here, and so is that the plan has a first stage.
- The simulator's strategy is nextOfOut of its algorithm at the challenges of ρ. It looks at all
  challenges from its first message on.

Notes. The test that gives WantTie is evaluated in SeamAtFull.lean, not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamOfOut
import Johnson.LinkSim.AtText.SpecShift
import Johnson.Prover.Link.BodyGroups

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.LinkSim OnBytes.LinkSim.AtText
open OnBytes.Flat (linkProtocolOfRoundData)
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO)
open TypedOracleCompiler.Run.PQ (RD SOf drawnSL wanted wantedL treeSh)

/-- The order of the test: (the round that sent the tree, the round whose positions open it, the
tree's depth). o: the number of the stage's first round. r: the round that sent the stage's tree. -/
def sched : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → ℕ → List (ℕ × ℕ × ℕ)
  | [], cur, o, r => [(r, o + 1, (sgOf cur).C.a)]
  | next :: rest, cur, o, r =>
    (r, o + 2 + ((sgOf cur).h + (sgOf cur).g), (sgOf cur).C.a) ::
      sched rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (o + (1 + ((sgOf cur).h + (sgOf cur).g)))

/-- One group: the column of the tree of round e.1 in TR, at the positions that round e.2.1
sampled. -/
def grpOf (D : ℕ → Fmt.Drawn) (TR : List (ℕ → List UInt64)) (e : ℕ × ℕ × ℕ) :
    List (ℕ × List UInt64) :=
  groupAt e.2.2 (D e.2.1).poss ((TR[e.1]?).getD fun _ => [])

/-- **The stages' groups are the trees' columns at the lists of the sampled positions.** TR: a list
of the rounds' columns that holds bodyAll's from place o on. -/
theorem gs_body (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (TR : List (ℕ → List UInt64)) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64) (r : ℕ),
      (∀ i, TR[o + i]? = (bodyAll p K rest j cur l o t P col D).tr[i]?) →
      (TR[r]?).getD (fun _ => []) = col →
      (bodyAll p K rest j cur l o t P col D).gs = (sched rest cur o r).map (grpOf D TR)
  | [], _, cur, _, o, _, _, col, r, _, hc => by
      show [groupAt (sgOf cur).C.a (D (o + 1)).poss col] =
        [groupAt (sgOf cur).C.a (D (o + 1)).poss ((TR[r]?).getD fun _ => [])]
      rw [hc]
  | next :: rest, j, cur, l, o, t, P, col, r, h, hc => by
      have ih := gs_body p K D TR rest (j + 1) next (l.drop (cur.k + 3))
        (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
        (sNext K rest.isEmpty j cur next o P (rowOf t) D)
        (sCol K rest.isEmpty j cur next o P (rowOf t) D)
        (o + (1 + ((sgOf cur).h + (sgOf cur).g)))
        (fun i => by
          have e : o + ((sgOf cur).h + (sgOf cur).g) + 3 + i =
              o + (((sgOf cur).h + (sgOf cur).g) + 3 + i) := by omega
          rw [e, h, tr_later])
        (by rw [h, tr_seed]; rfl)
      show [groupAt (sgOf cur).C.a (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss col] ++
          (bodyAll p K rest (j + 1) next (l.drop (cur.k + 3))
            (o + ((sgOf cur).h + (sgOf cur).g) + 3)
            (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
            (sNext K rest.isEmpty j cur next o P (rowOf t) D)
            (sCol K rest.isEmpty j cur next o P (rowOf t) D) D).gs =
        groupAt (sgOf cur).C.a (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss
            ((TR[r]?).getD fun _ => []) ::
          (sched rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)
            (o + (1 + ((sgOf cur).h + (sgOf cur).g)))).map (grpOf D TR)
      rw [ih, hc]
      rfl

section
variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

/-- **The link's groups**: the stored columns, then the columns of its own trees in the schedule's
order. -/
theorem gs_link (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).gs =
      lStored P S X D ++ (sched rest first 6 1).map (grpOf D (linkAll P S t X C D).tr) := by
  have hg : (linkAll P S t X C D).gs = lStored P S X D ++
      (bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
        (lPS P S X C D) (lCol P S X C D) D).gs := by
    unfold linkAll
    rw [hs]
  rw [hg]
  refine congrArg _ (gs_body (p12Of P) C.body D _ rest 0 first _ 6 _ _ _ 1 (fun i => ?_) ?_)
  · rw [linkAll_tr P S t X C D first rest hs,
      List.getElem?_append_right (by show 6 ≤ 6 + i; omega)]
    show _[6 + i - 6]? = _
    rw [Nat.add_sub_cancel_left]
  · rw [linkAll_tr P S t X C D first rest hs]
    rfl

/-- The simulator's algorithm has the trees of the prover's algorithm at the data 0. -/
theorem simAll_tr : (simAll P S t X C D).tr = (linkAll P S t (zeroIn X) C D).tr := by
  unfold simAll
  split <;> rfl

/-- The simulator's algorithm has the groups of the prover's algorithm at the data 0. -/
theorem simAll_gs : (simAll P S t X C D).gs = (linkAll P S t (zeroIn X) C D).gs := by
  unfold simAll
  split <;> rfl

end

/-- A public premise: every position that the challenges ask of a tree of the prover is in the
schedule sch. -/
def WantTie (ds : List RD) (sch : List (ℕ × ℕ × ℕ)) (Ds : List Fmt.Drawn) : Prop :=
  ∀ nx ∈ wanted ds Ds, ∀ j k, seatOf ds nx.1 = some (j, k) →
    ∃ e ∈ sch, e.1 = j ∧ nx.2 ∈ Fmt.listOf ((drawsOf Ds e.2.1).poss.map (· % 2 ^ e.2.2))

/-- A Boolean test: each tree that round number i opens is in sch with its seat's round, i and
its depth. An opened number that has no shape or no seat passes. That is harmless: of a number
without a shape the challenges ask nothing (wantedL), and WantTie, like SameCols and SameAt, speaks
only of numbers that have a seat. -/
def wantOkL (all : List RD) (sch : List (ℕ × ℕ × ℕ)) : ℕ → List RD → Bool
  | _, [] => true
  | i, d :: ds =>
    (d.opens.all fun n =>
      match treeSh all n, seatOf all n with
      | some s, some jk => sch.contains (jk.1, i, s.a)
      | _, _ => true) && wantOkL all sch (i + 1) ds

/-- The induction behind wantTie_of_ok, from round i on. -/
theorem wantTieL (all : List RD) (sch : List (ℕ × ℕ × ℕ)) : ∀ (i : ℕ) (ds : List RD)
    (Ds : List Fmt.Drawn), wantOkL all sch i ds = true → ∀ nx ∈ wantedL all ds Ds, ∀ j k,
    seatOf all nx.1 = some (j, k) →
    ∃ e ∈ sch, e.1 = j ∧ i ≤ e.2.1 ∧ ∃ D, Ds[e.2.1 - i]? = some D ∧
      nx.2 ∈ Fmt.listOf (D.poss.map (· % 2 ^ e.2.2))
  | _, [], _, _, _, h, _, _, _ => by simp [wantedL] at h
  | _, _ :: _, [], _, _, h, _, _, _ => by simp [wantedL] at h
  | i, d :: ds, D :: Ds, hok, nx, h, j, k, hs => by
      unfold wantedL at h
      unfold wantOkL at hok
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
      rcases List.mem_append.1 h with h | h
      · obtain ⟨n, hn, h⟩ := List.mem_flatMap.1 h
        have hn' := List.all_eq_true.1 h1 n hn
        split at h
        · cases h
        · rename_i s hsh
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
          have hs2 : seatOf all n = some (j, k) := hs
          simp only [hsh, hs2] at hn'
          exact ⟨(j, i, s.a), by simpa using hn', rfl, le_refl _, D, by simp, hx⟩
      · obtain ⟨e, he, e1, e2, D', hD, hx⟩ := wantTieL all sch (i + 1) ds Ds h2 nx h j k hs
        refine ⟨e, he, e1, by omega, D', ?_, hx⟩
        have e3 : e.2.1 - i = (e.2.1 - (i + 1)) + 1 := by omega
        rw [e3]
        simpa using hD

/-- The test gives WantTie, at every list of challenges. -/
theorem wantTie_of_ok (ds : List RD) (sch : List (ℕ × ℕ × ℕ)) (Ds : List Fmt.Drawn)
    (h : wantOkL ds sch 0 ds = true) : WantTie ds sch Ds := by
  intro nx hnx j k hs
  obtain ⟨e, he, e1, -, D, hD, hx⟩ := wantTieL ds sch 0 ds Ds h nx hnx j k hs
  refine ⟨e, he, e1, ?_⟩
  have e2 : drawsOf Ds e.2.1 = D := by
    show Ds.getD e.2.1 _ = D
    rw [List.getD_eq_getElem?_getD, ← Nat.sub_zero e.2.1, hD]
    rfl
  rw [e2]
  exact hx

/-- Statement only; proved as sameOfShown below. **Equal disclosures of the two algorithms give
SameAt**, under a first stage and WantTie. -/
def Spec.sameOfShown : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X X' : LIn S) (C C' : LCoins) (ds : List RD)
    (Ds : List Fmt.Drawn) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
    (p12Of P).nums.stages = first :: rest → WantTie ds (sched rest first 6 1) Ds →
    shownOf (linkAll P S t X C (drawsOf Ds)) = shownOf (simAll P S t X' C' (drawsOf Ds)) →
    SameAt ds (linkAll P S t X C (drawsOf Ds)) (simAll P S t X' C' (drawsOf Ds)) Ds

theorem sameOfShown : Spec.sameOfShown := by
  intro P S t X X' C C' ds Ds first rest hs hw h
  have hrs : (linkAll P S t X C (drawsOf Ds)).rs = (simAll P S t X' C' (drawsOf Ds)).rs :=
    congrArg Prod.fst h
  have hgs : (linkAll P S t X C (drawsOf Ds)).gs = (simAll P S t X' C' (drawsOf Ds)).gs :=
    congrArg Prod.snd h
  refine ⟨fun i _ => by unfold valsAt; rw [hrs], fun nx hnx j k hseat => ?_⟩
  obtain ⟨e, he, rfl, hx⟩ := hw nx hnx j k hseat
  rw [simAll_gs, gs_link P S t X C _ first rest hs, gs_link P S t (zeroIn X') C' _ first rest hs,
    ← simAll_tr] at hgs
  have hm := (List.append_inj hgs (by unfold lStored; rw [List.length_map, List.length_map])).2
  have hg := List.map_inj_left.1 hm e he
  exact (Prod.mk.inj (List.map_inj_left.1 hg nx.2 hx)).2

/-- Statement only; proved as showsOfShown below. The same, down to the two runs: they disclose the
same (Shows). The simulator's strategy is made of its algorithm at the challenges of ρ. -/
def Spec.showsOfShown : Prop :=
  ∀ (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) (Xi : Type) (dec : Xi → View → Bool) (x : Xi)
    (P : P15) (S : Sz) (t : ℕ) (X X' : LIn S) (C C' : LCoins) (first : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (ρ : Rho (_root_.Run.Twin.up (SOf K ds))),
    (p12Of P).nums.stages = first :: rest →
    WantTie ds (sched rest first 6 1) (drawnSL K ds ρ.2) →
    shownOf (linkAll P S t X C (drawsOf (drawnSL K ds ρ.2))) =
      shownOf (simAll P S t X' C' (drawsOf (drawnSL K ds ρ.2))) →
    Shows (linkProtocolOfRoundData K ds a xs dec) x ((stratOf K ds (linkNext P S t X C)).run ρ).1
      ((stratOf K ds (nextOfOut (simAll P S t X' C' (drawsOf (drawnSL K ds ρ.2))))).run ρ).1

theorem showsOfShown : Spec.showsOfShown :=
  fun K ds a xs Xi dec x P S t X X' C C' first rest ρ hs hw h =>
    showsOfOut K ds a xs Xi dec x _ _ _ _ ρ (readsOut_linkNext P S t X C _)
      (readsOut_nextOfOut _ _) (sameOfShown P S t X X' C C' ds _ first rest hs hw h)

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.gs_link
#print axioms OnBytes.LinkSim.Seam.wantTie_of_ok
#print axioms OnBytes.LinkSim.Seam.sameOfShown
#print axioms OnBytes.LinkSim.Seam.showsOfShown
