-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.BookAppends
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.MadeRounds
import Johnson.Desc.K12.SeatLaws
import Johnson.G.RoundsOfPlan
import OnBytes.Params.Fit.LayPasses
import Johnson.Desc.K12.Law.PlacesFull
/-
Johnson/Desc/K12/Law/RootsAcross.lean: ACROSS THE PROXIMITY TEST's BLOCK THE RECORD's COUNT OF ROOTS RISES BY WHAT THE BLOCK's OWN ROUNDS DECLARE: one root a switch. For the row book_numbers_first_chain's second law («the first chain has received as many roots as its declared rounds hold»): K12's share. FIRST ARM (the first fold's mask has come; the place does not send its own). BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  send_one          WHATEVER THE CODES: the planner's two passes lay a switch's sending (the target and the one mask that rides with it) INTO ONE TREE: the mask for the next fold has no main row and the target's class of leaves; the mask for the base case has the target's own code and class
  laidFrom_len      so what the test's sendings lay, from stage j on, has as many trees as there are stages behind (the place names a pair of codes for each)
  roots_across      early · one answer · the mask has come · a yes of the decision from t0 to tE ⇒ ∃ first rest A: the stages are first :: rest · laidFrom t0.st.codes t0.book.trees.size (sendsFrom p 0 rest) = some A · tE.roots = t0.roots + A.shapes.length
  roots_switches    the block's test on the plan (early and one answer follow from it: early_of_planOk | answers_of_planOk) · the mask has come · a yes ⇒ tE.roots + 1 = t0.roots + p.nums.stages.length: ONE ROOT A SWITCH
  lay_same · later_roots · declared_of_plan    ON THE PLAN: the block's test on the plan · ownMask = false ⇒ rootsOf (the block's declared rounds) + 1 = the number of stages: of the declared rounds' own make (Johnson/Desc/K12/TestEntries.lean; Fmt/M1Plan.lean's laterRounds: "SEND seed" alone declares a root)
  roots_declared    the block's test on the plan · ownMask = false · the mask has come · a yes ⇒ tE.roots = t0.roots + rootsOf (proximityTestKind guardedProximityTestParts p).rounds: NO TEST THAT NO RUNNING TEXT ASKS
  atFinish_roots    the same at the first chain's finish, at the chain's own record: a yes of (atFinish p).decide from s to s' · where the chain stands at its finish the mask is noted ⇒ s'.roots = s.roots + rootsOf (atFinish p).rounds (by Seat.atFinish_ok)
  own_declares_more «ownMask = false» is spent: a closed place said to send its own first mask declares one root more (decide +kernel; the place is a run's print made into a term)
CALLED: k12_appends · size_of_shapes (Johnson/Desc/K12/Coin/BookAppends.lean) · k12_out3 (Johnson/Desc/K12/Law/OutK3.lean: the roots rise as the trees do) · idx_len (Top.lean) · k12_rounds (Johnson/Desc/K12/FrameLaws.lean) · rounds_top (MadeRounds.lean) · layTrees_size (OnBytes/Params/Fit/LayPasses.lean).
NOT HERE: the own mask's arm (there the first fold receives a tree too, and its round declares it) · «the mask has come» is a premise, as in k12_appends.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Out H2K.Sw
open Johnson.G.OfPlan (rootsOf)

theorem send_one (codes : Codes) (nx : IoppStage) (last : Bool) :
    (Params.laidOf codes (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
      (othersOf last nx))).1.size = 1 := by
  have h2 : (2 ^ nx.k == 0) = false := by
    have := Nat.two_pow_pos nx.k
    simp
  cases last <;>
    simp [Params.laidOf, Params.layPass, Params.layStep, Slice.sentOf, othersOf, switchTargetStage,
      foldMaskNotice, baseMaskNotice, ioppFoldShape, List.range_succ, h2]

theorem laidFrom_len (codes : Codes) (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j b : ℕ) (A : Laid),
    j + 1 + rest.length ≤ p.idx.length → laidFrom codes b (sendsFrom p j rest) = some A →
    A.shapes.length = rest.length
  | [], _, _, A, _, h => by
    simp only [sendsFrom, laidFrom] at h
    cases h
    rfl
  | nxt :: rest, j, b, A, hl, h => by
    simp only [sendsFrom, laidFrom] at h
    obtain ⟨lay, hlay, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    have hj : j + 1 < p.idx.length := by
      simp only [List.length_cons] at hl
      omega
    have hs : stageAt p (j + 1) nxt =
        some { code := p.idx[j + 1].1, maskCode := p.idx[j + 1].2, k := nxt.k, h := nxt.h } := by
      unfold stageAt
      rw [List.getElem?_eq_getElem hj]
      rfl
    unfold sendAt at hlay
    rw [hs] at hlay
    have e1 := Params.layTrees_size hlay
    rw [send_one] at e1
    have ih := laidFrom_len codes p rest (j + 1) _ R
      (by simp only [List.length_cons] at hl; omega) hR
    simp only [List.length_append, Array.length_toList, List.length_cons, e1, ih]
    omega


theorem roots_across (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t0.mask.isSome = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ first rest A, p.nums.stages = first :: rest ∧
      laidFrom t0.st.codes t0.book.trees.size (sendsFrom p 0 rest) = some A ∧
      tE.roots = t0.roots + A.shapes.length := by
  obtain ⟨first, rest, hs, A, hA, _, es⟩ := k12_appends p he ha t0 tE rs gs hm h
  have sz := size_of_shapes es
  have o := (k12_out3 p he ha t0 tE rs gs h).rootsTrees
  exact ⟨first, rest, A, hs, hA, by omega⟩

/-- One root a switch. -/
theorem roots_switches (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t0.mask.isSome = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    tE.roots + 1 = t0.roots + p.nums.stages.length := by
  obtain ⟨first, rest, A, hs, hA, e⟩ :=
    roots_across p (early_of_planOk p hp) (answers_of_planOk p hp) t0 tE rs gs hm h
  have hi := idx_len p hp
  have hl := laidFrom_len t0.st.codes p rest 0 _ A (by rw [hi, hs, List.length_cons]; omega) hA
  rw [hs, List.length_cons]
  omega

/-- Where the test does not send its own first mask the laid rounds have the toy's rounds' entries. -/
theorem lay_same : ∀ (rs : List Fmt.Round) (seen : Bool)
    (l : List (List (Fmt.Shape × Fmt.TreeSource))) (out : List Fmt.DeclaredRound),
    H2U.layOpens false seen rs l = some out → out.map (·.entry) = rs.map (·.entry)
  | [], _, [], out, h => by
    cases h
    rfl
  | [], _, _ :: _, _, h => by cases h
  | r :: rs, seen, l, out, h => by
    unfold H2U.layOpens at h
    dsimp only at h
    split at h
    · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [List.map_cons, lay_same rs _ l o' h1]
      simp
    · split at h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          simp only [List.map_cons, lay_same rs _ _ o' h1]
          simp
      · cases h

/-- The toy's rounds from a stage on declare one root for each stage behind. -/
theorem later_roots (work : ℕ) : ∀ (rest : List Fmt.M1.Stage) (tree W : ℕ) (old : Fmt.M1.Stage),
    ((Fmt.M1.laterRounds work tree W old rest).map (·.entry.roots)).sum = rest.length
  | [], _, _, _ => rfl
  | new :: rest, tree, W, old => by
    simp only [Fmt.M1.laterRounds, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.map_replicate, List.sum_replicate,
      later_roots work rest (tree + 1) _ new, List.length_cons]
    show 0 + 0 + old.k • 0 + (1 + (0 + 0)) + rest.length = rest.length + 1
    simp
    omega

/-- ON THE PLAN: where the test does not send its own first mask its declared rounds hold one
root for each stage but the first. -/
theorem declared_of_plan (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) :
    rootsOf (proximityTestKind guardedProximityTestParts p : Blk').rounds + 1 = p.nums.stages.length := by
  have hr := k12_rounds (Cl := Unit) guardedProximityTestParts p hp
  obtain ⟨s, next, rest, R, hs, hR, e⟩ := H2K.Made.rounds_top p.nums _ hr
  rw [ho] at hR
  have h1 := lay_same _ _ _ R hR
  have h2 : R.map (·.entry.roots) =
      (Fmt.M1.laterRounds p.nums.work 0 0 s (next :: rest)).map (·.entry.roots) := by
    have := congrArg (List.map (·.roots)) h1
    simpa [List.map_map, Function.comp_def] using this
  rw [e, hs]
  unfold rootsOf
  rw [List.map_cons, List.sum_cons, h2, later_roots]
  show 0 + (next :: rest).length + 1 = (s :: next :: rest).length
  simp

/-- ACROSS THE BLOCK THE ROOTS RISE BY WHAT ITS OWN ROUNDS DECLARE. -/
theorem roots_declared (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : t0.mask.isSome = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    tE.roots = t0.roots + rootsOf (proximityTestKind guardedProximityTestParts p : Blk').rounds := by
  have e := roots_switches p hp t0 tE rs gs hm h
  have e2 := declared_of_plan p hp ho
  omega

/-- AT THE FIRST CHAIN's FINISH, at the chain's own record. -/
theorem atFinish_roots (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (s s' : First.S)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : ∀ fo, s.here = .fin fo → fo.mask.isSome = true)
    (h : (atFinish p).decide s rs gs = .ok s') :
    s'.roots = s.roots + rootsOf (atFinish p).rounds := by
  obtain ⟨fo, t', hfo, _, _, hd, rfl⟩ := Seat.atFinish_ok p s s' rs gs h
  exact roots_declared p hp ho _ t' rs gs (hm fo hfo) hd

/-- «ownMask = false» is spent: the full size's place of the first chain's last test, SAID TO SEND
ITS OWN FIRST MASK, declares one root more. -/
theorem own_declares_more :
    rootsOf (proximityTestKind guardedProximityTestParts { H2K.Member.piLFull with
                                     nums := { H2K.Member.piLFull.nums with ownMask := true } } : Blk').rounds =
      H2K.Member.piLFull.nums.stages.length := by
  decide +kernel

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.send_one
#print axioms VerifiableInference.Desc.K12.Coin.laidFrom_len
#print axioms VerifiableInference.Desc.K12.Coin.roots_across
#print axioms VerifiableInference.Desc.K12.Coin.roots_switches
#print axioms VerifiableInference.Desc.K12.Coin.lay_same
#print axioms VerifiableInference.Desc.K12.Coin.later_roots
#print axioms VerifiableInference.Desc.K12.Coin.declared_of_plan
#print axioms VerifiableInference.Desc.K12.Coin.roots_declared
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_roots
#print axioms VerifiableInference.Desc.K12.Coin.own_declares_more
