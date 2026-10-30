-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFoldPlan.lean: THE FORM's HALF AT A FOLD, THE PLAN's SHARE: at every place
of a proximity test whose first fold does not send its own mask, the declared rounds that the frame
deals to each stage's fold pass foldCut (Johnson/Prover/Link/FormFold.lean); and a fold is owed no
group of columns.

Main names.
  quietDecl, layOpens_quiet   layOpens (Johnson/Desc/K12/TestEntries.lean) along rounds that open
  nothing. layOpens_entries, entries_of_nums   the declared rounds' entries are those of
    Fmt.M1.laterRounds (Fmt/M1Plan.lean) at the place's own numbers, behind "BAT"'s.
  foldCut_made     foldCut at "FOLD epsilon" and k times "FOLD round", as they are laid.
  later_cuts, foldCuts_of_nums   THE STATEMENT: foldCuts at the place's declared rounds.
  nOpen_foldCut, grpF_nil   the frame's cut of the groups for a fold is empty.

Limits. The premise is N.ownMask = false, a field of the place's numbers. It is NOT P12.early, which
guardedProximityTestParts asks on the plan: at the link's place the two are made of two fields of the planner's
record (Johnson/Desc/Link/LinkDesc.lean, numsOf): nothing here ties them. Nothing on a record or a
view.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFold
import Johnson.Desc.K12.Law.JointK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (Stage laterRounds rEps rTwo rSeed rCs rBat)

/-- A round that opens nothing, as layOpens lays it where no fold sends its own mask. -/
def quietDecl (r : Fmt.Round) : Fmt.DeclaredRound := ⟨r.entry, [], []⟩

/-- **layOpens along rounds that open nothing.** -/
theorem layOpens_quiet : ∀ (A B : List Fmt.Round) (seen : Bool)
    (L : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    (∀ r ∈ A, r.opens.isEmpty = true) → H2U.layOpens false seen (A ++ B) L = some ds →
    ∃ seen' ds', H2U.layOpens false seen' B L = some ds' ∧ ds = A.map quietDecl ++ ds'
  | [], _, seen, _, ds, _, h => ⟨seen, ds, h, rfl⟩
  | r :: A, B, seen, L, ds, hA, h => by
    have hr : r.opens.isEmpty = true := hA r (List.mem_cons_self)
    rw [List.cons_append] at h
    simp only [H2U.layOpens, Bool.false_and, hr, if_true, Bool.false_eq_true, if_false] at h
    cases hq : H2U.layOpens false (seen || r.entry.name == "FOLD epsilon") (A ++ B) L with
    | none => simp [hq] at h
    | some a =>
      simp only [hq, Option.map_some, Option.some.injEq] at h
      obtain ⟨seen', ds', h1, h2⟩ := layOpens_quiet A B _ L a
        (fun x hx => hA x (List.mem_cons_of_mem _ hx)) hq
      refine ⟨seen', ds', h1, ?_⟩
      rw [← h, h2]
      rfl

/-- The entries are the rounds'. -/
theorem layOpens_entries : ∀ (R : List Fmt.Round) (seen : Bool)
    (L : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    H2U.layOpens false seen R L = some ds → ds.map (·.entry) = R.map (·.entry)
  | [], _, [], ds, h => by
    cases h
    rfl
  | [], _, _ :: _, _, h => by cases h
  | r :: R, seen, L, ds, h => by
    simp only [H2U.layOpens, Bool.false_and, Bool.false_eq_true, if_false] at h
    split at h
    · cases hq : H2U.layOpens false (seen || r.entry.name == "FOLD epsilon") R L with
      | none => simp [hq] at h
      | some a =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        rw [← h, List.map_cons, List.map_cons, layOpens_entries R _ L a hq]
    · split at h
      · rename_i x t
        split at h
        · simp at h
        · cases hq : H2U.layOpens false (seen || r.entry.name == "FOLD epsilon") R t with
          | none => simp [hq] at h
          | some a =>
            simp only [hq, Option.map_some, Option.some.injEq] at h
            rw [← h, List.map_cons, List.map_cons, layOpens_entries R _ t a hq]
      · simp at h

/-- **The declared rounds' entries at a place whose first fold sends no mask of its own.** -/
theorem entries_of_nums (N : H2U.TestNums) (s next : Stage) (rest : List Stage)
    (ds : List Fmt.DeclaredRound) (ho : N.ownMask = false) (hs : N.stages = s :: next :: rest)
    (h : H2U.roundsOfNums N = some ds) :
    ds.map (·.entry) = { rBat.entry with rows := N.rows } ::
      (laterRounds N.work 0 0 s (next :: rest)).map (·.entry) := by
  unfold H2U.roundsOfNums at h
  rw [hs, ho] at h
  exact layOpens_entries _ _ _ _ h

/-- foldCut at the rounds as they are laid. -/
theorem foldCut_made (k : Nat) :
    foldCut k ((rEps "FOLD epsilon" :: List.replicate k (rTwo "FOLD round")).map quietDecl) =
      true := by
  have e1 : elemEntry "FOLD epsilon" 1 (rEps "FOLD epsilon").entry = true := by decide
  have e2 : elemEntry "FOLD round" 2 (rTwo "FOLD round").entry = true := by decide
  rw [List.map_cons, List.map_replicate]
  unfold foldCut
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_replicate, List.all_cons,
    List.all_eq_true]
  refine ⟨⟨⟨e1, trivial⟩, fun d hd => ?_⟩, ⟨rfl, rfl⟩, fun d hd => ?_⟩
  · rw [List.eq_of_mem_replicate hd]
    exact e2
  · rw [List.eq_of_mem_replicate hd]
    exact ⟨rfl, rfl⟩

/-- **Stage by stage.** -/
theorem later_cuts (work : Nat) : ∀ (rest : List Stage) (tree W : Nat) (old : Stage) (seen : Bool)
    (L : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    H2U.layOpens false seen (laterRounds work tree W old rest) L = some ds →
    foldCuts old rest ds = true
  | [], _, _, _, _, _, _, _ => rfl
  | new :: rest, tree, W, old, seen, L, ds, h => by
    have e : laterRounds work tree W old (new :: rest) =
        ((rEps "FOLD epsilon" :: List.replicate old.k (rTwo "FOLD round")) ++ [rSeed new]) ++
          (rCs work old tree W :: laterRounds work (tree + 1) (Fmt.M1.wMid new) new rest) := by
      rw [laterRounds]
      simp
    rw [e] at h
    obtain ⟨seen', ds', h1, h2⟩ := layOpens_quiet _ _ seen L ds (fun r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · rcases List.mem_cons.1 hr with rfl | hr
        · rfl
        · rw [List.eq_of_mem_replicate hr]
          rfl
      · rw [List.mem_singleton.1 hr]
        rfl) h
    have hc : (rCs work old tree W).opens.isEmpty = false := rfl
    simp only [H2U.layOpens, Bool.false_and, Bool.false_eq_true, if_false, hc] at h1
    cases L with
    | nil => simp at h1
    | cons x t =>
      simp only at h1
      split at h1
      · simp at h1
      · cases hq : H2U.layOpens false (seen' || (rCs work old tree W).entry.name == "FOLD epsilon")
            (laterRounds work (tree + 1) (Fmt.M1.wMid new) new rest) t with
        | none => simp [hq] at h1
        | some a =>
          simp only [hq, Option.map_some, Option.some.injEq] at h1
          subst h1
          have ih := later_cuts work rest _ _ new _ t a hq
          have lA : ((rEps "FOLD epsilon" :: List.replicate old.k (rTwo "FOLD round")).map
              quietDecl).length = 1 + old.k := by
            rw [List.length_map, List.length_cons, List.length_replicate]
            omega
          rw [h2, List.map_append, List.append_assoc]
          unfold foldCuts
          rw [Bool.and_eq_true]
          constructor
          · rw [List.take_left' lA]
            exact foldCut_made old.k
          · rw [show old.k + 3 = (1 + old.k) + 2 by omega, ← List.drop_drop,
              List.drop_left' lA]
            exact ih

/-- **AT EVERY PLACE WHOSE FIRST FOLD SENDS NO MASK OF ITS OWN EVERY FOLD's CUT PASSES foldCut.** -/
theorem foldCuts_of_nums (N : H2U.TestNums) (s : Stage) (rest : List Stage) (d0 : Fmt.DeclaredRound)
    (ds : List Fmt.DeclaredRound) (ho : N.ownMask = false) (hs : N.stages = s :: rest)
    (h : H2U.roundsOfNums N = some (d0 :: ds)) : foldCuts s rest ds = true := by
  cases rest with
  | nil => rfl
  | cons next rest =>
    unfold H2U.roundsOfNums at h
    rw [hs, ho] at h
    obtain ⟨seen', ds', h1, h2⟩ := layOpens_quiet
      [{ rBat with entry := { rBat.entry with rows := N.rows } }] _ false _ _
      (fun r hr => by rw [List.mem_singleton.1 hr]; rfl) h
    obtain ⟨_, rfl⟩ := List.cons.inj h2
    exact later_cuts N.work _ _ _ s _ _ _ h1

/-- A fold's cut opens nothing. -/
theorem nOpen_foldCut {k : Nat} {cut : List Fmt.DeclaredRound} (h : foldCut k cut = true) :
    H2K.JointK.nOpen cut = 0 := by
  have hq : (cut.all fun d => d.stored.isEmpty && d.opens.isEmpty) = true := by
    cases cut with
    | nil => cases h
    | cons dE dR =>
      unfold foldCut at h
      simp only [Bool.and_eq_true] at h
      exact h.2
  have gen : ∀ (l : List Fmt.DeclaredRound) (a : Nat),
      (l.all fun d => d.stored.isEmpty && d.opens.isEmpty) = true →
      l.foldl (fun n r => n + r.stored.length + r.opens.length) a = a := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons d l ih =>
      intro a hl
      rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, List.isEmpty_iff,
        List.isEmpty_iff] at hl
      rw [List.foldl_cons, hl.1.1, hl.1.2]
      exact ih a hl.2
  exact gen cut 0 hq

/-- **The frame's cut of the groups for a fold is empty.** -/
theorem grpF_nil (l : Laid) (k : Nat) (gs : H2K.JointK.Gs)
    (h : foldCut k (H2K.JointK.cutF l k) = true) : H2K.JointK.grpF l k gs = [] := by
  unfold H2K.JointK.grpF
  rw [nOpen_foldCut h]
  rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.layOpens_quiet
#print axioms Johnson.Prover.Link.layOpens_entries
#print axioms Johnson.Prover.Link.entries_of_nums
#print axioms Johnson.Prover.Link.foldCut_made
#print axioms Johnson.Prover.Link.later_cuts
#print axioms Johnson.Prover.Link.foldCuts_of_nums
#print axioms Johnson.Prover.Link.nOpen_foldCut
#print axioms Johnson.Prover.Link.grpF_nil
