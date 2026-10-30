-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/TestForms.lean: THE PROXIMITY TEST (the kind K12's own block, proximityTestKind guardedProximityTestParts
p, Johnson/Desc/K12/JoinGuarded.lean) ON THE ROWS' MAKES (Forms.lean): WHERE THE BLOCK ACCEPTS, ON
WHATEVER ROUNDS AND COLUMNS, THE MAKES BEHIND ARE A WRITTEN FUNCTION OF THE PLAN, THE SHAPE IN FRONT
AND THE MAKES IN FRONT. General laws; nothing is evaluated. It goes beside another house's function
 (Johnson/Desc/K12/Honest/Shape/TestCore.lean: batThin, foldThin, switchThin, stagesThin)
and is proved part by part after the make of the laws "these values stay" (TestKeeps.lean),
over the library's own foldJ_form, switchUnfolds, stagesFrom_ok, k12_ok.

What the test does to the makes.
  the batching: the group under test loses its open rows.
  a fold: a new group, empty; and, if the first fold's mask had not come, one new message without a
    sample row.
  a switch with the batching behind it: two new messages: the stage's, with ONE sample row, and the
    next mask's, with none; the fold's new group takes rows and loses them at once.
  the base case: nothing.

  1 `forms_begun`, `forms_withRows`, `forms_joined`, `forms_ledgerShut`, `forms_admitted`,
    `forms_spent`, `forms_withGroup`: the statement's effects. `modAt_append_first`, `units_places`,
    `othersOf_size` (the library's H2K.Out.othersOf_size once more): tools.
  2 `formS`, **`form_mk`**: the make of the program's sample row (Send.form): kind sample; a single
    entry at each place of the pad; a term on the main table and one on the mask table where the
    message has such rows. It hangs on the codes, the message's shape and number and the number of
    the seed's coordinates.
  3 `batMk` | `bat_mk`, `foldMk` | `fold_mk`, `base_mk`, `switchMk` | **`switch_mk`**.
  4 `stagesMk` | `stages_mk`, **`testMk`** | **`k12_mk`**: proximityTestKind guardedProximityTestParts p accepts from t0 to tE ⊢
    testMk p ‹the core's shape of t0› t0.g t0.mask (formsOf t0.st) = some (formsOf tE.st).

Limits. From an accept alone: that the block accepts is not shown. Premises: the masks come early
and a sample has one answer (the block's own test on the plan asks both). A RETURN OF testMk IS NO
SIGN OF AN ACCEPT: nothing holds the core's shape and the makes together (the new message's number
is read off the makes; at a group outside the makes' list the makes come back unchanged, in
silence); at the last stage stagesMk asks nothing. Nothing on what a row is worth. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.K12.Honest.Shape.TestKeeps
import Johnson.Desc.First.Shape.SendForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open ProofFile.Honest.Sh (ThinSh thinSh batThin foldThin switchThin stagesThin bat_thin fold_thin
  switch_thin bat_form)
open H2K.Out (like_P5 foldJ_form spendP_form)
open H2K.FoldLaw (bind_ok got_ok)
open H2K.JointK H2K.Sw

/-! ## 1 The statement's effects -/

theorem forms_begun (S : Statement) (g : Nat) (G : Group) :
    formsOf (begun S g G) =
      { formsOf S with groups := modAt (formsOf S).groups g fun _ => [] } := by
  have e := forms_closeLedgers G.members.toList S
  unfold formsOf at e ⊢
  unfold begun
  dsimp only
  rw [FormsSh.mk.injEq] at e
  rw [map_modify _ g _ grpMk (fun _ => []) (fun _ => rfl), e.1, e.2]

theorem forms_withRows (g : Nat) : ∀ (l : List OnBytes.Row) (S : Statement),
    formsOf (withRows S g l) =
      { formsOf S with groups := modAt (formsOf S).groups g (· ++ l.map rowMk) }
  | [], S => by
    show formsOf S = _
    have : modAt (formsOf S).groups g (· ++ ([] : List OnBytes.Row).map rowMk) =
        (formsOf S).groups := by
      unfold modAt
      simp
    rw [this]
  | r :: l, S => by
    show formsOf (withRows (withRow S g r) g l) = _
    rw [forms_withRows g l]
    have e : formsOf (withRow S g r) =
        { formsOf S with groups := modAt (formsOf S).groups g (· ++ [rowMk r]) } := by
      unfold formsOf withRow
      dsimp only
      rw [map_modify _ g _ grpMk (· ++ [rowMk r]) (fun G => by
        unfold grpMk
        simp)]
    rw [e]
    dsimp only
    rw [modAt_modAt]
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem forms_joined (S : Statement) (g o : Nat) (kept : Bool) (G : Group) :
    formsOf (OnBytes.Slice.withMessageInGroup S g o kept G) = formsOf S := by
  unfold formsOf OnBytes.Slice.withMessageInGroup
  dsimp only
  rw [orc_same, grp_same]
  all_goals (intro _; rfl)

theorem forms_ledgerShut (S : Statement) (T : SwitchTarget) (o : Nat) :
    formsOf (ledgerShut S T o) = formsOf S := by
  unfold ledgerShut
  split
  · exact forms_closeLedgers _ _
  · rfl

theorem forms_admitted (S : Statement) (o : Nat) (s : OracleShape) (places : List PadPlace)
    (rows : Array OnBytes.Row) :
    formsOf (admitted S o s places rows) =
      { formsOf S with oracles := modAt (formsOf S).oracles o fun _ => rows.toList.map rowMk } := by
  unfold formsOf admitted
  dsimp only
  rw [map_modify _ o _ orcMk (fun _ => rows.toList.map rowMk) (fun _ => rfl)]

theorem forms_spent (S : Statement) (o : Nat) :
    formsOf { S with oracles := S.oracles.modify o fun x => { x with spentAsMask := true } } =
      formsOf S := by
  unfold formsOf
  dsimp only
  rw [orc_same]
  intro _
  rfl

theorem forms_withGroup (S : Statement) (code maskCode : Nat) :
    formsOf (Ground.withGroup S code maskCode) =
      { formsOf S with groups := (formsOf S).groups ++ [[]] } := by
  unfold formsOf Ground.withGroup
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- Laying at the first of the places that were added. -/
theorem modAt_append_first {α : Type} (l : List α) (a : α) (r : List α) (f : α → α) :
    modAt (l ++ a :: r) l.length f = l ++ f a :: r := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  by_cases e : j = l.length
  · subst e
    simp
  · rw [if_neg e]
    by_cases e2 : j < l.length
    · rw [List.getElem_append_left e2, List.getElem_append_left e2]
    · have e3 : l.length ≤ j := by omega
      rw [List.getElem_append_right e3, List.getElem_append_right e3]
      obtain ⟨k, hk⟩ : ∃ k, j - l.length = k + 1 := ⟨j - l.length - 1, by omega⟩
      simp only [hk, List.getElem_cons_succ]

/-! ## 2 The program's sample row -/

/-- Send.form's make. zlen: the number of the seed's coordinates. -/
def formS (codes : Codes) (s : OracleShape) (o zlen : Nat) (places : List PadPlace) : RowMk :=
  { kind := .sample
    terms :=
      (if (Send.cube codes s).hasMain then
        [⟨o, .main, ⟨min (Send.cube codes s).mainBits zlen, [], 0, 0⟩⟩] else []) ++
      (if (Send.cube codes s).hasMask then
        [⟨o, .mask, ⟨min (Send.cube codes s).maskBits zlen, [], 0, 0⟩⟩] else [])
    units := places.map fun p => ⟨o, p.part, p.index⟩
    runs := [], forms := [] }

theorem units_places (o : Nat) (c : PadPlace → E) : ∀ (l : List PadPlace) (r : OnBytes.Row),
    rowMk (l.foldl (fun r p => r.addUnit o p.part p.index (c p)) r) =
      { rowMk r with units := (rowMk r).units ++ l.map fun p => ⟨o, p.part, p.index⟩ }
  | [], r => by simp
  | p :: l, r => by
    rw [List.foldl_cons, units_places o c l]
    unfold OnBytes.Row.addUnit rowMk
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl

theorem form_mk {codes : Codes} {s : OracleShape} {o : Nat} {seed : SampleSeed} {i : Nat}
    {r : OnBytes.Row} {places : List PadPlace} (hp : Send.pad codes s = some places)
    (h : Send.form codes s o seed i = some r) : rowMk r = formS codes s o seed.z.length places := by
  unfold Send.form at h
  simp only [hp, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
  obtain rfl := Option.some.inj h
  have hu := units_places o (fun p =>
    subE (if p.answer == i then mulE seed.beta p.basis else zeroE)
      ((if p.part == .main then
          Tensor.eq (seed.z.take (Send.cube codes s).mainBits)
            (Send.front seed.z (Send.cube codes s) (Send.cube codes s).mainBits false)
        else Tensor.eq (seed.z.take (Send.cube codes s).maskBits)
          (Send.front seed.z (Send.cube codes s) (Send.cube codes s).maskBits true)).entry
        p.index)) places { kind := .sample }
  revert hu
  generalize List.foldl _ ({ kind := .sample } : OnBytes.Row) places = r₀
  intro hu
  unfold formS
  by_cases h1 : (Send.cube codes s).hasMain = true <;>
    by_cases h2 : (Send.cube codes s).hasMask = true
  · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, rowMk_add, rowMk_add, hu, tensorSh_eq,
      tensorSh_eq, List.length_take, List.length_take]
    rfl
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, rowMk_add, hu, tensorSh_eq, List.length_take]
    rfl
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, rowMk_add, hu, tensorSh_eq, List.length_take]
    rfl
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, hu]
    rfl

/-! ## 3 The parts -/

/-- The batching. g: the group under test. -/
def batMk (g : Nat) (F : FormsSh) : FormsSh :=
  { F with groups := modAt F.groups g fun _ => [] }

theorem bat_mk (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) : formsOf t1.st = batMk t.g (formsOf t.st) := by
  obtain ⟨G, row, L, m, _, rfl⟩ := bat_form p cut t t1 rs gs h
  exact forms_begun t.st t.g G

/-- A fold. mask: the number of the message that holds its mask, if it has come. -/
def foldMk (mask : Option Nat) (F : FormsSh) : FormsSh :=
  { groups := F.groups ++ [[]]
    oracles := if mask.isSome then F.oracles else F.oracles ++ [[]] }

theorem fold_mk (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    formsOf t1.st = foldMk t.mask (formsOf t.st) := by
  obtain ⟨row, L, c, nn, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  show formsOf (Ground.withGroup _ nn.1 nn.2) = _
  rw [forms_withGroup, forms_spent]
  unfold foldMk
  rcases hcase with ⟨hm, rfl⟩ | ⟨hm, ids, hr, _⟩
  · rw [hm]
    rfl
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    rw [hm]
    show ({ formsOf (stSent t.st _) with groups := (formsOf (stSent t.st _)).groups ++ [[]] } :
      FormsSh) = _
    rw [forms_stSent]
    rfl

theorem base_mk (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    formsOf tE.st = formsOf t.st := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    unfold formsOf
    dsimp only
    rw [orc_same]
    intro _
    rfl
  · cases h

/-- A switch with the batching behind it. a: the thin shape in front of the switch. It is written
for one answer to a sample (the 1 in switchTargetStage … 1). -/
def switchMk (p : P12) (j : Nat) (nxt : Fmt.M1.Stage) (a : ThinSh) (F : FormsSh) :
    Option FormsSh :=
  match a.pass, stageAt p (j + 1) nxt with
  | .single _ gp, some nx =>
    (Send.pad a.core.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).map
      fun places =>
        { groups := modAt F.groups gp fun _ => []
          oracles := F.oracles ++
            [[formS a.core.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape
                F.oracles.length
                (Send.cube a.core.st.codes
                  (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).bits places], []] }
  | _, _ => none

theorem othersOf_size (last : Bool) (nx : IoppStage) : (othersOf last nx).size = 1 := by
  unfold othersOf
  split <;> rfl

theorem switch_mk (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    switchMk p j nxt (thinSh t1) (formsOf t1.st) = some (formsOf t3.st) := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, h1''⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := H2K.Out.switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    -- the sample row's make
    have hz : (D.z (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) t1.st).length =
        (Send.cube t1.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).bits := by
      have hs := congrArg List.length hd.seed
      rw [List.length_drop] at hs
      unfold Taken.z
      rw [List.length_take]
      simp only [List.length_cons, List.length_nil] at hs
      omega
    have hmk : rowMk D.sample =
        formS t1.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape
          t1.st.oracles.size
          (Send.cube t1.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).bits
          D.places := by
      unfold Taken.sample
      rw [rowMk_target, form_mk hd.pad hd.form]
      show formS _ _ _ (D.z _ t1.st).length _ = _
      rw [hz]
    have hlenO : (formsOf t1.st).oracles.length = t1.st.oracles.size := by
      unfold formsOf
      simp
    -- the statement behind
    have hF : formsOf t3.st =
        { groups := modAt (formsOf t1.st).groups gp fun _ => []
          oracles := (formsOf t1.st).oracles ++ [[rowMk D.sample], []] } := by
      rw [hd.st, forms_begun]
      unfold Taken.stR
      rw [forms_withRows]
      dsimp only
      rw [modAt_modAt]
      unfold Taken.stJ
      rw [forms_joined, forms_ledgerShut]
      unfold Taken.stA
      rw [forms_admitted, forms_stSent]
      dsimp only
      have hs2 : (OnBytes.Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
          (othersOf last nx)).size = 2 := by
        unfold OnBytes.Slice.sentOf
        rw [Array.size_append, othersOf_size]
        rfl
      rw [hs2, ← hlenO]
      show FormsSh.mk _ (modAt ((formsOf t1.st).oracles ++ [] :: [[]]) _ _) = _
      rw [modAt_append_first]
      rfl
    unfold switchMk
    show (match ProofFile.Honest.Sh.thinPass t1.pass, stageAt p (j + 1) nxt with
      | .single _ gp, some nx => _
      | _, _ => none) = _
    rw [e1, e2]
    show (Send.pad t1.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).map _ = _
    rw [hd.pad, Option.map_some, hF, hmk, hlenO]
    rfl
  · cases h1'

/-! ## 4 The stages; the whole test -/

def stagesMk (p : P12) : List Fmt.M1.Stage → Nat → Fmt.M1.Stage → ThinSh → FormsSh →
    Option FormsSh
  | [], _, _, _, F => some F
  | nxt :: rest, j, cur, a, F =>
    (foldThin p j cur a).bind fun a1 => (switchThin p j nxt rest.isEmpty a1).bind fun a3 =>
      (switchMk p j nxt a1 (foldMk a.mask F)).bind fun F3 => stagesMk p rest (j + 1) nxt a3 F3

theorem stages_mk (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (la : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE →
      stagesMk p rest j cur (thinSh t) (formsOf t.st) = some (formsOf tE.st)
  | [], j, cur, la, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    show some (formsOf t.st) = _
    rw [base_mk p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1]
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := fold_thin p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
    have m1 := fold_mk p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switch_thin p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3)
    have m2 := switch_mk p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3)
    have m4 := stages_mk p he ha rest (j + 1) nxt _ t3 tE _ _ f5
    show (foldThin p j cur (thinSh t)).bind _ = _
    rw [k1, Option.bind_some, k2, Option.bind_some]
    show (switchMk p j nxt (thinSh t1) (foldMk t.mask (formsOf t.st))).bind _ = _
    rw [← m1, m2, Option.bind_some]
    exact m4

/-- **The proximity test on the rows' makes.** c: the core's shape in front. g: the group under
test. mask: the number of the message that holds the first stage's mask, if it has come. -/
def testMk (p : P12) (c : CoreSh) (g : Nat) (mask : Option Nat) (F : FormsSh) : Option FormsSh :=
  match p.nums.stages with
  | first :: rest =>
    (batThin p ⟨c, g, .nothing, mask⟩).bind fun a1 => stagesMk p rest 0 first a1 (batMk g F)
  | [] => none

/-- **Where the test's block accepts, the test on the makes returns the makes behind.** -/
theorem k12_mk (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    testMk p (coreSh ⟨t0.st, t0.book, t0.roots⟩) t0.g t0.mask (formsOf t0.st) =
      some (formsOf tE.st) := by
  have e : (⟨coreSh ⟨t0.st, t0.book, t0.roots⟩, t0.g, .nothing, t0.mask⟩ : ThinSh) = thinSh t0 := by
    unfold thinSh
    rw [ProofFile.Honest.Sh.k12_nothing p t0 tE rs gs h]
    rfl
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  unfold testMk
  rw [hs, e]
  show (batThin p (thinSh tF)).bind _ = _
  rw [bat_thin p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat), Option.bind_some,
    ← bat_mk p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)]
  exact stages_mk p he ha rest 0 first _ _ tE _ _ hst

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.bat_mk
#print axioms VerifiableInference.Desc.First.Shape.fold_mk
#print axioms VerifiableInference.Desc.First.Shape.base_mk
#print axioms VerifiableInference.Desc.First.Shape.switch_mk
#print axioms VerifiableInference.Desc.First.Shape.stages_mk
#print axioms VerifiableInference.Desc.First.Shape.k12_mk
#print axioms VerifiableInference.Desc.First.Shape.forms_begun
#print axioms VerifiableInference.Desc.First.Shape.forms_withRows
#print axioms VerifiableInference.Desc.First.Shape.forms_joined
#print axioms VerifiableInference.Desc.First.Shape.forms_ledgerShut
#print axioms VerifiableInference.Desc.First.Shape.forms_admitted
#print axioms VerifiableInference.Desc.First.Shape.forms_spent
#print axioms VerifiableInference.Desc.First.Shape.forms_withGroup
#print axioms VerifiableInference.Desc.First.Shape.modAt_append_first
#print axioms VerifiableInference.Desc.First.Shape.form_mk
#print axioms VerifiableInference.Desc.First.Shape.formS
#print axioms VerifiableInference.Desc.First.Shape.units_places
#print axioms VerifiableInference.Desc.First.Shape.batMk
#print axioms VerifiableInference.Desc.First.Shape.foldMk
#print axioms VerifiableInference.Desc.First.Shape.switchMk
#print axioms VerifiableInference.Desc.First.Shape.othersOf_size
#print axioms VerifiableInference.Desc.First.Shape.stagesMk
#print axioms VerifiableInference.Desc.First.Shape.testMk
