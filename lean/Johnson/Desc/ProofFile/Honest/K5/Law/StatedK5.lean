-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/StatedK5.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5): WHAT THE MAKER OF THE BOOK LAYS FOR THE PARTS OF THE KIND's MEMBER, BY NAME AND COUNT, IS
WHAT THE PARTS OF THE KIND's ROW STATE THAT THEY SPEND: AT EVERY PLAN THAT PASSES THE VERIFIER's OWN
TEST ON THE PLAN. Two texts that were written apart are held against each other: the maker reads the
verifier's member by its rounds' names and bytes and names no half (Honest/BookOf.lean,
Honest/BookEntries.lean, of other authors); the row is made of the plan's shapes
(Honest/K5/RowOf.lean). On public data alone. Two definitions with code; twenty-one statements with
their proofs.

  stated p          A SECOND TEXT, HELD TO THE FIRST BY stated_is: what the maker's partWants
                    (BookEntries.lean) lays for a part that is no merge, read by name and count
  stated_is         ((partWants row idx false p j t).1.map Want.entry).map Ahead.named = stated p,
                    at every row that bears the mask row's name, every idx, j and t: by cases
  spendsOf a s      what the row's part at a shape and its number states
  partAt_spends     (partAt a chalOf J s).spends = spendsOf a s: by unfolding
  pr e              an entry's name and number of scalars: scalarsIn's arithmetic (BookOf.lean) on
                    an entry; rounds_pr, rounds_names tie it to the member's rounds
  pr_entry · one_stated · own_rounds · end_rounds · foldl_shift · entries_pr · sum_stated
                    one part: a lone round; a sumcheck with ends
  headRun_sum · entries_names · unitLen_sum · cons_unit   the maker's cut, one unit at a time
  walk              along the script, by induction on its stages
  cutOfNames_K5     at this kind the cut is the list of units
  k5_stated         CONDITIONAL: **(planParts blk).map stated = (k5Row Z).map (·.spends)**
  names_in          every entry of the script bears one of six names
  k5_plain_names    CONDITIONAL: **no round of the member is named "SEND seed" or "FOLD epsilon"**
  k5_no_seed · k5_no_fold   its two halves, each spelled as the laws on the maker spell their
                    premise

The premises of k5_stated. hpl: the member stands at the seat's place · hr: its rounds are the
plan's (rounds p, Johnson/Desc/First/Att/K5AttentionKind.lean) · hx: the plan's numbers are the seat's · hok:
planOk p = true. All four are spent. hok is spent at one arm: where the number of a sumcheck's end
values is 0 the maker lays the run "sum" alone, while the row's part states a run "ends" of the
count 0 beside it: planOk's test on each sumcheck of the script (shapeOk) bars that.

What for. A test on the book at the kind's places (rowNamed, Honest/Small/RowNamed.lean) asks that
the book's entries with a part's address, by name and count, are the runs that the part states. This
file ties the runs that the parts state to what the maker's text lays for that part. k5_plain_names
pays, at this kind, the premise on names of laws on the maker, other authors' and ours.

Kin. For other kinds: Honest/K3/RowCut.lean, Honest/K6/Cut.lean, of other authors.

Two names of this file's table stand for the declarations of the same spelling in ProofFile.Honest.Small
(Honest/Small/WantsStated.lean; one line `export`) and are no declarations here: `stated`,
`stated_is`.

Limits. Conditional. NOTHING IS SAID OF A BOOK HERE: that the entries of a book that the maker
returns, at a part's address, are what partWants lays for that part is not proved here; nor that the
kind's parts are no merges in the caller's list; nor that no other entry and no row of the book's
tables stands at these addresses. That a member with these rounds stands in a chain is a premise.
The maker reads names: a round under another name is cut otherwise. No module under the library's
folder ThirdParty/ lies in its import closure. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookEntries
import Johnson.Desc.ProofFile.Honest.Small.WantsStated
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Part (MaskedSum.Var MaskedSum.Ends MaskedSum.Call MaskedSum.entries
  MaskedSum.entry MaskedSum.ownSlots MaskedSum.shapeOk)
open VerifiableInference.Desc.First.Att.P (Par rounds Stage script entriesOf planOk)
open H2K5.Honest (PartShape shapes shapesOf Chal)

export ProofFile.Honest.Small (stated stated_is)

/-! ## 1 What K5's parts state -/

/-- What the part at a shape and its number states that it spends. -/
def spendsOf (a : Place) (s : PartShape × Nat) : List (String × Due) :=
  match s.1 with
  | .sum k => (nameOf a s.2 "sum", ⟨0, ownRun k⟩) :: endRuns (nameOf a s.2 "ends") k.ends
  | .one 0 => []
  | .one (n + 1) => [(nameOf a s.2 "scalars", ⟨0, n + 1⟩)]

theorem partAt_spends {W' : Type} (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ s : PartShape × Nat, (partAt a chalOf J s).spends = spendsOf a s
  | (.sum _, _) => rfl
  | (.one 0, _) => rfl
  | (.one (_ + 1), _) => rfl

/-! ## 2 The plan's entries, as the maker reads them -/

/-- An entry's name and number of scalars. -/
def pr (e : Fmt.Entry) : String × Nat := (e.name, (e.msg - 32 * e.roots - 24 * e.answers) / 24)

theorem pr_entry (nm : String) (sent drawn nz : Nat) :
    pr (MaskedSum.entry nm sent drawn nz) = (nm, sent) := by
  unfold pr MaskedSum.entry
  simp

theorem rounds_pr (p : Par) :
    ((rounds p).map fun r => (r.entry.name, scalarsIn r)) =
      (entriesOf 0 (script p.own)).map pr := by
  unfold rounds
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show ((if e.drawE == 0 then e else { e with work := p.work }).name, scalarsIn _) = pr e
  unfold scalarsIn pr
  by_cases h : (e.drawE == 0) = true <;> simp [h]

theorem rounds_names (p : Par) :
    ((rounds p).map fun r => r.entry.name) = (entriesOf 0 (script p.own)).map (·.name) := by
  unfold rounds
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show (if e.drawE == 0 then e else { e with work := p.work }).name = e.name
  by_cases h : (e.drawE == 0) = true <;> simp [h]

/-! ## 3 One part -/

/-- A lone round under a name that is neither the frame's nor a sumcheck's first. -/
theorem one_stated (a : Place) (j : Nat) (nm : String) (h1 : frameNames.contains nm = false)
    (h2 : (nm == "PSC epsilon") = false) :
    ∀ lead, stated ⟨⟨a, j⟩, [(nm, lead)]⟩ = spendsOf a (.one lead, j)
  | 0 => by simp [stated, PartAt.ownScalars, spendsOf]
  | n + 1 => by
    have h1' : nm ∉ frameNames := fun hm => by
      rw [List.contains_iff_mem.2 hm] at h1
      cases h1
    simp [stated, PartAt.ownScalars, PartAt.isSum, spendsOf, nameOf, h1', h2]

theorem own_rounds : ∀ (vs : List MaskedSum.Var) (acc : Nat),
    (vs.map fun v => ("PSC round", v.d - 1)).foldl
      (fun n (r : String × Nat) => if frameNames.contains r.1 then n else n + r.2) acc =
      vs.foldl (fun n v => n + (v.d - 1)) acc
  | [], _ => rfl
  | v :: vs, acc => by
    have h : frameNames.contains "PSC round" = false := by decide
    simp only [List.map_cons, List.foldl_cons, h, Bool.false_eq_true, if_false]
    exact own_rounds vs _

theorem end_rounds : ∀ (vs : List MaskedSum.Var) (acc : Nat),
    (vs.map fun v => ("PSC round", v.d - 1)).foldl
      (fun n (r : String × Nat) => if r.1 == "PSC values" then n + r.2 else n) acc = acc
  | [], _ => rfl
  | v :: vs, acc => by
    have h : ("PSC round" == "PSC values") = false := by decide
    simp only [List.map_cons, List.foldl_cons, h, Bool.false_eq_true, if_false]
    exact end_rounds vs _

theorem foldl_shift : ∀ (vs : List MaskedSum.Var) (c b : Nat),
    vs.foldl (fun n v => n + (v.d - 1)) (c + b) = c + vs.foldl (fun n v => n + (v.d - 1)) b
  | [], _, _ => rfl
  | v :: vs, c, b => by
    simp only [List.foldl_cons]
    rw [Nat.add_assoc]
    exact foldl_shift vs c _

/-- A sumcheck's entries, as the maker reads them. -/
theorem entries_pr (lead : Nat) (vs : List MaskedSum.Var) (e : MaskedSum.Ends) :
    (MaskedSum.entries ⟨lead, vs, some e⟩).map pr =
      ("PSC epsilon", lead + 1) :: ((vs.map fun v => ("PSC round", v.d - 1)) ++
        [("PSC Y", e.dY), ("PSC values", e.n)]) := by
  simp [MaskedSum.entries, pr_entry, List.map_map, Function.comp_def]

/-- A sumcheck with ends, of which there is at least one. -/
theorem sum_stated (a : Place) (j lead : Nat) (vs : List MaskedSum.Var) (e : MaskedSum.Ends)
    (he : 1 ≤ e.n) :
    stated ⟨⟨a, j⟩, (MaskedSum.entries ⟨lead, vs, some e⟩).map pr⟩ =
      spendsOf a (.sum ⟨lead, vs, some e⟩, j) := by
  rw [entries_pr]
  have f1 : frameNames.contains "PSC epsilon" = false := by decide
  have f2 : frameNames.contains "PSC Y" = false := by decide
  have f3 : frameNames.contains "PSC values" = false := by decide
  have g1 : ("PSC epsilon" == "PSC values") = false := by decide
  have g2 : ("PSC Y" == "PSC values") = false := by decide
  have hO : (⟨⟨a, j⟩, ("PSC epsilon", lead + 1) :: ((vs.map fun v => ("PSC round", v.d - 1)) ++
      [("PSC Y", e.dY), ("PSC values", e.n)])⟩ : PartAt).ownScalars =
      lead + vs.foldl (fun n v => n + (v.d - 1)) 1 + e.dY + e.n := by
    simp only [PartAt.ownScalars, List.foldl_cons, List.foldl_append, List.foldl_nil, f1, f2, f3,
      Bool.false_eq_true, if_false, own_rounds, Nat.zero_add]
    rw [foldl_shift]
  have hE : (⟨⟨a, j⟩, ("PSC epsilon", lead + 1) :: ((vs.map fun v => ("PSC round", v.d - 1)) ++
      [("PSC Y", e.dY), ("PSC values", e.n)])⟩ : PartAt).endScalars = e.n := by
    simp only [PartAt.endScalars, List.foldl_cons, List.foldl_append, List.foldl_nil, g1, g2,
      Bool.false_eq_true, if_false, end_rounds, beq_self_eq_true, if_true, Nat.zero_add]
  have hS : (⟨⟨a, j⟩, ("PSC epsilon", lead + 1) :: ((vs.map fun v => ("PSC round", v.d - 1)) ++
      [("PSC Y", e.dY), ("PSC values", e.n)])⟩ : PartAt).isSum = true := by
    simp [PartAt.isSum]
  have hR : ownRun ⟨lead, vs, some e⟩ = lead + vs.foldl (fun n v => n + (v.d - 1)) 1 + e.dY := by
    simp [ownRun, MaskedSum.Call.all, MaskedSum.ownSlots, List.foldl_append, MaskedSum.Var.d]
    omega
  unfold stated
  rw [hO, hE, hS]
  have n0 : (lead + vs.foldl (fun n v => n + (v.d - 1)) 1 + e.dY + e.n == 0) = false := by
    simp
    omega
  have n1 : (e.n == 0) = false := by
    simp
    omega
  simp only [n0, n1, Bool.not_true, Bool.false_eq_true, if_false]
  show _ = (nameOf a j "sum", (⟨0, ownRun ⟨lead, vs, some e⟩⟩ : Due)) ::
    endRuns (nameOf a j "ends") (some e)
  rw [hR, Nat.add_sub_cancel]
  rfl

/-! ## 4 The maker's cut along the script -/

theorem headRun_sum : ∀ (vs : List MaskedSum.Var) (rest : List String),
    headRun "PSC round" ((vs.map fun _ => "PSC round") ++ "PSC Y" :: rest) = vs.length
  | [], rest => by simp [headRun]
  | v :: vs, rest => by
    have ih := headRun_sum vs rest
    unfold headRun at ih ⊢
    simp only [List.map_cons, List.cons_append, List.takeWhile_cons, beq_self_eq_true, if_true,
      List.length_cons, ih]

theorem entries_names (lead : Nat) (vs : List MaskedSum.Var) (e : MaskedSum.Ends) :
    (MaskedSum.entries ⟨lead, vs, some e⟩).map (·.name) =
      "PSC epsilon" :: ((vs.map fun _ => "PSC round") ++ ["PSC Y", "PSC values"]) := by
  simp [MaskedSum.entries, MaskedSum.entry, List.map_map, Function.comp_def]

theorem unitLen_sum (vs : List MaskedSum.Var) (rest : List String) :
    unitLen ("PSC epsilon" :: ((vs.map fun _ => "PSC round") ++
      "PSC Y" :: "PSC values" :: rest)) = vs.length + 3 := by
  have hl : (vs.map fun _ : MaskedSum.Var => "PSC round").length = vs.length := List.length_map ..
  have ha := headRun_sum vs ("PSC values" :: rest)
  have hd : ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
      "PSC Y" :: "PSC values" :: rest).drop vs.length = "PSC Y" :: "PSC values" :: rest :=
    List.drop_left' hl
  have hd1 : ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
      "PSC Y" :: "PSC values" :: rest).drop (vs.length + 1) = "PSC values" :: rest := by
    have e2 : ((vs.map fun _ : MaskedSum.Var => "PSC round") ++ "PSC Y" :: "PSC values" :: rest) =
        ((vs.map fun _ : MaskedSum.Var => "PSC round") ++ ["PSC Y"]) ++ "PSC values" :: rest := by
      simp
    rw [e2]
    exact List.drop_left' (by rw [List.length_append, hl]; rfl)
  have e0 : ("PSC epsilon" == "PSC epsilon") = true := rfl
  simp only [unitLen, e0, if_true, sumTail, ha, hd, hd1, headOne, List.head?_cons,
    beq_self_eq_true]
  omega

/-- One unit off the head of both lists. -/
theorem cons_unit {β : Type} (F : List (String × Nat) × Nat → β) (X rest : List (String × Nat))
    (c : String) (u ns2 : List String) (K j : Nat) (hX : X.length = (c :: u).length)
    (hu : unitLen ((c :: u) ++ ns2) = (c :: u).length) :
    ((stretchesBy (X ++ rest) (unitsOf (K + 1) ((c :: u) ++ ns2))).zipIdx j).map F =
      F (X, j) :: ((stretchesBy rest (unitsOf K ns2)).zipIdx (j + 1)).map F := by
  have e1 : unitsOf (K + 1) ((c :: u) ++ ns2) = (c :: u).length :: unitsOf K ns2 := by
    show unitLen ((c :: u) ++ ns2) ::
      unitsOf K (((c :: u) ++ ns2).drop (unitLen ((c :: u) ++ ns2))) = _
    rw [hu, List.drop_left]
  rw [e1]
  show F ((X ++ rest).take (c :: u).length, j) ::
    ((stretchesBy ((X ++ rest).drop (c :: u).length) (unitsOf K ns2)).zipIdx (j + 1)).map F = _
  rw [← hX, List.take_left, List.drop_left]

/-- **ALONG THE SCRIPT: WHAT THE MAKER STATES, PART BY PART, IS WHAT THE ROW's PARTS STATE.**
CONDITIONAL: each sumcheck of the list has at least one end value; K, the fuel of the maker's cut,
is no less than the number of entries. -/
theorem walk (a : Place) : ∀ (l : List Stage) (lead j K : Nat),
    (∀ vs e, Stage.sum vs e ∈ l → 1 ≤ e.n) → (entriesOf lead l).length ≤ K →
    ((stretchesBy ((entriesOf lead l).map pr)
      (unitsOf K ((entriesOf lead l).map (·.name)))).zipIdx j).map
        (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) = ((shapesOf lead l).zipIdx j).map (spendsOf a)
  | [], _, _, K, _, _ => by cases K <;> rfl
  | .scalars n :: l, lead, j, K, h, hK =>
    walk a l (lead + n) j K (fun vs e m => h vs e (List.mem_cons_of_mem _ m)) hK
  | .batch rows :: l, lead, j, K, h, hK => by
    cases K with
    | zero => exact absurd hK (Nat.not_succ_le_zero _)
    | succ K =>
      have ih := walk a l 0 (j + 1) K (fun vs e m => h vs e (List.mem_cons_of_mem _ m))
        (Nat.le_of_succ_le_succ hK)
      have hu : unitLen (("BAT-sigma" :: []) ++ (entriesOf 0 l).map (·.name)) =
          ("BAT-sigma" :: ([] : List String)).length := by simp [unitLen]
      have p0 : pr { name := "BAT-sigma", msg := 24 * lead, drawE := 1, rows := rows } =
          ("BAT-sigma", lead) := by simp [pr]
      have step := cons_unit (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) [("BAT-sigma", lead)]
        ((entriesOf 0 l).map pr) "BAT-sigma" [] ((entriesOf 0 l).map (·.name)) K j rfl hu
      show ((stretchesBy (pr { name := "BAT-sigma", msg := 24 * lead, drawE := 1, rows := rows } ::
        (entriesOf 0 l).map pr)
        (unitsOf (K + 1) ("BAT-sigma" :: (entriesOf 0 l).map (·.name)))).zipIdx j).map
          (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) =
        spendsOf a (.one lead, j) :: ((shapesOf 0 l).zipIdx (j + 1)).map (spendsOf a)
      rw [p0]
      refine step.trans ?_
      rw [ih]
      exact congrArg (· :: _) (one_stated a j "BAT-sigma" (by decide) (by decide) lead)
  | .point n :: l, lead, j, K, h, hK => by
    cases K with
    | zero => exact absurd hK (Nat.not_succ_le_zero _)
    | succ K =>
      have ih := walk a l 0 (j + 1) K (fun vs e m => h vs e (List.mem_cons_of_mem _ m))
        (Nat.le_of_succ_le_succ hK)
      have hu : unitLen (("ZERO" :: []) ++ (entriesOf 0 l).map (·.name)) =
          ("ZERO" :: ([] : List String)).length := by simp [unitLen]
      have step := cons_unit (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) [("ZERO", lead)]
        ((entriesOf 0 l).map pr) "ZERO" [] ((entriesOf 0 l).map (·.name)) K j rfl hu
      show ((stretchesBy (pr (MaskedSum.entry "ZERO" lead n 0) :: (entriesOf 0 l).map pr)
        (unitsOf (K + 1) ("ZERO" :: (entriesOf 0 l).map (·.name)))).zipIdx j).map
          (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) =
        spendsOf a (.one lead, j) :: ((shapesOf 0 l).zipIdx (j + 1)).map (spendsOf a)
      rw [pr_entry]
      refine step.trans ?_
      rw [ih]
      exact congrArg (· :: _) (one_stated a j "ZERO" (by decide) (by decide) lead)
  | .sum vs e :: l, lead, j, K, h, hK => by
    have hlen : (entriesOf lead (.sum vs e :: l)).length =
        (vs.length + 3) + (entriesOf 0 l).length := by
      show (MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).length = _
      rw [List.length_append]
      simp [MaskedSum.entries]
    cases K with
    | zero =>
      rw [hlen] at hK
      omega
    | succ K =>
      have ih := walk a l 0 (j + 1) K (fun vs e m => h vs e (List.mem_cons_of_mem _ m))
        (by rw [hlen] at hK; omega)
      have hu : unitLen (("PSC epsilon" :: ((vs.map fun _ => "PSC round") ++
          ["PSC Y", "PSC values"])) ++ (entriesOf 0 l).map (·.name)) =
          ("PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
            ["PSC Y", "PSC values"])).length := by
        have e2 : (("PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
            ["PSC Y", "PSC values"])) ++ (entriesOf 0 l).map (·.name)) =
            "PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
              "PSC Y" :: "PSC values" :: (entriesOf 0 l).map (·.name)) := by simp
        rw [e2, unitLen_sum]
        simp
      have hX : ((MaskedSum.entries ⟨lead, vs, some e⟩).map pr).length =
          ("PSC epsilon" :: ((vs.map fun _ : MaskedSum.Var => "PSC round") ++
            ["PSC Y", "PSC values"])).length := by
        rw [← entries_names lead vs e, List.length_map, List.length_map]
      have step := cons_unit (fun x => stated ⟨⟨a, x.2⟩, x.1⟩)
        ((MaskedSum.entries ⟨lead, vs, some e⟩).map pr) ((entriesOf 0 l).map pr) "PSC epsilon"
        ((vs.map fun _ => "PSC round") ++ ["PSC Y", "PSC values"])
        ((entriesOf 0 l).map (·.name)) K j hX hu
      show ((stretchesBy ((MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).map pr)
        (unitsOf (K + 1) ((MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).map
          (·.name)))).zipIdx j).map (fun x => stated ⟨⟨a, x.2⟩, x.1⟩) =
        spendsOf a (.sum ⟨lead, vs, some e⟩, j) ::
          ((shapesOf 0 l).zipIdx (j + 1)).map (spendsOf a)
      rw [List.map_append, List.map_append, entries_names]
      refine step.trans ?_
      rw [ih]
      exact congrArg (· :: _) (sum_stated a j lead vs e (h vs e (List.mem_cons_self ..)))

/-! ## 5 At K5's member -/

theorem cutOfNames_K5 (ns : List String) : cutOfNames .K5 ns = unitsOf ns.length ns := by
  unfold cutOfNames
  cases unitsOf ns.length ns with
  | nil => rfl
  | cons a rest => rfl

/-- **WHAT THE BOOK's MAKER STATES AT THE PARTS OF K5's MEMBER, BY NAME AND COUNT, IS WHAT THE PARTS
OF K5's ROW STATE THAT THEY SPEND.** CONDITIONAL: the member stands at the seat's place; its rounds
are the plan's; the plan's numbers are the seat's; the verifier's test on the plan accepts. -/
theorem k5_stated {S Cl : Type} (blk : Block S Cl) (p : Par) (Z : Seat5) (hpl : blk.place = Z.place)
    (hr : blk.rounds = rounds p) (hx : p.own = Z.P.x) (hok : planOk p = true) :
    (planParts blk).map stated = (k5Row Z).map (·.spends) := by
  have he : ∀ vs e, Stage.sum vs e ∈ script p.own → 1 ≤ e.n := by
    intro vs e hm
    unfold planOk at hok
    rw [Bool.and_eq_true] at hok
    have h1 := List.all_eq_true.1 hok.2 _ hm
    have h2 : MaskedSum.shapeOk ⟨0, vs, some e⟩ = true := h1
    unfold MaskedSum.shapeOk at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.2.2
  have hw := walk Z.place (script p.own) 0 0 ((entriesOf 0 (script p.own)).map (·.name)).length he
    (by rw [List.length_map])
  have hc : partsCut blk = unitsOf ((entriesOf 0 (script p.own)).map (·.name)).length
      ((entriesOf 0 (script p.own)).map (·.name)) := by
    unfold partsCut
    rw [hpl, hr, rounds_names]
    exact cutOfNames_K5 _
  unfold planParts
  rw [hc, hr, rounds_pr, hpl, List.map_map]
  refine Eq.trans ?_ (hw.trans ?_)
  · rfl
  · rw [hx]
    show _ = ((shapes Z.P.x).zipIdx.map (partAt Z.place (chalOf Z) (jobs Z.P))).map (·.spends)
    rw [List.map_map]
    exact List.map_congr_left fun s _ => (partAt_spends Z.place (chalOf Z) (jobs Z.P) s).symm

/-! ## 6 The names of K5's rounds -/

/-- Every entry of the script bears one of six names. -/
theorem names_in : ∀ (l : List Stage) (lead : Nat), ∀ n ∈ (entriesOf lead l).map (·.name),
    n ∈ ["PSC epsilon", "PSC round", "PSC Y", "PSC values", "BAT-sigma", "ZERO"]
  | [], _, n, h => by cases h
  | .scalars k :: l, lead, n, h => names_in l (lead + k) n h
  | .batch rows :: l, lead, n, h => by
    have h' : n ∈ "BAT-sigma" :: (entriesOf 0 l).map (·.name) := h
    rcases List.mem_cons.1 h' with rfl | h'
    · simp
    · exact names_in l 0 n h'
  | .point k :: l, lead, n, h => by
    have h' : n ∈ "ZERO" :: (entriesOf 0 l).map (·.name) := h
    rcases List.mem_cons.1 h' with rfl | h'
    · simp
    · exact names_in l 0 n h'
  | .sum vs e :: l, lead, n, h => by
    have h' : n ∈ (MaskedSum.entries ⟨lead, vs, some e⟩ ++ entriesOf 0 l).map (·.name) := h
    rw [List.map_append, entries_names, List.mem_append] at h'
    rcases h' with h' | h'
    · rcases List.mem_cons.1 h' with rfl | h'
      · simp
      · rcases List.mem_append.1 h' with h' | h'
        · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h'
          simp
        · rcases List.mem_cons.1 h' with rfl | h'
          · simp
          · rcases List.mem_cons.1 h' with rfl | h'
            · simp
            · cases h'
    · exact names_in l 0 n h'

/-- **NO ROUND OF K5's MEMBER IS NAMED "SEND seed" OR "FOLD epsilon".** CONDITIONAL: its rounds are
the plan's. -/
theorem k5_plain_names {S Cl : Type} (blk : Block S Cl) (p : Par) (hr : blk.rounds = rounds p) :
    ∀ r ∈ blk.rounds, r.entry.name ≠ "SEND seed" ∧ r.entry.name ≠ "FOLD epsilon" := by
  intro r hm
  have h1 : r.entry.name ∈ (rounds p).map fun r => r.entry.name :=
    List.mem_map.2 ⟨r, hr ▸ hm, rfl⟩
  rw [rounds_names] at h1
  have h2 := names_in (script p.own) 0 _ h1
  refine ⟨fun e => ?_, fun e => ?_⟩ <;> rw [e] at h2 <;> simp at h2

theorem k5_no_seed {S Cl : Type} (blk : Block S Cl) (p : Par) (hr : blk.rounds = rounds p) :
    ∀ r ∈ blk.rounds, r.entry.name ≠ "SEND seed" := fun r hm => (k5_plain_names blk p hr r hm).1

theorem k5_no_fold {S Cl : Type} (blk : Block S Cl) (p : Par) (hr : blk.rounds = rounds p) :
    ∀ r ∈ blk.rounds, r.entry.name ≠ "FOLD epsilon" := fun r hm => (k5_plain_names blk p hr r hm).2

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.partAt_spends
#print axioms ProofFile.Honest.K5.pr_entry
#print axioms ProofFile.Honest.K5.rounds_pr
#print axioms ProofFile.Honest.K5.rounds_names
#print axioms ProofFile.Honest.K5.one_stated
#print axioms ProofFile.Honest.K5.own_rounds
#print axioms ProofFile.Honest.K5.end_rounds
#print axioms ProofFile.Honest.K5.foldl_shift
#print axioms ProofFile.Honest.K5.entries_pr
#print axioms ProofFile.Honest.K5.sum_stated
#print axioms ProofFile.Honest.K5.headRun_sum
#print axioms ProofFile.Honest.K5.entries_names
#print axioms ProofFile.Honest.K5.unitLen_sum
#print axioms ProofFile.Honest.K5.cons_unit
#print axioms ProofFile.Honest.K5.walk
#print axioms ProofFile.Honest.K5.cutOfNames_K5
#print axioms ProofFile.Honest.K5.k5_stated
#print axioms ProofFile.Honest.K5.names_in
#print axioms ProofFile.Honest.K5.k5_plain_names
#print axioms ProofFile.Honest.K5.k5_no_seed
#print axioms ProofFile.Honest.K5.k5_no_fold
