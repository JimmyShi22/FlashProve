-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SendForms.lean: THE SENDING (the kind K1) ON THE ROWS' MAKES: the sample
rows that a sending lays have makes that hang on the plan, the messages' numbers and the number of
a seed's coordinates alone. General in the carried record; nothing is evaluated.

  1 `tensorSh_eq`, `padIdx`, `sampleRowS`, `units_loop`, `rowMk_add`, `rowMk_target`,
    **`sampleRow_mk`**: rowMk (K1.sampleRow m o z β i y) = sampleRowS m o z.length
    (Johnson/Desc/K1/Own.lean:84): kind sample; a single entry at each pad's place of every answer;
    a term on the main table and one on the mask table where the message has such rows, each an
    equality vector on as many variables as the table has bits, at most the seed's coordinates. It
    does not hang on which answer the row is for.
  2 `sentMk`, `rowsOf_mk`, `orcMk_wr`, `sentMks`, `outs_mk`, `sendForms`, `forms_behind`,
    **`send_forms`**: from a return of K1.decideSend on two rounds, AND NOTHING ELSE: formsOf x.2.st
    = sendForms P d.st.oracles.size (formsOf d.st): no group's rows turn; each new message has as
    many sample rows as answers, all of one make. (The return says that no seed's factor is 0; such
    a seed has all its coordinates: the library's K1.cutSeeds_full.)

Limits. The joinings behind a sending turn no row (Forms.lean's join_forms). Nothing on
what a row is worth. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.SendCore
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.K1.Law.RowsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open _root_.Desc.Plain (DState)

variable {L : Type}

/-! ## 1 A sample row's make -/

theorem tensorSh_eq (z : List E) (s : E) : tensorSh (Tensor.eq z s) = ⟨z.length, [], 0, 0⟩ := by
  unfold Tensor.eq tensorSh
  simp

/-- The indices of all pads' entries of a message, answer by answer. -/
def padIdx (m : K1.Msg) : List Nat :=
  (List.range m.answers).flatMap fun k => (m.pad k).map (·.1)

/-- K1.sampleRow's make. zlen: the number of the seed's coordinates. -/
def sampleRowS (m : K1.Msg) (o zlen : Nat) : RowMk :=
  { kind := .sample
    terms := (if m.K != 0 then [⟨o, .main, ⟨min m.mainBits zlen, [], 0, 0⟩⟩] else []) ++
      (if m.Kzk != 0 then [⟨o, .mask, ⟨min m.maskBits zlen, [], 0, 0⟩⟩] else [])
    units := (padIdx m).map fun j => ⟨o, if m.Kzk != 0 then .mask else .main, j⟩
    runs := [], forms := [] }

theorem units_loop {ι : Type} (o : Nat) (part : Part) (ix : ι → Nat) (c : ι → E) :
    ∀ (l : List ι) (r : OnBytes.Row),
      rowMk (l.foldl (fun r x => r.addUnit o part (ix x) (c x)) r) =
        { rowMk r with units := (rowMk r).units ++ l.map fun x => ⟨o, part, ix x⟩ }
  | [], r => by simp
  | x :: l, r => by
    rw [List.foldl_cons, units_loop o part ix c l]
    unfold OnBytes.Row.addUnit rowMk
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]
    rfl

theorem rowMk_add (r : OnBytes.Row) (o : Nat) (part : Part) (v : Tensor) :
    rowMk (r.add o part v) =
      { rowMk r with terms := (rowMk r).terms ++ [⟨o, part, tensorSh v⟩] } := by
  unfold OnBytes.Row.add rowMk
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem rowMk_target (r : OnBytes.Row) (y : E) : rowMk { r with target := y } = rowMk r := by
  cases r
  rfl

/-- **A sample row's make hangs on the message's numbers, its number and the number of the seed's
coordinates: not on which answer it is for.** -/
theorem sampleRow_mk (m : K1.Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E) :
    rowMk (K1.sampleRow m o z β i y) = sampleRowS m o z.length := by
  unfold K1.sampleRow sampleRowS
  dsimp only
  rw [rowMk_target]
  have hu := units_loop o (if m.Kzk != 0 then Part.mask else Part.main)
    (fun x : Nat × Nat × Nat => x.2.1)
    (fun x => subE (if x.1 == i then mulE β (thetaE x.2.2) else zeroE)
      ((if m.Kzk != 0 then Tensor.eq (z.take m.maskBits) (m.front z m.maskBits true)
        else Tensor.eq (z.take m.mainBits) (m.front z m.mainBits false)).entry x.2.1))
    ((List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)) { kind := .sample }
  have hp : ((List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)).map
      (fun x : Nat × Nat × Nat =>
        (⟨o, if m.Kzk != 0 then Part.mask else Part.main, x.2.1⟩ : UnitMk)) =
      (padIdx m).map fun j => ⟨o, if m.Kzk != 0 then .mask else .main, j⟩ := by
    unfold padIdx
    simp only [List.map_flatMap, List.map_map]
    rfl
  rw [hp] at hu
  revert hu
  generalize List.foldl _ ({ kind := .sample } : OnBytes.Row) _ = r₀
  intro hu
  by_cases h1 : (m.K != 0) = true <;> by_cases h2 : (m.Kzk != 0) = true
  · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, rowMk_add, rowMk_add, hu, tensorSh_eq,
      tensorSh_eq, List.length_take, List.length_take]
    rfl
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, rowMk_add, hu, tensorSh_eq, List.length_take]
    rfl
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, rowMk_add, hu, tensorSh_eq, List.length_take]
    rfl
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, hu]
    rfl

/-! ## 2 A sending's new messages -/

/-- The sample rows' makes of one new message. v: the number of a seed's coordinates. -/
def sentMk (codes : Codes) (v o : Nat) (s : OracleShape) : List RowMk :=
  List.replicate s.answers (sampleRowS (K1.Msg.of codes s) o v)

theorem rowsOf_mk (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (v : Nat) (hv : ∀ x ∈ seeds, x.1.length = v) (h1 : s.answers ≤ seeds.length)
    (h2 : s.answers ≤ ys.length) :
    (K1.rowsOf codes seeds o s ys).toList.map rowMk = sentMk codes v o s := by
  unfold sentMk
  rw [List.eq_replicate_iff]
  refine ⟨by rw [List.length_map, Array.length_toList, K1.rowsOf_size codes seeds o s ys h1 h2],
    fun b hb => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
  unfold K1.rowsOf at hr
  rw [List.toList_toArray] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  rw [sampleRow_mk]
  have hm : x.1.1 ∈ seeds :=
    List.mem_of_mem_take (List.of_mem_zip (List.mem_zipIdx' hx |> fun _ =>
      (List.mem_map.2 ⟨x, hx, rfl⟩ : x.1 ∈ (List.zipIdx _).map (·.1)) |> fun h => by
        rwa [List.zipIdx_map_fst] at h)).1
  rw [hv _ hm]

theorem orcMk_wr (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (v : Nat) (hv : ∀ x ∈ seeds, x.1.length = v)
    (h : s.answers ≠ 0 → s.answers ≤ seeds.length ∧ s.answers ≤ ys.length) :
    orcMk (K1.wr codes seeds o s ys) = sentMk codes v o s := by
  unfold K1.wr
  split
  · rename_i h0
    unfold sentMk
    rw [h0]
    rfl
  · rename_i h0
    exact rowsOf_mk codes seeds o s ys v hv (h h0).1 (h h0).2

/-- All new messages' sample rows' makes, from the number o on. -/
def sentMks (codes : Codes) (v : Nat) : Nat → List OracleShape → List (List RowMk)
  | _, [] => []
  | o, s :: l => sentMk codes v o s :: sentMks codes v (o + 1) l

theorem outs_mk (codes : Codes) (seeds : List (List E × E)) (v : Nat)
    (hv : ∀ x ∈ seeds, x.1.length = v) :
    ∀ (l : List OracleShape) (o : Nat) (ys : List E), K1.fitB codes seeds.length l ys = true →
      (K1.outs codes seeds o l ys).map orcMk = sentMks codes v o l
  | [], _, _, _ => rfl
  | s :: l, o, ys, h => by
    show orcMk (K1.wr codes seeds o s ys) ::
      (K1.outs codes seeds (o + 1) l (ys.drop s.answers)).map orcMk =
        sentMk codes v o s :: sentMks codes v (o + 1) l
    unfold K1.fitB at h
    by_cases h0 : s.answers = 0
    · rw [if_pos h0] at h
      rw [orcMk_wr _ _ _ _ _ v hv (fun h1 => absurd h0 h1), h0, List.drop_zero,
        outs_mk codes seeds v hv l (o + 1) ys h]
    · rw [if_neg h0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [orcMk_wr _ _ _ _ _ v hv (fun _ => ⟨h.1.1.1, h.1.1.2⟩),
        outs_mk codes seeds v hv l (o + 1) _ h.2]

/-- The makes behind a sending. n0: the number of messages in front. -/
def sendForms (P : K1.Par) (n0 : Nat) (F : FormsSh) : FormsSh :=
  { F with oracles := F.oracles ++ sentMks P.codes P.coordinates n0 (K1.shapesOf P) }

theorem forms_behind (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E)
    (hv : ∀ x ∈ seeds, x.1.length = P.coordinates)
    (hf : K1.fitB P.codes seeds.length (K1.shapesOf P) ys = true) :
    formsOf (K1.behind P d seeds ys).st = sendForms P d.st.oracles.size (formsOf d.st) := by
  show (⟨d.st.groups.toList.map grpMk, ((d.st.oracles.toList ++ K1.outs P.codes seeds
    d.st.oracles.size (K1.shapesOf P) ys).toArray).toList.map orcMk⟩ : FormsSh) = _
  rw [List.toList_toArray, List.map_append, outs_mk _ _ _ hv _ _ _ hf]
  rfl

/-- **A sending's return, seen through the rows' makes.** From the yes alone: it says that no seed's
factor is 0, and such a seed has all its coordinates (the library's K1.cutSeeds_full). -/
theorem send_forms {P : K1.Par} {owed : Option Nat} {d : DState L} {r₁ r₂ : Fmt.RoundView}
    {x : Array Nat × DState L} (h : K1.decideSend P owed d [r₁, r₂] = .ok x) :
    formsOf x.2.st = sendForms P d.st.oracles.size (formsOf d.st) := by
  obtain ⟨ids, d'⟩ := x
  have hz := (K1.decideSend_ok P owed d d' r₁ r₂ ids h).2.2.1
  obtain ⟨ha, rfl, rfl⟩ := (K1.decideSend_iff P owed d d' r₁ r₂ ids).1 h
  refine forms_behind P d _ _ (fun y hy => ?_) ?_
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hy
    exact (K1.cutSeeds_full _ _ _ i y hi (hz y hy)).1
  rw [show (K1.seedsOf P r₁).length = P.seeds from K1.cutSeeds_length _ _ _]
  exact ha.2.2.2.2

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.rowsOf_mk
#print axioms VerifiableInference.Desc.First.Shape.outs_mk
#print axioms VerifiableInference.Desc.First.Shape.forms_behind
#print axioms VerifiableInference.Desc.First.Shape.send_forms
#print axioms VerifiableInference.Desc.First.Shape.sampleRow_mk
