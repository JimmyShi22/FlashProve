-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieThreeRows.lean: THE TIE t3 OF A LINK's THIRD PIECE (t3_eq,
TieThreeEq.lean) WITH ITS PREMISE "rows" (the group's list ends with the equation's
row) PAID OUT OF THE TABLE's OWN PROMISE BEHIND THE PIECE, and "grp" asked in front of it. It
overtakes t3_eq_front's premise hr (TieThreeFront.lean), which nobody had. Theorems.

WHY. The promise at a border holds a test with code on the verifier's state, `rowsHeld`
(Johnson/Desc/First/Borders.lean): of every segment of which a class of rows is open: ITS GROUP's
LIST HAS JUST AS MANY ROWS AS THE OPEN CLASSES COUNT (`rowsDue`). Behind the one equation's piece
the class "equation" of the segment is open. So the list's length there is the promise's to say, and
what is left is a closed fact on the table and the plan's numbers.

What is said.
  `rowsHeld_of_onQ`: the test, out of the promise at an unmarked state (the like of
    membersHeld_of_onQ).
  `rows_of_promise`: where a class of rows of segment m is open at border k: the list of the
    segment's group has rowsDue N O m rows.
  `grp_step`: a yes of the one equation's step leaves the group that the link's check names.
  `t3_eq_rows`: **t3 AT THE ONE EQUATION's PIECE**, ending in the field's own type: behind: EqRest
    (six fields); in front: hg · K9.totalIn · InsideAt · hstep; closed: houts · hn · hopen · hdue.

Limits. PREMISES: closed facts: houts · hn · hopen (the class is open behind the piece) · hdue (the
count there is the equation's place and one: numbers_of_fit and rowsDue_snoc say the
like in front) · inside `onTR`, SHOWN AT NO STATE HERE: EqRest behind; hg · hT · hin in front ·
hstep. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TieThreeFront
import Johnson.Desc.First.Link.Law.RowsPush

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item RowClass Meaning Numbers rowSays wordsAtFirst start
  openSets rowSegs rowsDue rowsHeld)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- **The test on the open rows' lists, out of the promise.** -/
theorem rowsHeld_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    rowsHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact e.1.1.1.1.2

/-- **THE LIST's LENGTH IS THE PROMISE's TO SAY.** -/
theorem rows_of_promise {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) (m : ℕ) (c : RowClass)
    (hopen : Item.row m c ∈ (openSets links ps (start links))[k]?.getD []) (G : Group)
    (hG : (get a.1).2.st.groups[N.groupAt m]? = some G) :
    G.rows.size = rowsDue N ((openSets links ps (start links))[k]?.getD []) m := by
  have hr := rowsHeld_of_onQ N Mg links ps get k a h hm
  unfold rowsHeld at hr
  have h1 := List.all_eq_true.1 hr m ((mem_rowSegs _ m).2 ⟨c, hopen⟩)
  rw [hG] at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1.1.2

/-- **A yes of the one equation's step leaves the group that the link's check names.** -/
theorem grp_step {Cl : Type} (p : Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (n : ℕ) (hs : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', n))
    (g : ℕ) (hg : ∀ x, atS.get? s = some x → x.L.check.group = g) :
    ∀ a', atS.get? s' = some a' → a'.L.check.group = g := by
  intro a' ha'
  obtain ⟨a, out, ha, hdoor, e⟩ := oneEquation_inv atS p ft s rs cols s' n hs
  obtain ⟨a₁, e0, _, e2, _⟩ :=
    atS_reads s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← e] at e0
  obtain rfl : a₁ = a' := Option.some.inj (e0.symm.trans ha')
  rw [e2]
  show out.L.check.group = g
  rw [door_link _ _ _ _ _ _ hdoor]
  exact hg a ha

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **t3 AT THE ONE EQUATION's PIECE, THE LIST's LENGTH OUT OF THE PROMISE.** -/
theorem t3_eq_rows {C : CK} (M : List OracleShape) (N : ℕ)
    (houts : (rowQ links pl k).outs = [.row m .equation])
    (hn : 0 < (𝔇.N.rowsAt m .equation).2)
    (hopen : Item.row m .equation ∈ (openSets links pl (start links))[k + 1]?.getD [])
    (hdue : rowsDue 𝔇.N ((openSets links pl (start links))[k + 1]?.getD []) m =
      (𝔇.N.rowsAt m .equation).1 + 1)
    (hA : ∀ b, onK (k + 1) b → EqRest 𝔇.cs 𝔇.ms M (𝔇.N.groupAt m) N b.1)
    (hg : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → x.L.check.group = 𝔇.N.groupAt m)
    (hT : ∀ a, onK k a → K9.totalIn own a.1 = true)
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, onK k a → pe.ior.red.out a τ = some b → ∃ p ft rs cols n,
      (K9.oneEquation (Cl := Claim) atS p).step ft a.1 rs cols = .ok (b.1, n)) :
    ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relRow own N rdW b w := by
  intro a τ b w ha hout hb h
  obtain ⟨p, ft, rs, cols, n, hs⟩ := hstep a τ b ha hout
  have R := hA b hb
  have hm : b.1.failed = none := Classical.not_not.1 hb.1.2
  have h1 : rowSays 𝔇.N (wordsAtFirst 𝔇.arr) m .equation (z, b.1) (strsOf F b.2) w :=
    h (.row m .equation) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  exact rowEq_of_says 𝔇.cs 𝔇.arr 𝔇.ms own M _ _ _ N hn b.1 w
    { order := R.order
      grp := grp_step p ft a.1 rs cols b.1 n hs _ (hg a ha)
      rows := fun G hG => (rows_of_promise 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b hb.1.1
        hm m .equation hopen G hG).trans hdue
      codes := R.codes, shapes := R.shapes, numbers := R.numbers, places := R.places
      member := R.member }
    (seats_first own p ft a.1 rs cols b.1 n hs (hT a ha))
    (rowInside_step 𝔇.cs 𝔇.ms own p ft a.1 rs cols b.1 n N hs (hin a ha)) h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsHeld_of_onQ
#print axioms VerifiableInference.Desc.LinkJoin.rows_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.grp_step
#print axioms VerifiableInference.Desc.LinkJoin.t3_eq_rows
