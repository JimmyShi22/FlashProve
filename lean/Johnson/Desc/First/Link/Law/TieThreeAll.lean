-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieThreeAll.lean: THE TIE t3 OF A LINK's THIRD PIECE (the one
equation's)
AT THE TABLE (`TieRestR`, LinkTiedR.lean) AND THE COMPOSED MEANING (`mgAll 𝔇 Mg₀`), WITH NOTHING
LEFT ON THE STATE BEHIND THE PIECE BUT ANOTHER FILE's LIST OF FACTS ON REACHED STATES (`FoldFacts`)
AND THE TABLE's OWN PROMISE. Two theorems: a joining of TieThreeEq.lean (rowEq_of_says),
TieThreeRows.lean (rows_of_promise, grp_step), EqRestOf.lean (eqRest_of_facts, bookAt_of_onQ),
FactsAtList.lean (grp_of_facts), two lemmas behind the step's yes (seats_first,
rowInside_step) and member_listed (MemberListed.lean).

What is said.
  `eqRest_at`: EqRest at one state, "member" asked at that state alone.
  `t3_eq_all`: **t3 AT THE ONE EQUATION's PIECE**, ending in the field's own type at
    R' := relRow (𝔇.N.group m) N (rdC 𝔇.cs 𝔇.arr 𝔇.ms).
    "member" (EqRest's last field) is paid HERE, inside the proof, because it wants both sides of
    the step: "the seat is of the segment's own list" comes from the test K9.totalIn IN FRONT of the
    step (seats_first); "a member with the listed shape sits there" from the list and the promise
    BEHIND it (member_listed), under one closed test (hmem).

PREMISES, BY SORT.
  closed facts (the table · the written list · the plan's numbers · the list's data): houts · hn ·
    hopen · hdue · hp · hl · hgr · hcs · hft · hN · hmem.
  on states, asked only inside the condition `onTR`: FF (FoldFacts at the condition's own Rz) · hT
    (K9.totalIn in front) · hin (InsideAt in front).
  the law's own: hstep (step_of_out, TieFronts.lean, pays it from hpe and hb₃).

Limits. FF, hT AND hin ARE SHOWN AT NO STATE HERE; THE CLOSED FACTS ARE EVALUATED BY NOBODY HERE.
Where no state meets the condition on both sides of the piece the tie is idle. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EqRestOf
import Johnson.Desc.First.Link.Law.FactsAtList
import Johnson.Desc.First.Link.Law.MemberListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers rowSays wordsAtFirst start openSets
  rowsDue FoldFacts FoldData)
open _root_.Run.PQ (CK)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Frame}
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- EqRest AT ONE STATE, "member" asked at that state alone (eqRest_of_facts asks it at all). -/
theorem eqRest_at {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW links pl) (N : ℕ)
    (hcs : d.sent.codes = 𝔇.cs) (hft : d.ft = 0) (hN : d.M.length ≤ N) (b : S × F.E.Str)
    (hb : onK k b)
    (member : ∀ G row, b.1.st.groups[𝔇.N.groupAt m]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, b.1.book.place[o]? = some q →
      ∃ y, (𝔇.ms.find? fun y => decide (seatOf y = q)) = some y ∧
        d.M[o]? = some (y.1.l.get y.2).1) :
    EqRest 𝔇.cs 𝔇.ms d.M (𝔇.N.groupAt m) N b.1 := by
  have hf : b.1.failed = none := Classical.not_not.1 hb.1.2
  have hsh : K12.Door.msgShapesB d.M b.1.st = true := FF.msgShapes k b hb.2 hf
  have hbk : K12.Door.bookInOrderB d.ft b.1.book b.1.roots = true := FF.bookInOrder k b hb.2 hf
  rw [hft] at hbk
  have hfit : Book.BookFits b.1.book := (bookFitsB_iff b.1.book).1 (FF.bookFits k b hb.2 hf)
  have hat := bookAt_of_onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) k b hb.1.1 hf
  unfold First.bookAt at hat
  simp only [Bool.and_eq_true, beq_iff_eq] at hat
  have hsz : b.1.book.place.size = b.1.st.oracles.size := hat.1.2
  have hle : b.1.st.oracles.size ≤ d.M.length := by
    unfold K12.Door.msgShapesB at hsh
    rw [Bool.and_eq_true] at hsh
    exact of_decide_eq_true hsh.2
  exact
    { order := ⟨(OnBytes.Means.tidy4B_iff.1 (FF.tidy k b hb.2 hf)).inOrder, Nat.le_trans hle hN⟩
      codes := (FF.codes k b hb.2 hf).trans hcs
      shapes := fun o ho => K12.Door.msgShape_at hsh o ho
      numbers := fun t T hT => K12.Door.numbers_of_book0 hbk t T hT
      places := fun o ho => by
        have ho' : o < b.1.book.place.size := by rw [hsz]; exact ho
        have hq : b.1.book.place[o]? = some b.1.book.place[o] := Array.getElem?_eq_getElem ho'
        obtain ⟨t, ht, _⟩ := hfit o _ hq
        exact ⟨_, hq, (Array.getElem?_eq_some_iff.1 ht).1⟩
      member := member }

/-- **t3 AT THE ONE EQUATION's PIECE: NOTHING LEFT BEHIND IT BUT THE LIST AND THE PROMISE.** -/
theorem t3_eq_all {C : CK} {d : FoldData} {reqW : P → Array UInt32}
    (FF : FoldFacts Rz (fun a : S × F.E.Str => (z, a.1)) d reqW links pl) (N : ℕ)
    (houts : (rowQ links pl k).outs = [.row m .equation])
    (hn : 0 < (𝔇.N.rowsAt m .equation).2)
    (hopen : Item.row m .equation ∈ (openSets links pl (start links))[k + 1]?.getD [])
    (hdue : rowsDue 𝔇.N ((openSets links pl (start links))[k + 1]?.getD []) m =
      (𝔇.N.rowsAt m .equation).1 + 1)
    (p : Place) (hp : pl[k]? = some p) (hl : p.link = some m)
    (hgr : d.groupAt m = 𝔇.N.groupAt m) (hcs : d.sent.codes = 𝔇.cs) (hft : d.ft = 0)
    (hN : d.M.length ≤ N)
    (hmem : membersThereB d 𝔇.ms own (𝔇.N.msgsAt pl[k + 1]?) = true)
    (hT : ∀ a, onK k a → K9.totalIn own a.1 = true)
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hstep : ∀ a τ b, onK k a → pe.ior.red.out a τ = some b → ∃ p ft rs cols n,
      (K9.oneEquation (Cl := Claim) atS p).step ft a.1 rs cols = .ok (b.1, n)) :
    ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relRow own N rdW b w := by
  intro a τ b w ha hout hb h
  obtain ⟨pw, ft, rs, cols, n, hs⟩ := hstep a τ b ha hout
  have hm : b.1.failed = none := Classical.not_not.1 hb.1.2
  have hseat := seats_first own pw ft a.1 rs cols b.1 n hs (hT a ha)
  have hg1 := grp_step pw ft a.1 rs cols b.1 n hs _
    (grp_of_facts 𝔇 Mg₀ links pl z Rz k m FF p hp hl hgr a ha)
  have hB := bookAt_of_onQ 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b hb.1.1 hm
  have h1 : rowSays 𝔇.N (wordsAtFirst 𝔇.arr) m .equation (z, b.1) (strsOf F b.2) w :=
    h (.row m .equation) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  -- the part behind the step: it is there, for the step's yes writes through the lens
  obtain ⟨a0, out, ha0, _, e⟩ := oneEquation_inv atS pw ft a.1 rs cols b.1 n hs
  obtain ⟨a', ha', _, _, _⟩ :=
    atS_reads a.1 { a0 with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha0])
  rw [← e] at ha'
  have hst := st_part b.1 a' ha'
  have hbk := book_part b.1 a' ha'
  have R := eqRest_at 𝔇 Mg₀ links pl z Rz (k + 1) m FF N hcs hft hN b hb
    fun G row hG hr o part J hz q hq =>
      member_listed FF 𝔇.N 𝔇.ms own hb.2 hm hB hq
        (hseat a' G row ha' (by rw [hst, hg1 a' ha']; exact hG) hr o part J hz q
          (by rw [hbk]; exact hq)) hmem
  exact rowEq_of_says 𝔇.cs 𝔇.arr 𝔇.ms own d.M _ _ _ N hn b.1 w
    { order := R.order
      grp := hg1
      rows := fun G hG => (rows_of_promise 𝔇.N Mg links pl (fun s : S => (z, s)) (k + 1) b hb.1.1
        hm m .equation hopen G hG).trans hdue
      codes := R.codes, shapes := R.shapes, numbers := R.numbers, places := R.places
      member := R.member }
    hseat (rowInside_step 𝔇.cs 𝔇.ms own pw ft a.1 rs cols b.1 n N hs (hin a ha)) h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.eqRest_at
#print axioms VerifiableInference.Desc.LinkJoin.t3_eq_all
