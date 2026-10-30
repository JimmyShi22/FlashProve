-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanFast.lean: THE CLOSED TESTS OF Johnson/Road/K4/K4PlanClosed.lean IN A FORM
THAT CAN RUN. `firstB` and `laterB` read the numbering of the messages through `arrAt Z` and `numAt
Z`, which make the list of keys anew at every call, and `shapesTiedB` asks for a segment's group
some hundred thousand times. Here the keys, the table "seat ↦ number" and the 25 groups are laid
ONCE, in front of the tests; and the law: the fast tests give what the slow ones give. Thirteen
definitions with code and thirteen theorems. Glue; no draw, no count.

  `seatKeys`, `arrTab`: the keys, each once; the table "seat ↦ the place of its key".
  `lookup_tab`, `arrOf_tab`: `P5T.arrOf ps` IS the look-up in that table, at every pair of numbers.
  `firstWithB`, `laterWithB`: `firstB`, `laterB` with num, arr (and the groups that `shapesTiedB`
    reads) as letters; `firstB_with`, `laterB_with`: by unfolding.
  `firstFastB`, `laterFastB`: these at the tables.
  `firstFast_eq`: `firstFastB Z g = firstB Z g`.
  `three_of_laterFast`: a yes of `laterFastB` gives what `three_of_laterB` concludes.
  `commonFastB Z`, `seamFastB Z g`, `seamFit_of_parts`: IN PARTS: six of the ten tests do
    not hang on the group: asked once; two at each seam: these give `SeamFit`; with `firstFastB` at
    each group (`firstFast_eq`, `two_of_firstB`) that is 1 + 11 + 12 closed tests for all twelve
    groups.
  `k4PlanFit_fast`, `k4PlanFitF_fast`: THE TWO STRUCTURES FROM THE TESTS THAT CAN RUN, and what is
    no test.
  `pinsCore`, `firstCoreB`, `commonCoreB`, `seamCoreB`, `allFastB Z`: ALL 24 IN ONE TEST, A FUNCTION
    OF Z ALONE, WITH EVERY LETTER (D, the seats, N, the members, the tables) LAID ONCE: an
    evaluator makes `seatsAt Z` anew wherever it stands inside a test: at the full size the 24 asked
    one by one did not end within an hour. `allFast_eq`: it is the 24, by unfolding;
    `parts_of_all`: one yes gives each.

Limits. K04_law IS NOT PROVED BY THIS. NO RUN IS A PART OF THIS FILE. `laterFastB = laterB` is NOT
shown: the table of groups answers [] from segment 25 on; the law goes through the condition
(`shapesTied_of_table`). AT A NUMBER g THAT IS NO GROUP's, `firstB` AND `firstFastB` CAN SAY YES OF
NOTHING: `Meaning.tlAt X (2 g)` is then the empty default, with no matrix to ask: the laws take
X.G[p.g]? = some p.hp beside the yes. Whether Lean's kernel bears these tests is not tried.

-/
import Johnson.Road.K4.K4PlanClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Layer (matIx)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.PlanWritten (PublicSteps)
open VerifiableInference.Desc.First (Numbers groupsAreMembers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (Mem msOf)
open Johnson.Road.K4.LayoutTies (shapesTiedB)
open Meaning (nmFit pairFit seatBy fLay follows_sizesOf)
open Inst.Model.Layout (kRef hRef)

/-! ## 1 The table "seat ↦ number" -/

/-- The seats' keys, each once, in the list's order. -/
def seatKeys (ps : List P5T.PSeat) : List (ℕ × ℕ × ℕ) := (ps.map P5T.keyOf).eraseDups

/-- Seat ↦ the place of its key among keys. -/
def arrTab (keys : List (ℕ × ℕ × ℕ)) (ps : List P5T.PSeat) : List ((ℕ × ℕ) × ℕ) :=
  ps.map fun p => ((p.j, p.t), keys.idxOf (P5T.keyOf p))

theorem lookup_tab (keys : List (ℕ × ℕ × ℕ)) (j t : ℕ) : ∀ ps : List P5T.PSeat,
    (arrTab keys ps).lookup (j, t) =
      (ps.find? fun p => p.j == j && p.t == t).map fun p => keys.idxOf (P5T.keyOf p)
  | [] => rfl
  | p :: l => by
    have ih := lookup_tab keys j t l
    have hb : ((j, t) == (p.j, p.t)) = (p.j == j && p.t == t) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true]
      constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a.symm, b.symm⟩
    show List.lookup (j, t) (((p.j, p.t), keys.idxOf (P5T.keyOf p)) :: arrTab keys l) = _
    rw [List.lookup_cons, List.find?_cons, hb]
    cases (p.j == j && p.t == t)
    · exact ih
    · rfl

/-- **`arrOf` is the look-up in the table.** -/
theorem arrOf_tab (ps : List P5T.PSeat) (j t : ℕ) :
    P5T.arrOf ps j t = ((arrTab (seatKeys ps) ps).lookup (j, t)).getD (seatKeys ps).length := by
  rw [lookup_tab]
  unfold P5T.arrOf seatKeys
  cases ps.find? fun p => p.j == j && p.t == t <;> rfl

/-! ## 2 The tests with the numbering as letters -/

/-- `firstB` with num and arr as letters. -/
def firstWithB (Z : ProofFile.Pub) (g : ℕ) (num arr : ℕ → ℕ → ℕ) : Bool :=
  sitsInB (sigListCalls (sentAt Z) (fun _ => 0) (2 * g)) (pinsZero Z (2 * g)).seatT
      (msOf (lists0At Z)) (numbersAt Z) (2 * g) &&
    (List.range (Meaning.sizesOf Z.p.X (2 * g)).NM).all fun μ =>
      symTieB (pinsZero Z (2 * g)) num arr (numbersAt Z) (2 * g)
        (Meaning.tlAt Z.p.X (2 * g)) Z.p.X (Meaning.sizesOf Z.p.X) μ

theorem firstB_with (Z : ProofFile.Pub) (g : ℕ) :
    firstB Z g = firstWithB Z g (numAt Z) (arrAt Z) := rfl

/-- `laterB` with num, arr and the groups that `shapesTiedB` reads as letters. -/
def laterWithB (Z : ProofFile.Pub) (g : ℕ) (num arr : ℕ → ℕ → ℕ)
    (grp : ℕ → List (ℕ × ℕ)) : Bool :=
  firstWithB Z g num arr && (sentAt Z).codes.lengthsOk && reqShapeOk (sentAt Z).shape &&
    reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout && nmFit Z.p.X &&
    shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout num arr (lists0At Z) grp &&
    groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z) &&
    pairFit Z.p.X (2 * g) (matIx Z.p.X.y).iXI (2 * (g - 1)) (matIx Z.p.X.y).iXO &&
    seamArrB Z.p.X (Meaning.sizesOf Z.p.X) (sentAt Z).layout num arr (numbersAt Z)
      (2 * g) (2 * (g - 1)) (matIx Z.p.X.y).iXI

theorem laterB_with (Z : ProofFile.Pub) (g : ℕ) :
    laterB Z g =
      laterWithB Z g (numAt Z) (arrAt Z) fun k => (numbersAt Z).group k := rfl

/-! ## 3 At the tables -/

/-- **What the first group asks, with the keys and the table laid once.** -/
def firstFastB (Z : ProofFile.Pub) (g : ℕ) : Bool :=
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  firstWithB Z g (fun l k => keys.idxOf (0, l, k)) fun j t =>
    (tab.lookup (j, t)).getD keys.length

/-- **What a later group asks, with the keys, the table and the 25 groups laid once.** -/
def laterFastB (Z : ProofFile.Pub) (g : ℕ) : Bool :=
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  let tbl := (List.range 25).map fun k => (numbersAt Z).group k
  laterWithB Z g (fun l k => keys.idxOf (0, l, k))
    (fun j t => (tab.lookup (j, t)).getD keys.length) fun k => tbl.getD k []

/-- The two functions at the tables are `numAt Z` and `arrAt Z`. -/
theorem num_fast (Z : ProofFile.Pub) :
    (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k)) = numAt Z := rfl

theorem arr_fast (Z : ProofFile.Pub) :
    (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
      (seatKeys (allSeatsAt Z)).length) = arrAt Z := by
  funext j t
  exact (arrOf_tab (allSeatsAt Z) j t).symm

/-- **The fast test of the first group is the slow one.** -/
theorem firstFast_eq (Z : ProofFile.Pub) (g : ℕ) :
    firstFastB Z g = firstB Z g := by
  show firstWithB Z g (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
    (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
      (seatKeys (allSeatsAt Z)).length) = _
  rw [arr_fast, num_fast]
  rfl

variable {rows cols : ℕ}

/-- **A yes of `laterFastB` gives the three conditions**, for 0 < g < 12: as `three_of_laterB`. -/
theorem three_of_laterFast (Z : ProofFile.Pub) {g : ℕ}
    (h : laterFastB Z g = true) (hg0 : 0 < g) (hg : g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * g) (p : Par) (hp : p.g = g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) :
    (SitsIn (sigListCalls (sentAt Z) rad x.link) (seatTAt Z rad x.link) (msOf (lists0At Z))
      (numbersAt Z) (2 * p.g) ∧
    SymsOne (planAt x (sentAt Z) rad (seatTAt Z rad x.link) (cutW enc wOf hRef (2 ^ kRef)) posI)
      p.hp.tl (arrAt Z) (numbersAt Z) (2 * p.g) (Meaning.sizesOf Z.p.X (2 * p.g))
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X) (2 * p.g))) ∧
    SeamFit (arrAt Z) (msOf (lists0At Z)) (numbersAt Z) (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) (sentAt Z).codes
      Z.p.X.y g := by
  have h' : laterWithB Z g (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
      (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
        (seatKeys (allSeatsAt Z)).length)
      (fun k => ((List.range 25).map fun k => (numbersAt Z).group k).getD k []) = true := h
  rw [arr_fast, num_fast] at h'
  unfold laterWithB at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a7⟩, a8⟩, a9⟩ := h'
  exact ⟨two_of_firstB Z ((firstB_with Z g).trans a0) hg x hx p hp hG rad posI oW enc wOf,
    seamFit_of_layout a1 a2 a3 (follows_sizesOf a4) (shapesTied_of_table _ rfl a5)
      (groupsSeated_of_lengths _ (seatsAsShapes_R _ _ _) _ _ a7 (groups_end Z Z.D.1)) hg0 hg a8
      a9⟩

/-! ## 4 In parts: what hangs on the group, and what does not -/

/-- **What no group's number enters**: six of the ten tests, with the tables laid once. -/
def commonFastB (Z : ProofFile.Pub) : Bool :=
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  let tbl := (List.range 25).map fun k => (numbersAt Z).group k
  (sentAt Z).codes.lengthsOk && reqShapeOk (sentAt Z).shape &&
    reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout && nmFit Z.p.X &&
    shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout
      (fun l k => keys.idxOf (0, l, k)) (fun j t => (tab.lookup (j, t)).getD keys.length)
      (lists0At Z) (fun k => tbl.getD k []) &&
    groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z)

/-- **The two tests at the seam in front of group g**, with the tables laid once. -/
def seamFastB (Z : ProofFile.Pub) (g : ℕ) : Bool :=
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  pairFit Z.p.X (2 * g) (matIx Z.p.X.y).iXI (2 * (g - 1)) (matIx Z.p.X.y).iXO &&
    seamArrB Z.p.X (Meaning.sizesOf Z.p.X) (sentAt Z).layout (fun l k => keys.idxOf (0, l, k))
      (fun j t => (tab.lookup (j, t)).getD keys.length) (numbersAt Z) (2 * g) (2 * (g - 1))
      (matIx Z.p.X.y).iXI

/-- **`SeamFit` from the common test and the seam's**, for 0 < g < 12. -/
theorem seamFit_of_parts (Z : ProofFile.Pub) {g : ℕ} (hc : commonFastB Z = true)
    (hs : seamFastB Z g = true) (hg0 : 0 < g) (hg : g < 12) :
    SeamFit (arrAt Z) (msOf (lists0At Z)) (numbersAt Z) (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) (sentAt Z).codes
      Z.p.X.y g := by
  have hc' : ((sentAt Z).codes.lengthsOk && reqShapeOk (sentAt Z).shape &&
      reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout && nmFit Z.p.X &&
      shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout
        (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
        (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
          (seatKeys (allSeatsAt Z)).length)
        (lists0At Z)
        (fun k => ((List.range 25).map fun k => (numbersAt Z).group k).getD k []) &&
      groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z)) = true := hc
  have hs' : (pairFit Z.p.X (2 * g) (matIx Z.p.X.y).iXI (2 * (g - 1)) (matIx Z.p.X.y).iXO &&
      seamArrB Z.p.X (Meaning.sizesOf Z.p.X) (sentAt Z).layout
        (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
        (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
          (seatKeys (allSeatsAt Z)).length) (numbersAt Z) (2 * g) (2 * (g - 1))
        (matIx Z.p.X.y).iXI) = true := hs
  rw [arr_fast, num_fast] at hc' hs'
  simp only [Bool.and_eq_true] at hc' hs'
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a7⟩ := hc'
  exact seamFit_of_layout a1 a2 a3 (follows_sizesOf a4) (shapesTied_of_table _ rfl a5)
    (groupsSeated_of_lengths _ (seatsAsShapes_R _ _ _) _ _ a7 (groups_end Z Z.D.1)) hg0 hg hs'.1
    hs'.2

/-! ## 5 The two structures, from the tests that can run -/

/-- **`K4PlanFit` from the three tests that can run** (the common one, the group's, the seam's), at
every family radM of the members' radii and every N' with `numbersAt Z`'s sent and index. -/
theorem k4PlanFit_fast {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (hc : commonFastB Z = true) (hf : firstFastB Z p.g = true)
    (hm : seamFastB Z p.g = true) (hg0 : 0 < p.g) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps pol KL Z.p.X)
    (B : RefPub Z.p.X p.g) (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFit (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  have T := two_of_firstB Z ((firstFast_eq Z p.g).symm.trans hf) hg x hx p rfl hG rad posI oW enc
    wOf
  planFit_carry (samePairs_R _ _ radM _) hs hi
    (planFit_of_tests x (sentAt Z) rad (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z)
      (msOf (lists0At Z)) (numbersAt Z) (2 * p.g) _ hd St B hP hG hg P0 hgr rfl hhd T.1 T.2
      (seamFit_of_parts Z hc hm hg0 hg))

/-- **`K4PlanFitF` from the one test that can run.** -/
theorem k4PlanFitF_fast {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (hf : firstFastB Z p.g = true) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps pol KL Z.p.X)
    (B : RefPub Z.p.X p.g) (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFitF (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  k4PlanFitF_closed Z radM hs hi p ((firstFast_eq Z p.g).symm.trans hf) hg x hx hG rad posI oW enc
    wOf hd St B hP P0 hgr hhd

/-! ## 6 All twelve groups in one test, every letter laid once -/

/-- The letters on the plan at link l, with D and the seats as letters. -/
def pinsCore (D : Sent) (ps : List P5T.PSeat) (l : ℕ) : PinPlan Empty :=
  ⟨D, fun _ => 0, l, fun j => P6T.seatCallsT ps D l j.val, (fun c _ _ => nomatch c),
    fun _ => (false, 0, 0)⟩

/-- `firstWithB` with D, the seats, N, the members and X as letters. -/
def firstCoreB (D : Sent) (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem) (X : Public) (g : ℕ)
    (num arr : ℕ → ℕ → ℕ) : Bool :=
  sitsInB (sigListCalls D (fun _ => 0) (2 * g)) (pinsCore D ps (2 * g)).seatT ms N (2 * g) &&
    (List.range (Meaning.sizesOf X (2 * g)).NM).all fun μ =>
      symTieB (pinsCore D ps (2 * g)) num arr N (2 * g) (Meaning.tlAt X (2 * g)) X
        (Meaning.sizesOf X) μ

/-- `commonFastB`'s six with their letters. -/
def commonCoreB (D : Sent) (N : Numbers) (L : MemberLists) (X : Public) (n : ℕ)
    (num arr : ℕ → ℕ → ℕ) (grp : ℕ → List (ℕ × ℕ)) : Bool :=
  D.codes.lengthsOk && reqShapeOk D.shape && reqLayoutOk D.codes D.shape D.layout && nmFit X &&
    shapesTiedB D.codes D.shape D.layout num arr L grp && groupsAreMembers N n L

/-- `seamFastB`'s two with their letters. -/
def seamCoreB (D : Sent) (N : Numbers) (X : Public) (g : ℕ) (num arr : ℕ → ℕ → ℕ) : Bool :=
  pairFit X (2 * g) (matIx X.y).iXI (2 * (g - 1)) (matIx X.y).iXO &&
    seamArrB X (Meaning.sizesOf X) D.layout num arr N (2 * g) (2 * (g - 1)) (matIx X.y).iXI

/-- **ALL 24 CLOSED TESTS IN ONE, EVERY LETTER LAID ONCE**: a function of Z alone. -/
def allFastB (Z : ProofFile.Pub) : Bool :=
  let D := sentAt Z
  let ps := seatsAt Z
  let N := numbersAt Z
  let L := lists0At Z
  let ms := msOf L
  let X := Z.p.X
  let keys := seatKeys (allSeatsAt Z)
  let tab := arrTab keys (allSeatsAt Z)
  let tbl := (List.range 25).map fun k => N.group k
  let num : ℕ → ℕ → ℕ := fun l k => keys.idxOf (0, l, k)
  let arr : ℕ → ℕ → ℕ := fun j t => (tab.lookup (j, t)).getD keys.length
  commonCoreB D N L X (lastAt Z) num arr (fun k => tbl.getD k []) &&
    ((List.range 12).all fun g => firstCoreB D ps N ms X g num arr) &&
    (List.range 11).all fun i => seamCoreB D N X (i + 1) num arr

/-- **It is the 24, by unfolding.** -/
theorem allFast_eq (Z : ProofFile.Pub) :
    allFastB Z = (commonFastB Z && ((List.range 12).all fun g => firstFastB Z g) &&
      (List.range 11).all fun i => seamFastB Z (i + 1)) := rfl

/-- **One yes gives each of the 24.** -/
theorem parts_of_all (Z : ProofFile.Pub) (h : allFastB Z = true) :
    commonFastB Z = true ∧ (∀ g, g < 12 → firstFastB Z g = true) ∧
      ∀ g, 0 < g → g < 12 → seamFastB Z g = true := by
  rw [allFast_eq, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨h.1.1, fun g hg => h.1.2 g (List.mem_range.2 hg), fun g h0 hg => ?_⟩
  have e := h.2 (g - 1) (List.mem_range.2 (by omega))
  rwa [show g - 1 + 1 = g by omega] at e

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.lookup_tab
#print axioms OnBytes.Road.K4.arrOf_tab
#print axioms OnBytes.Road.K4.firstB_with
#print axioms OnBytes.Road.K4.laterB_with
#print axioms OnBytes.Road.K4.arr_fast
#print axioms OnBytes.Road.K4.firstFast_eq
#print axioms OnBytes.Road.K4.three_of_laterFast
#print axioms OnBytes.Road.K4.seamFit_of_parts
#print axioms OnBytes.Road.K4.k4PlanFit_fast
#print axioms OnBytes.Road.K4.k4PlanFitF_fast
#print axioms OnBytes.Road.K4.allFast_eq
#print axioms OnBytes.Road.K4.parts_of_all
