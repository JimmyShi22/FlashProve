-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanClosed.lean: THE TESTS OF Johnson/Road/K4/K4PlanTests.lean AS ONE TEST WITH
CODE A GROUP THAT IS A FUNCTION OF Z (what follows from the public files) AND THE GROUP's NUMBER g
ALONE; and the law: its yes gives `SitsIn`, `SymsOne`, `SeamFit` at every place x with x.link = 2 g,
all parameters p of K4's sub-protocol with p.g = g whose plan is the public parameters' own, ALL
radii of the caller's list, and all of the letters that no test reads; and the two structures
besides at ALL radii of the members and every N' with the same sent and index. The letters are
those of Johnson/Road/K4/K4PlanAt.lean: no raw file is read a
second time; `seatsAsShapesB` is a theorem at them and no conjunct. Three definitions with
code and ten theorems. Glue; no draw, no count.

  THE THREE SMALL LAWS.
  `calls_fst`, `calls_len`, `calls_get_fst`: the caller's list at two families of radii has the same
    shapes in the same order.
  `sitsIn_rad`: `SitsIn` does not hang on the radii, where the seats are a function of the member's
    number.
  `symsOne_any`: `SymsOne` hangs on D, the link and the seats as a function of the member's number
    alone: not on the radii, not on the type of the committed table's cells, not on rc or posI.
  `tlAt_even`: the approximate range proof's public parameters of sub-proof 2 g are the group's
    plan's.

  THE CLOSED TESTS.
  `pinsZero Z l`: the letters on the plan at link l, at the radii 0 and the empty type of cells.
  `firstB Z g`: `sitsInB` and `symTieB` at every matrix: what the first group asks.
  `laterB Z g`: these and eight others of `K4PlanTests`; the eleventh is a theorem here.
  `two_of_firstB`: a yes of `firstB` gives `SitsIn` and `SymsOne`.
  `three_of_laterB`: a yes of `laterB`, 0 < g < 12, gives these and `SeamFit`.
  `k4PlanFit_closed`, `k4PlanFitF_closed`: so `K4PlanFit` (Johnson/Road/K4/K4PinsEnd.lean) and
    `K4PlanFitF` (K4PinsEndFirst.lean) from ONE yes each, and what is no test: `PublicSteps`,
    `RefPub`, the two lines on p, `PlaceIs x p 0`, x.link = 2 p.g and two lines on numbers.

KIN: `digList_fst`, `digB_rad` (Johnson/Desc/First/Look/K3DigRows.lean) say the like of the
digits' list; of the calls' list nothing shown here says it.

Limits. K04_law IS NOT PROVED BY THIS. NO RUN IS A PART OF THIS FILE. The letters are those of
Johnson/Road/K4/K4PlanAt.lean, with that file's limits. AT A NUMBER g THAT IS NO GROUP's `firstB`
CAN SAY YES OF NOTHING: `Meaning.tlAt X (2 g)` is then the empty default, with no matrix to ask: no
count is in the test: the laws take X.G[p.g]? = some p.hp beside the yes. BESIDE THE ONE YES each of
the two last laws takes premises that are no test: `PublicSteps` and `RefPub` among them. `arrAt Z`
and `numAt Z` make their list of keys anew at every call: as typed these tests are slow:
Johnson/Road/K4/K4PlanFast.lean.
-/
import Johnson.Road.K4.K4PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.First (Numbers groupsAreMembers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (Mem msOf)
open Johnson.Road.K4.LayoutTies (shapesTiedB shapesTied_of_B)
open Meaning (nmFit pairFit seatBy fLay follows_sizesOf)
open Cb.Pv.Tail (Size)
open Inst.Model.Layout (kRef hRef)

/-! ## 1 The radii -/

section
variable (D : Sent) (rad rad' : OnBytes.OracleShape → ℕ) (i : ℕ)

/-- The caller's list at two families of radii: the same shapes in the same order. -/
theorem calls_fst :
    (sigListCalls D rad i).map Prod.fst = (sigListCalls D rad' i).map Prod.fst := by
  unfold sigListCalls sigList
  simp only [List.map_append, List.map_map]
  rfl

theorem calls_len : (sigListCalls D rad i).length = (sigListCalls D rad' i).length := by
  have e := congrArg List.length (calls_fst D rad rad' i)
  rwa [List.length_map, List.length_map] at e

theorem calls_get_fst {k : ℕ} (h : k < (sigListCalls D rad i).length)
    (h' : k < (sigListCalls D rad' i).length) :
    ((sigListCalls D rad i).get ⟨k, h⟩).1 = ((sigListCalls D rad' i).get ⟨k, h'⟩).1 := by
  have e : ((sigListCalls D rad i).map Prod.fst)[k]? =
      ((sigListCalls D rad' i).map Prod.fst)[k]? := by rw [calls_fst D rad rad' i]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem h'] at e
  exact Option.some.inj e

/-- **`SitsIn` does not hang on the radii.** f: the seat of a member, by its number. -/
theorem sitsIn_rad (f : ℕ → ℕ × ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (h : SitsIn (sigListCalls D rad i) (fun j => f j.val) ms N m) :
    SitsIn (sigListCalls D rad' i) (fun j => f j.val) ms N m := by
  intro j
  have hj : j.val < (sigListCalls D rad i).length := by
    rw [calls_len D rad rad' i]
    exact j.isLt
  obtain ⟨h1, u, hu, e⟩ := h ⟨j.val, hj⟩
  exact ⟨h1, u, hu, e.trans (calls_get_fst D rad rad' i hj j.isLt)⟩

/-- **`SymsOne` hangs on D, the link and the seats by number alone.** -/
theorem symsOne_any {C C' : Type} (f : ℕ → ℕ × ℕ) (rc : C → ℕ → ℕ → Cb.Gl.E)
    (rc' : C' → ℕ → ℕ → Cb.Gl.E) (posI posI' : ℕ → Bool × ℕ × ℕ) (tl : HTailF2)
    (arr : ℕ → ℕ → ℕ) (N : Numbers) (k : ℕ) (sz : Size)
    (seat' : Fin sz.NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (h : SymsOne (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) tl arr N k sz seat') :
    SymsOne (⟨D, rad', i, fun j => f j.val, rc', posI'⟩ : PinPlan C') tl arr N k sz seat' := by
  intro μ r c
  obtain ⟨s, hk, e1, e2, e3, e4, e5, e6⟩ := h μ r c
  have hk0 : s.msg < (sigListCalls D rad i).length := hk
  have hk' : s.msg < (sigListCalls D rad' i).length := by
    rw [← calls_len D rad rad' i]
    exact hk0
  have eg := calls_get_fst D rad rad' i hk0 hk'
  refine ⟨s, hk', e1, e2, ?_, ?_, e5, e6⟩
  · show s.row < ((sigListCalls D rad' i).get ⟨s.msg, hk'⟩).1.mainRows
    rw [← eg]
    exact e3
  · show s.place < (Johnson.Pack.pMain D.codes ((sigListCalls D rad' i).get ⟨s.msg, hk'⟩).1).ell
    rw [← eg]
    exact e4

end

/-- The public parameters of the approximate range proof of sub-proof 2 g are the group's plan's. -/
theorem tlAt_even {X : Public} {g : ℕ} (hg : g < 12) {P : Model.Layer.HPlan2}
    (h : X.G[g]? = some P) : Meaning.tlAt X (2 * g) = P.tl := by
  unfold Meaning.tlAt
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, h]
  rfl

/-! ## 2 The closed tests -/

/-- The letters on the plan at link l, at the radii 0 and the empty type of cells. -/
def pinsZero (Z : ProofFile.Pub) (l : ℕ) : PinPlan Empty :=
  ⟨sentAt Z, fun _ => 0, l, fun j => P6T.seatCallsT (seatsAt Z) (sentAt Z) l j.val,
    (fun c _ _ => nomatch c), fun _ => (false, 0, 0)⟩

/-- **What the first group asks**, as a function of Z and g. -/
def firstB (Z : ProofFile.Pub) (g : ℕ) : Bool :=
  sitsInB (sigListCalls (sentAt Z) (fun _ => 0) (2 * g)) (pinsZero Z (2 * g)).seatT
      (msOf (lists0At Z)) (numbersAt Z) (2 * g) &&
    (List.range (Meaning.sizesOf Z.p.X (2 * g)).NM).all fun μ =>
      symTieB (pinsZero Z (2 * g)) (numAt Z) (arrAt Z) (numbersAt Z) (2 * g)
        (Meaning.tlAt Z.p.X (2 * g)) Z.p.X (Meaning.sizesOf Z.p.X) μ

/-- **What a later group asks.** -/
def laterB (Z : ProofFile.Pub) (g : ℕ) : Bool :=
  firstB Z g && (sentAt Z).codes.lengthsOk && reqShapeOk (sentAt Z).shape &&
    reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout && nmFit Z.p.X &&
    shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout (numAt Z) (arrAt Z)
      (lists0At Z) (fun k => (numbersAt Z).group k) &&
    groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z) &&
    pairFit Z.p.X (2 * g) (matIx Z.p.X.y).iXI (2 * (g - 1)) (matIx Z.p.X.y).iXO &&
    seamArrB Z.p.X (Meaning.sizesOf Z.p.X) (sentAt Z).layout (numAt Z) (arrAt Z) (numbersAt Z)
      (2 * g) (2 * (g - 1)) (matIx Z.p.X.y).iXI

variable {rows cols : ℕ}

/-- **A yes of `firstB` gives `SitsIn` and `SymsOne`**, at every place of link 2 g, all parameters
of group g with the public parameters' own plan, all radii and all letters that no test reads. -/
theorem two_of_firstB (Z : ProofFile.Pub) {g : ℕ} (h : firstB Z g = true)
    (hg : g < 12) (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * g) (p : Par)
    (hp : p.g = g) (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ)
    (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) :
    SitsIn (sigListCalls (sentAt Z) rad x.link) (seatTAt Z rad x.link) (msOf (lists0At Z))
      (numbersAt Z) (2 * p.g) ∧
    SymsOne (planAt x (sentAt Z) rad (seatTAt Z rad x.link) (cutW enc wOf hRef (2 ^ kRef)) posI)
      p.hp.tl (arrAt Z) (numbersAt Z) (2 * p.g) (Meaning.sizesOf Z.p.X (2 * p.g))
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X) (2 * p.g)) := by
  subst hp
  unfold firstB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e : Meaning.tlAt Z.p.X (2 * p.g) = p.hp.tl := tlAt_even hg hG
  rw [e] at h2
  have S0 := sitsIn_of_B h1
  have Y0 := symsOne_of_layout (pinsZero Z (2 * p.g)) (numAt Z) (arrAt Z) (numbersAt Z) (2 * p.g)
    p.hp.tl (X := Z.p.X) (s := Meaning.sizesOf Z.p.X) rfl fun μ hμ =>
      List.all_eq_true.1 h2 μ (List.mem_range.2 hμ)
  unfold planAt seatTAt
  rw [hx]
  exact ⟨sitsIn_rad (sentAt Z) (fun _ => 0) rad (2 * p.g)
      (P6T.seatCallsT (seatsAt Z) (sentAt Z) (2 * p.g)) _ _ _ S0,
    symsOne_any (sentAt Z) (fun _ => 0) rad (2 * p.g)
      (P6T.seatCallsT (seatsAt Z) (sentAt Z) (2 * p.g)) _ _ _ _ _ _ _ _ _ _ Y0⟩

/-- **A yes of `laterB` gives the three conditions**, for 0 < g < 12. -/
theorem three_of_laterB (Z : ProofFile.Pub) {g : ℕ} (h : laterB Z g = true)
    (hg0 : 0 < g) (hg : g < 12) (x : VerifiableInference.Desc.First.Look.Place)
    (hx : x.link = 2 * g) (p : Par) (hp : p.g = g) (hG : Z.p.X.G[p.g]? = some p.hp)
    (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) :
    (SitsIn (sigListCalls (sentAt Z) rad x.link) (seatTAt Z rad x.link) (msOf (lists0At Z))
      (numbersAt Z) (2 * p.g) ∧
    SymsOne (planAt x (sentAt Z) rad (seatTAt Z rad x.link) (cutW enc wOf hRef (2 ^ kRef)) posI)
      p.hp.tl (arrAt Z) (numbersAt Z) (2 * p.g) (Meaning.sizesOf Z.p.X (2 * p.g))
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X) (2 * p.g))) ∧
    SeamFit (arrAt Z) (msOf (lists0At Z)) (numbersAt Z) (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) (sentAt Z).codes
      Z.p.X.y g := by
  unfold laterB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a7⟩, a8⟩, a9⟩ := h
  exact ⟨two_of_firstB Z a0 hg x hx p hp hG rad posI oW enc wOf,
    seamFit_of_layout a1 a2 a3 (follows_sizesOf a4) (shapesTied_of_B a5)
      (groupsSeated_of_lengths _ (seatsAsShapes_R _ _ _) _ _ a7 (groups_end Z Z.D.1)) hg0 hg a8
      a9⟩

/-! ## 3 The two structures, from one test each -/

/-- **`K4PlanFit` from one yes of `laterB`**, at every family radM of the members' radii and every
N' with `numbersAt Z`'s sent and index; beside the yes: what `planFit_of_tests` takes beside the
three conditions. -/
theorem k4PlanFit_closed {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (h : laterB Z p.g = true) (hg0 : 0 < p.g) (hg : p.g < 12)
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
  have T := three_of_laterB Z h hg0 hg x hx p rfl hG rad posI oW enc wOf
  planFit_carry (samePairs_R _ _ radM _) hs hi
    (planFit_of_tests x (sentAt Z) rad (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z)
      (msOf (lists0At Z)) (numbersAt Z) (2 * p.g) _ hd St B hP hG hg P0 hgr rfl hhd T.1.1 T.1.2
      T.2)

/-- **`K4PlanFitF` from one yes of `firstB`**, likewise. -/
theorem k4PlanFitF_closed {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (h : firstB Z p.g = true) (hg : p.g < 12)
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
  planFitF_carry (samePairs_R _ _ radM _) hs hi
    { sits := (two_of_firstB Z h hg x hx p rfl hG rad posI oW enc wOf).1
      covers := covers_top p.hp.tl
      place := P0
      keys := keysFit_at_pub St B hP hG hgr
      size := size_sizesOf hG hg
      syms := (two_of_firstB Z h hg x hx p rfl hG rad posI oW enc wOf).2
      segment := rfl
      notHead := hhd }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.calls_get_fst
#print axioms OnBytes.Road.K4.sitsIn_rad
#print axioms OnBytes.Road.K4.symsOne_any
#print axioms OnBytes.Road.K4.tlAt_even
#print axioms OnBytes.Road.K4.two_of_firstB
#print axioms OnBytes.Road.K4.three_of_laterB
#print axioms OnBytes.Road.K4.k4PlanFit_closed
#print axioms OnBytes.Road.K4.k4PlanFitF_closed
