-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLaid.lean: the public records on the output head's sub-proof, as conclusions from
the verifier's own functions.

Johnson/Road/HeadLines.lean states what the forms of the head's lookup keys are worth under records
of hypotheses on public numbers: Laid (the layout's numbers), ReqFits (the request as the library's
record), SegHas and SegFit (a segment's columns). This file shows the first three, and the public
half of the fourth, of what the verifier's functions return.

How. The functions layout, numbers, stFromCall and coveredOf of OnBytes/Model/HeadLayout.lean are
blocks of tests, each of which refuses or goes on. If a block returns a value, every test has gone
on, and the value is the record that the block's last line writes out.

Main definitions: AdmittedH (what is used of a layout that the verifier returns); SegLaid (the
public half of SegFit).
Main theorems:
 - admittedH_of_layout, laid_of_layout: every layout that the function layout returns, if no column
   stands behind the vocabulary (JV = V), has the record Laid at the sizes 2^lt, d, V, JVa.
   AdmittedH.JV_iff: JV = V if and only if a block's features divide V. laid_ref: at 2^10 positions,
   width 5,120 and 202,048 entries the record holds at the library's sizes.
   layout_of_public: the head's layout in what publicOf (OnBytes/Model/VerifyPublic.lean) returns
   is what layout returns for the head's shape there and the layers' table of the clamp.
 - stFromCall_ok, coveredOf_ok: what the two functions on a request return.
 - reqFits_of_covered: a request of the library with the r and e of the request file's words, the
   file's next token at each covered position below the last, and the prover's token at the last
   position if that is covered, has the record ReqFits; for any sizes with the same number of
   positions.
 - reqFits_of_instance: so have the two terms at which the library's theorems read an instance with
   the file's tokens, r and e and the prover's token, at the library's sizes.
 - instance_of_covered: such an instance exists, if the prover's token is below the vocabulary's
   size.
 - alike_of_reqFits: two requests with the record ReqFits of one run cover the same positions and
   check the same tokens there (HeadReq.Alike).
 - lineSegs_spec, callsFrom_spec, callsOf_spec, seg_of_admitted: each of the nine names of the
   head's list of segments has a call and a segment there, placed by the rule of
   OnBytes/Model/Calls.lean, with the list's length.
 - segHas_of_layout, row_of_layout: so it has the record SegHas. segLaid_of_layout, eight_of_layout:
   a segment whose length is a whole number of blocks is aligned on blocks (place_aligned of
   Johnson/Road/FormsKeysPlace.lean), in a call with at least a block's columns: the eight segments
   but the ledger's.
 - SegLaid.fit: with two hypotheses on the call's point, the record SegFit.

What is not claimed. The half of SegFit on the call's point (its number of coordinates; that its
last coordinates are the block's) and the record PosFit are not shown: they come from tests on
values that the verifier makes when it runs. That the functions return a value for some shape or
request is not shown here: every theorem begins "if it does". Nothing is said on the prover's token
but that it is a number; that it is the reply which the caller was given is another test's. The
program does not import this file.
-/
import Johnson.Road.HeadLines
import Johnson.Road.HeadReq
import Johnson.Road.FormsKeysLaid
import OnBytes.Model.VerifyPublic

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open HeadSizes (Sizes)

/-! ## A block of tests that returns a value -/

/-- A test that goes on has found its condition true. -/
theorem true_of_needed {b : Bool} {n : String} {a : Unit} (h : Model.Head.needed b n = .ok a) :
    b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- If a test and what follows it return a value, the test's condition is true, and what follows
returns the value. -/
theorem ok_of_needed {β : Type} {b : Bool} {n : String} {f : Unit → Except String β} {y : β}
    (h : (Model.Head.needed b n >>= f) = .ok y) : b = true ∧ f () = .ok y := by
  obtain ⟨a, h1, h2⟩ := ok_of_bind h
  exact ⟨true_of_needed h1, h2⟩

/-- If "both conditions" is true, each is. -/
theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- If "neither condition" is true, both are false. -/
theorem nor_true_split {a b : Bool} (h : (!(a || b)) = true) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- A choice by a Boolean value that is true exactly if p holds is the choice by p. -/
theorem ite_bool_iff {α : Type} {b : Bool} {p : Prop} [Decidable p] (h : b = true ↔ p) (x y : α) :
    (if b then x else y) = if p then x else y := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.2 hp)]
  · rw [if_neg hp, if_neg fun hb => hp (h.1 hb)]

/-! ## The layout -/

/-- What is used of a layout that the verifier has returned for the shape h. -/
structure AdmittedH (h : Model.Head.Shape) (L : Model.Head.HL) : Prop where
  /-- the tests on the shape's words -/
  adm : Model.Head.admitted h = true
  /-- the vocabulary's size, rounded up to whole blocks -/
  JV : L.JV = Model.roundUp h.V h.S2
  JVa : L.JVa = 2 ^ (ceilLog2 L.JV - 1)
  /-- the first of the two segments of table values is made of whole blocks -/
  SVa : h.S2 ∣ L.JVa
  oAw : L.oAw = 0
  oRa : L.oRa = 2 * h.d
  oD1 : L.oD1 = 4 * h.d
  oD2 : L.oD2 = 4 * h.d + 2 * L.JV
  oE : L.oE = 4 * h.d + 3 * L.JV
  /-- the calls are those that callsOf returns, and the tests on their sizes have gone on -/
  calls : ∃ cs, Model.Head.callsOf h L = .ok cs ∧ Model.Head.callSizes h cs = .ok () ∧
    L.calls = cs.toArray

/-- Every layout that the verifier returns is admitted. -/
theorem admittedH_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : AdmittedH h L := by
  unfold Model.Head.layout at hy
  obtain ⟨e1, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, hn, hy⟩ := ok_of_bind hy
  obtain ⟨cs, hc, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨u, hs, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  unfold Model.Head.numbers at hn
  obtain ⟨e2, hn⟩ := ok_of_needed hn
  obtain ⟨-, hn⟩ := ok_of_needed hn
  cases hn
  exact {
    adm := e1
    JV := rfl
    JVa := rfl
    SVa := dvd_of_bne (nor_true_split e2).1
    oAw := rfl
    oRa := rfl
    oD1 := rfl
    oD2 := rfl
    oE := rfl
    calls := ⟨cs, hc, hs, rfl⟩ }

/-- A number rounded up to a multiple of w is a multiple of w. -/
theorem dvd_roundUp (x w : ℕ) : w ∣ Model.roundUp x w := Nat.dvd_mul_left w _

/-- The last of the tests on the shape's words: a block's features divide the width. -/
theorem AdmittedH.Sd {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L) :
    h.S2 ∣ h.d := by
  have e := A.adm
  unfold Model.Head.admitted at e
  exact Nat.dvd_of_mod_eq_zero (eq_of_beq (and_true_split e).2)

/-- Three more of these tests: the bounds on the width, on the rows of a block and on the
vocabulary. -/
theorem AdmittedH.bounds {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L) :
    h.d ≤ 2 ^ 20 ∧ h.la ≤ 16 ∧ h.V ≤ 2 ^ 24 := by
  have e := A.adm
  unfold Model.Head.admitted at e
  have p17 := and_true_split e
  have p16 := and_true_split p17.1
  have p15 := and_true_split p16.1
  have p14 := and_true_split p15.1
  have p13 := and_true_split p14.1
  have p12 := and_true_split p13.1
  have p11 := and_true_split p12.1
  have p10 := and_true_split p11.1
  have p9 := and_true_split p10.1
  have p8 := and_true_split p9.1
  have p7 := and_true_split p8.1
  have p6 := and_true_split p7.1
  have p5 := and_true_split p6.1
  have p4 := and_true_split p5.1
  exact ⟨of_decide_eq_true p4.2, of_decide_eq_true p6.2, of_decide_eq_true p14.2⟩

/-- **Every layout that the verifier returns, with no column behind the vocabulary, has the record
Laid**, at the sizes 2^lt, d, V, JVa. -/
theorem laid_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) (hV : L.JV = h.V) {R : Model.Head.Run}
    (e1 : R.h = h) (e2 : R.L = L) : Laid R ⟨2 ^ h.lt, h.d, h.V, L.JVa⟩ := by
  have A := admittedH_of_layout hy
  subst e1 e2
  exact {
    T := rfl
    d := rfl
    V := rfl
    JV := hV
    JVa := rfl
    oAw := A.oAw
    oRa := A.oRa
    oD1 := A.oD1
    oD2 := by
      have e := A.oD2
      rw [hV] at e
      exact e
    oE := by
      have e := A.oE
      rw [hV] at e
      exact e
    Sd := A.Sd
    SV := by
      have e := dvd_roundUp R.h.V R.h.S2
      rw [← A.JV, hV] at e
      exact e }

/-- If either of two steps, chosen by a condition, and one continuation return a value, the
continuation returns it on some value. -/
theorem ok_of_ite {c : Prop} [Decidable c] {α β : Type} {x x' : Except String α}
    {jp : α → Except String β} {y : β} (h : (if c then x >>= jp else x' >>= jp) = .ok y) :
    ∃ a, jp a = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩
  · rw [if_neg hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩

/-- The same where the first branch has two steps. -/
theorem ok_of_ite2 {c : Prop} [Decidable c] {α β γ : Type} {x : Except String γ}
    {g : γ → Except String α} {x' : Except String α} {jp : α → Except String β} {y : β}
    (h : (if c then x >>= fun a => g a >>= jp else x' >>= jp) = .ok y) : ∃ a, jp a = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    obtain ⟨b, -, h⟩ := ok_of_bind h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩
  · rw [if_neg hc] at h
    obtain ⟨a, -, h⟩ := ok_of_bind h
    exact ⟨a, h⟩

/-- **The head's layout in the verifier's public part is what the function layout returns** for the
head's shape there and the clamp's table of the layers' layout. P, y: the parameter file as read,
and the layers' layout. -/
theorem layout_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) :
    ∃ P y, Model.Verify.polLayout pol = .ok (P, y) ∧ X.hS = Model.Verify.headShape P y ∧
      Model.Head.layout X.hS y.tauFC = .ok X.HLy := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  exact ⟨P, y, hpl, rfl, by assumption⟩

/-! ## The request -/

/-- Member i of the array of the values of f at 0 to n - 1. -/
theorem getD_rangeMap {α : Type} (f : ℕ → α) (n : ℕ) (d : α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  simp [Array.getD, hi]

/-- Writing at one index leaves the others. -/
theorem getD_setOther (a : Array ℕ) {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (a.setIfInBounds i x).getD j 0 = a.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- What has been written at an index within the array is read there. -/
theorem getD_setSame (a : Array ℕ) {i : ℕ} (h : i < a.size) (x : ℕ) :
    (a.setIfInBounds i x).getD i 0 = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- An entry of the first b members of an array. -/
theorem getD_firstOf {α : Type} (z : Array α) {b j : ℕ} (hb : b ≤ z.size) (hj : j < b) (d : α) :
    (z.extract 0 b).getD j d = z.getD j d := by
  have h2 : j < z.size := by omega
  simp [Array.getD, hj, h2]

/-- What stFromCall returns: the request's words as they are, r and e from the two words behind the
tokens, the reply from the reply's word. -/
theorem stFromCall_ok {P Q : Array UInt32} {T : ℕ} {so : Model.Head.StOwn}
    (h : Model.Head.stFromCall P Q T = .ok so) :
    so.req = P ∧ so.r = (P.getD T 0).toNat ∧ so.e = (P.getD (T + 1) 0).toNat ∧
      so.y = (Q.getD 0 0).toNat := by
  unfold Model.Head.stFromCall at h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- What coveredOf returns, with r and e for the two words behind the tokens. -/
theorem coveredOf_ok {so : Model.Head.StOwn} {T V : ℕ} {cov : Model.Head.Covered}
    (h : Model.Head.coveredOf so T V = .ok cov) :
    so.req.size = T + 2 ∧
    (((so.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true ∧
    (so.req.getD T 0).toNat < (so.req.getD (T + 1) 0).toNat ∧
    (so.req.getD (T + 1) 0).toNat ≤ T ∧
    cov.hOn = (Array.range T).map (fun t =>
      decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) ∧
    cov.hWin = (Array.range T).map (fun t =>
      if (decide ((so.req.getD T 0).toNat ≤ t) &&
          decide (t < (so.req.getD (T + 1) 0).toNat)) = true then
        (if t + 1 < T then ((so.req.extract 0 T).map (·.toNat)).getD (t + 1) 0 else so.y)
      else 0) ∧
    cov.hOnC = (Array.range T).map (fun t =>
      (decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) &&
        decide (t + 1 < T)) := by
  unfold Model.Head.coveredOf at h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨e2, h⟩ := ok_of_needed h
  obtain ⟨e3, h⟩ := ok_of_needed h
  obtain ⟨e4, h⟩ := ok_of_needed h
  cases h
  have a := nor_true_split e4
  exact ⟨eq_of_beq e2, e3, Nat.not_le.mp (of_decide_eq_false a.1),
    Nat.not_lt.mp (of_decide_eq_false a.2), rfl, rfl, rfl⟩

/-- **The request as the library's record.** y has the r and e of the request's words; at a covered
position below the last it checks the request's next token; at the last position, if that is
covered, the token that the prover has named. -/
theorem reqFits_of_covered {so : Model.Head.StOwn} {T V : ℕ} {cov : Model.Head.Covered}
    (hc : Model.Head.coveredOf so T V = .ok cov) {R : Model.Head.Run} (e1 : R.cov = cov)
    {yTok : ℕ} (e2 : R.x.win = Model.Head.winOf cov T yTok) {z : Sizes} (hz : z.T = T)
    {y : Inst.Model.Head.Req} (hr : y.r = (so.req.getD T 0).toNat)
    (he : y.e = (so.req.getD (T + 1) 0).toNat)
    (hw : ∀ i, i + 1 < T → y.r ≤ i → i < y.e → y.win i = (so.req.getD (i + 1) 0).toNat)
    (hl : y.r ≤ T - 1 → T - 1 < y.e → y.win (T - 1) = yTok) : ReqFits R z y := by
  obtain ⟨hsz, -, -, -, hOn, hWin, hOnC⟩ := coveredOf_ok hc
  subst e1
  have on_iff : ∀ i, (decide ((so.req.getD T 0).toNat ≤ i) &&
      decide (i < (so.req.getD (T + 1) 0).toNat)) = true ↔ y.r ≤ i ∧ i < y.e := by
    intro i
    rw [hr, he]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hon : ∀ i, i < T → (R.cov.hOn.getD i false = true ↔ y.r ≤ i ∧ i < y.e) := by
    intro i hi
    rw [hOn, getD_rangeMap _ _ _ hi]
    exact on_iff i
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi ho => ?_⟩
  · rw [hz] at hi
    unfold Inst.Model.Head.Req.rho
    exact (ite_bool_iff (hon i hi) 1 0).symm
  · rw [hz] at hi
    unfold HeadSizes.rhoC
    refine (ite_bool_iff ?_ 1 0).symm
    rw [hOnC, getD_rangeMap _ _ _ hi, Bool.and_eq_true, on_iff i, decide_eq_true_eq, hz]
    constructor
    · intro k
      omega
    · intro k
      omega
  · rw [hz] at hi
    have hcv := (hon i hi).1 ho
    have hsW : R.cov.hWin.size = T := by
      rw [hWin, Array.size_map, Array.size_range]
    rw [e2]
    unfold Model.Head.winOf
    by_cases hlast : i + 1 < T
    · have hne : T - 1 ≠ i := by omega
      have e3 : (if R.cov.hOn.getD (T - 1) false = true then
          R.cov.hWin.setIfInBounds (T - 1) yTok else R.cov.hWin).getD i 0 =
          R.cov.hWin.getD i 0 := by
        split
        · exact getD_setOther _ hne _
        · rfl
      rw [e3, hWin, getD_rangeMap _ _ _ hi, if_pos ((on_iff i).2 hcv), if_pos hlast,
        getD_map_lt _ _ (by rw [Array.size_extract]; omega) 0 0,
        getD_firstOf _ (by omega) hlast]
      exact hw i hlast hcv.1 hcv.2
    · have ei : i = T - 1 := by omega
      subst ei
      rw [if_pos ho, getD_setSame _ (by omega)]
      exact hl hcv.1 hcv.2

/-- **The two terms at which the library's theorems read an instance have the record**, at the
library's sizes: for an instance with the file's tokens, r and e, and the prover's token as y. -/
theorem reqFits_of_instance {P Q : Array UInt32} {so : Model.Head.StOwn}
    {cov : Model.Head.Covered} (hs : Model.Head.stFromCall P Q 1024 = .ok so) {V : ℕ}
    (hc : Model.Head.coveredOf so 1024 V = .ok cov) {R : Model.Head.Run} (e1 : R.cov = cov)
    {yTok : ℕ} (e2 : R.x.win = Model.Head.winOf cov 1024 yTok)
    (x : Inst.Model.Instance Inst.Model.ppref) (hr : x.r = so.r) (he : x.e = so.e)
    (hp : ∀ t (ht : t < Inst.Model.ppref.T), (x.prompt ⟨t, ht⟩).val = (P.getD t 0).toNat)
    (hy : x.y.val = yTok) :
    ReqFits R HeadSizes.ref (Cm.reqOf x) ∧
      ∀ pol, ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pol x) := by
  obtain ⟨q1, q2, q3, -⟩ := stFromCall_ok hs
  have hw : ∀ i, i + 1 < 1024 → x.w i = (so.req.getD (i + 1) 0).toNat := by
    intro i hi
    unfold Inst.Model.Instance.w Inst.Model.Instance.tok
    rw [dif_pos (show i + 1 < Inst.Model.ppref.T from hi), hp, q1]
  have hl : x.w (1024 - 1) = yTok := (x.w_last (by decide)).trans hy
  have k1 : x.r = (so.req.getD 1024 0).toNat := by rw [hr, q2, q1]
  have k2 : x.e = (so.req.getD (1024 + 1) 0).toNat := by rw [he, q3, q1]
  exact ⟨reqFits_of_covered hc e1 e2 rfl k1 k2 (fun i hi _ _ => hw i hi) (fun _ _ => hl),
    fun _ => reqFits_of_covered hc e1 e2 rfl k1 k2 (fun i hi _ _ => hw i hi) (fun _ _ => hl)⟩

/-- Two requests with the record of one run are alike. -/
theorem alike_of_reqFits {R : Model.Head.Run} {y y' : Inst.Model.Head.Req}
    (h : ReqFits R HeadSizes.ref y) (h' : ReqFits R HeadSizes.ref y') : HeadReq.Alike y y' := by
  refine ⟨fun i hi => (h.rho i hi).trans (h'.rho i hi).symm, fun i hi h1 => ?_⟩
  have ho : R.cov.hOn.getD i false = true := by
    have e := h.rho i hi
    rw [h1] at e
    by_contra hn
    rw [if_neg hn] at e
    exact absurd e (by norm_num)
  exact (h.win i hi ho).trans (h'.win i hi ho).symm

/-- **Such an instance exists**: the tests of coveredOf put every token below the vocabulary's size
and r and e at most at the number of positions. -/
theorem instance_of_covered {P Q : Array UInt32} {so : Model.Head.StOwn}
    {cov : Model.Head.Covered} (hs : Model.Head.stFromCall P Q 1024 = .ok so)
    (hc : Model.Head.coveredOf so 1024 202048 = .ok cov) {yTok : ℕ} (hy : yTok < 202048) :
    ∃ x : Inst.Model.Instance Inst.Model.ppref, x.r = so.r ∧ x.e = so.e ∧
      (∀ t (ht : t < Inst.Model.ppref.T), (x.prompt ⟨t, ht⟩).val = (P.getD t 0).toNat) ∧
      x.y.val = yTok := by
  obtain ⟨q1, q2, q3, -⟩ := stFromCall_ok hs
  obtain ⟨hsz, hall, hre, heT, -⟩ := coveredOf_ok hc
  rw [q1] at hsz hall hre heT
  have htok : ∀ t, t < 1024 → (P.getD t 0).toNat < 202048 := by
    intro t ht
    have hs1 : t < ((P.extract 0 1024).map (·.toNat)).size := by
      rw [Array.size_map, Array.size_extract]
      omega
    have k := (Array.all_eq_true.mp hall) t hs1
    have hP : t < P.size := by omega
    simpa [Array.getD, hP] using k
  refine ⟨⟨fun t => ⟨(P.getD t.val 0).toNat, htok t.val t.isLt⟩, ⟨yTok, hy⟩,
    ⟨so.r, ?_⟩, ⟨so.e, ?_⟩⟩, rfl, rfl, fun _ _ => rfl, rfl⟩
  · show so.r < 1024 + 1
    rw [q2]
    omega
  · show so.e < 1024 + 1
    rw [q3]
    omega

/-! ## The calls and their segments -/

/-- A member of a list is there with some number. -/
theorem zipIdx_has {α : Type} : ∀ (l : List α) (k : ℕ) (a : α), a ∈ l → ∃ i, (a, i) ∈ l.zipIdx k
  | [], _, _, h => by simp at h
  | x :: l, k, a, h => by
    rw [List.zipIdx_cons]
    rcases List.mem_cons.mp h with e | h
    · subst e
      exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := zipIdx_has l (k + 1) a h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

/-- Every segment that was to be placed is a segment of the placed call. -/
theorem place_has (name kind : String) (asks : List Model.SegAsk) (fl : ℕ) (a : Model.SegAsk)
    (ha : a ∈ asks) : ∃ s ∈ (Model.place name kind asks fl).segs, s.name = a.1 := by
  obtain ⟨i, hi⟩ := zipIdx_has asks 0 a ha
  exact ⟨_, (List.mem_map.mpr ⟨(a, i), hi, rfl⟩ : _ ∈ (Model.place name kind asks fl).segs), rfl⟩

/-- What one line of the calls takes: each segment has the length of the first member of the list of
segments with its name; a name that is returned as met was met before or is a taken segment's. -/
theorem lineSegs_spec (sd : List (String × String × ℕ)) (kind : String) :
    ∀ (ns seen : List String) (r : List Model.SegAsk × List String),
      Model.Head.lineSegs sd kind ns seen = some r →
      (∀ a ∈ r.1, ∃ x, sd.find? (fun x => x.1 == a.1) = some x ∧ a.2.1 = x.2.2) ∧
      ∀ n ∈ r.2, n ∈ seen ∨ n ∈ r.1.map (·.1)
  | [], seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact ⟨fun a ha => (by cases ha), fun n hn => Or.inl hn⟩
  | n0 :: ns, seen, r, h => by
    rw [Model.Head.lineSegs] at h
    split at h
    · cases h
    · rename_i x hf
      split at h
      · cases h
      · cases hr : Model.Head.lineSegs sd kind ns (n0 :: seen) with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : ((n0, x.2.2, false) :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          obtain ⟨i1, i2⟩ := lineSegs_spec sd kind ns (n0 :: seen) r' hr
          refine ⟨fun a ha => ?_, fun n hn => ?_⟩
          · rcases List.mem_cons.mp ha with e | ha'
            · subst e
              exact ⟨x, hf, rfl⟩
            · exact i1 a ha'
          · rcases i2 n hn with k | k
            · rcases List.mem_cons.mp k with e | k'
              · subst e
                exact Or.inr (by simp)
              · exact Or.inl k'
            · refine Or.inr ?_
              simp only [List.map_cons, List.mem_cons]
              exact Or.inr k

/-- What the lines of the calls give: each call is placed from segments of that kind; and a name
that is returned as met was met before or is the name of a segment of one of the calls. -/
theorem callsFrom_spec (sd : List (String × String × ℕ)) (fl : ℕ) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List Model.CallD × List String),
      Model.Head.callsFrom sd fl lines names seen = some r →
      (∀ c ∈ r.1, ∃ name kind asks, c = Model.place name kind asks fl ∧
        ∀ a ∈ asks, ∃ x, sd.find? (fun x => x.1 == a.1) = some x ∧ a.2.1 = x.2.2) ∧
      ∀ n ∈ r.2, n ∈ seen ∨ ∃ c ∈ r.1, ∃ s ∈ c.segs, s.name = n
  | [], _, seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact ⟨fun c hc => (by cases hc), fun n hn => Or.inl hn⟩
  | [] :: _, _, _, _, h => by cases h
  | [_] :: _, _, _, _, h => by cases h
  | [_, _] :: _, _, _, _, h => by cases h
  | (name :: kind :: s :: ss) :: rest, names, seen, r, h => by
    rw [Model.Head.callsFrom] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i asks seen' hl
        cases hr : Model.Head.callsFrom sd fl rest (name :: names) seen' with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : (Model.place name kind asks fl :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          obtain ⟨l1, l2⟩ := lineSegs_spec sd kind (s :: ss) seen (asks, seen') hl
          obtain ⟨i1, i2⟩ := callsFrom_spec sd fl rest (name :: names) seen' r' hr
          refine ⟨fun c hc => ?_, fun n hn => ?_⟩
          · rcases List.mem_cons.mp hc with e | hc'
            · exact ⟨name, kind, asks, e, l1⟩
            · exact i1 c hc'
          · rcases i2 n hn with k | ⟨c, hc, hs⟩
            · rcases l2 n k with k' | k'
              · exact Or.inl k'
              · obtain ⟨a, ha, hna⟩ := List.mem_map.mp k'
                obtain ⟨g, hg, hgn⟩ := place_has name kind asks fl a ha
                exact Or.inr ⟨_, List.mem_cons_self, g, hg, hgn.trans hna⟩
            · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hs⟩

/-- What callsOf returns: each call is placed from segments of the head's list, and each of the nine
names is the name of a segment of one of the calls. -/
theorem callsOf_spec {h : Model.Head.Shape} {L : Model.Head.HL} {cs : List Model.CallD}
    (hc : Model.Head.callsOf h L = .ok cs) :
    (∀ c ∈ cs, ∃ name kind asks fl, c = Model.place name kind asks fl ∧
      ∀ a ∈ asks, ∃ x, (Model.Head.segments h L).find? (fun x => x.1 == a.1) = some x ∧
        a.2.1 = x.2.2) ∧
    ∀ x ∈ Model.Head.segments h L, ∃ c ∈ cs, ∃ s ∈ c.segs, s.name = x.1 := by
  unfold Model.Head.callsOf at hc
  obtain ⟨-, hc⟩ := ok_of_needed hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i calls seen hf
    obtain ⟨e, hc⟩ := ok_of_needed hc
    cases hc
    obtain ⟨i1, i2⟩ := callsFrom_spec _ _ _ [] [] (cs, seen) hf
    refine ⟨fun c hcm => ?_, fun x hx => ?_⟩
    · obtain ⟨name, kind, asks, e1, e2⟩ := i1 c hcm
      exact ⟨name, kind, asks, _, e1, e2⟩
    · have hin : x.1 ∈ seen := by simpa using List.all_eq_true.mp e x hx
      rcases i2 x.1 hin with k | k
      · cases k
      · exact k

/-- The tests on the calls' sizes ask that each call has at least as many columns as a block has
features. -/
theorem lJ_of_callSizes (h : Model.Head.Shape) : ∀ cs : List Model.CallD,
    Model.Head.callSizes h cs = .ok () → ∀ c ∈ cs, h.ls ≤ c.lJ
  | [], _, _, hc => by cases hc
  | c0 :: cs, hs, c, hc => by
    rw [Model.Head.callSizes] at hs
    obtain ⟨-, hs⟩ := ok_of_needed hs
    obtain ⟨e, hs⟩ := ok_of_needed hs
    rcases List.mem_cons.mp hc with k | k
    · subst k
      exact Nat.not_lt.mp (of_decide_eq_false (nor_true_split e).2)
    · exact lJ_of_callSizes h cs hs c k

/-- In the head's list of segments each member is the first with its name. -/
theorem segments_find (h : Model.Head.Shape) (L : Model.Head.HL) :
    ∀ x ∈ Model.Head.segments h L,
      (Model.Head.segments h L).find? (fun y => y.1 == x.1) = some x := by
  intro x hx
  unfold Model.Head.segments at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Model.Head.segments]

/-- The first member of a list that a test picks: its number and itself. -/
theorem findIdx_of_mem {α : Type} (p : α → Bool) : ∀ l : List α, (∃ x ∈ l, p x = true) →
    ∃ q c, l.findIdx? p = some q ∧ l[q]? = some c ∧ p c = true
  | [], ⟨_, hx, _⟩ => by cases hx
  | a :: l, hex => by
    rw [List.findIdx?_cons]
    by_cases ha : p a = true
    · exact ⟨0, a, by rw [if_pos ha], by simp, ha⟩
    · obtain ⟨x, hx, hp⟩ := hex
      rcases List.mem_cons.mp hx with e | hx'
      · subst e
        exact absurd hp ha
      · obtain ⟨q, c, h1, h2, h3⟩ := findIdx_of_mem p l ⟨x, hx', hp⟩
        exact ⟨q + 1, c, by rw [if_neg ha, h1]; rfl, by simpa using h2, h3⟩

/-- A member of a list, read in the list's array. -/
theorem toArray_getD_some {α : Type} {l : List α} {q : ℕ} {c : α} (h : l[q]? = some c) (d : α) :
    l.toArray.getD q d = c := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The public half of what is asked of a segment that is read by blocks: it has n entries, its
columns are aligned on blocks of 2^ls entries, and its call has at least 2^ls columns. -/
def SegLaid (R : Model.Head.Run) (sn : String) (n : ℕ) : Prop :=
  ∃ q g, Model.Head.callNo R.L sn = some q ∧ (R.L.calls.getD q default).seg? sn = some g ∧
    g.n = n ∧ Aligned g R.h.ls (R.L.calls.getD q default).lJ ∧
    R.h.ls ≤ (R.L.calls.getD q default).lJ

/-- **With the half on the call's point, the record SegFit.** The point has one coordinate for each
bit of a column, and its last ls coordinates are low: these two come from tests on values that the
verifier makes when it runs, and stay hypotheses. -/
theorem SegLaid.fit {K : Type} [Field K] (ρ : Model.Reading K) {R : Model.Head.Run} {sn : String}
    {n : ℕ} (S : SegLaid R sn n) {low : ℕ → K}
    (hz : ∀ q, Model.Head.callNo R.L sn = some q →
      (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ ∧
      ∀ j, j < R.h.ls →
        pt ρ (Model.Head.zjOf R.L R.x.g1 q) ((R.L.calls.getD q default).lJ - R.h.ls + j) = low j) :
    SegFit ρ R sn n low := by
  obtain ⟨q, g, hq, hg, hn, A, hl⟩ := S
  exact ⟨q, g, hq, hg, hn, A, (hz q hq).1, hl, (hz q hq).2⟩

/-- The segment of an admitted layout with the name of a member of the head's list: its call, its
length, and the call's placing. -/
theorem seg_of_admitted {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L)
    (x : String × String × ℕ) (hx : x ∈ Model.Head.segments h L) :
    ∃ q g name kind asks fl, Model.Head.callNo L x.1 = some q ∧
      L.calls.getD q default = Model.place name kind asks fl ∧
      (L.calls.getD q default).seg? x.1 = some g ∧ g ∈ (Model.place name kind asks fl).segs ∧
      g.n = x.2.2 ∧ h.ls ≤ (L.calls.getD q default).lJ := by
  obtain ⟨cs, hc, hs, hL⟩ := A.calls
  obtain ⟨c1, c2⟩ := callsOf_spec hc
  obtain ⟨c, hcm, s, hsm, hsn⟩ := c2 x hx
  have hp : (c.seg? x.1).isSome = true := by
    unfold Model.CallD.seg?
    cases hf : c.segs.find? (fun g => g.name == x.1) with
    | some g => rfl
    | none =>
      have k := List.find?_eq_none.mp hf s hsm
      simp [hsn] at k
  obtain ⟨q, c', h1, h2, h3⟩ :=
    findIdx_of_mem (fun c : Model.CallD => (c.seg? x.1).isSome) cs ⟨c, hcm, hp⟩
  have hq : Model.Head.callNo L x.1 = some q := by
    unfold Model.Head.callNo
    rw [hL]
    simpa using h1
  have hg : L.calls.getD q default = c' := by
    rw [hL]
    exact toArray_getD_some h2 default
  have hc' : c' ∈ cs := List.mem_of_getElem? h2
  obtain ⟨g, hgs⟩ := Option.isSome_iff_exists.mp h3
  obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 c' hc'
  have hgm : g ∈ c'.segs := List.mem_of_find?_eq_some hgs
  have hgn : g.name = x.1 := by simpa using List.find?_some hgs
  rw [e1] at hgm
  obtain ⟨a, ha, a1, a2, -⟩ := place_segs name kind asks fl g hgm
  obtain ⟨x', f1, f2⟩ := e2 a ha
  rw [← a1, hgn, segments_find h L x hx] at f1
  have ex : x = x' := Option.some.inj f1
  refine ⟨q, g, name, kind, asks, fl, hq, hg.trans e1, by rw [hg]; exact hgs, hgm, ?_, ?_⟩
  · rw [a2, f2, ex]
  · rw [hg]
    exact lJ_of_callSizes h cs hs c' hc'

/-- A number is at most itself rounded up to a multiple of a positive number, and that is less than
their sum. -/
theorem roundUp_bounds (x : ℕ) {w : ℕ} (hw : 0 < w) :
    x ≤ Model.roundUp x w ∧ Model.roundUp x w < x + w := by
  unfold Model.roundUp
  have h1 := Nat.div_add_mod (x + w - 1) w
  have h2 := Nat.mod_lt (x + w - 1) hw
  rw [Nat.mul_comm] at h1
  constructor <;> omega

/-- A multiple of w is not moved by rounding up. -/
theorem roundUp_of_dvd {x w : ℕ} (hw : 0 < w) (h : w ∣ x) : Model.roundUp x w = x := by
  obtain ⟨b1, b2⟩ := roundUp_bounds x hw
  have hd : w ∣ Model.roundUp x w - x := Nat.dvd_sub (dvd_roundUp x w) h
  have h0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

/-- No column stands behind the vocabulary if and only if a block's features divide the
vocabulary's size. -/
theorem AdmittedH.JV_iff {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L) :
    L.JV = h.V ↔ h.S2 ∣ h.V := by
  constructor
  · intro e
    rw [← e, A.JV]
    exact dvd_roundUp _ _
  · intro hd
    rw [A.JV]
    exact roundUp_of_dvd (Nat.pow_pos (by norm_num)) hd

/-- **At the library's sizes**: a layout that the verifier returns for a shape with 2^10 positions,
width 5,120 and a vocabulary of 202,048 entries has the record Laid at the library's sizes. That no
column stands behind the vocabulary follows: a block has at most 2^6 features, and 2^6 divides
202,048. -/
theorem laid_ref {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) (h1 : h.lt = 10) (h2 : h.d = 5120)
    (h3 : h.V = 202048) {R : Model.Head.Run} (e1 : R.h = h) (e2 : R.L = L) :
    Laid R HeadSizes.ref := by
  have A := admittedH_of_layout hy
  obtain ⟨-, hla, -⟩ := A.bounds
  have hls : h.ls ≤ 6 := by
    unfold Model.Head.Shape.ls
    omega
  have hdv : h.S2 ∣ h.V := by
    rw [h3]
    exact Dvd.dvd.trans (pow_dvd_pow 2 hls) (by norm_num)
  have hV : L.JV = h.V := A.JV_iff.2 hdv
  have hJa : L.JVa = 131072 := by
    rw [A.JVa, hV, h3]
    decide +kernel
  have Z := laid_of_layout hy hV e1 e2
  rw [h1, h2, h3, hJa] at Z
  exact Z

/-- Every length in the head's list of segments is below the bound of the placing rule. -/
theorem segments_lt {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L) :
    ∀ x ∈ Model.Head.segments h L, x.2.2 < 2 ^ (Model.topBit + 1) := by
  have t : (2 : ℕ) ^ (Model.topBit + 1) = 2 ^ 41 := rfl
  rw [t]
  obtain ⟨hd, hla, hV⟩ := A.bounds
  have hS : h.S2 ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right (by norm_num) (by unfold Model.Head.Shape.ls; omega)
  have hS0 : 0 < h.S2 := Nat.pow_pos (by norm_num)
  have hJ : L.JV < 2 ^ 25 := by
    have k := (roundUp_bounds h.V hS0).2
    rw [← A.JV] at k
    omega
  have hJa : L.JVa < 2 ^ 41 := by
    rw [A.JVa]
    refine Nat.pow_lt_pow_right (by norm_num) ?_
    have k : ceilLog2 L.JV ≤ 25 := by
      unfold ceilLog2
      split
      · omega
      · have k2 : Nat.log2 (L.JV - 1) < 25 := (Nat.log2_lt (by omega)).mpr (by omega)
        omega
    omega
  have hR : Model.ledNRH h.XL < 2 ^ 41 := by
    unfold Model.ledNRH Model.ledNR Model.ledNE
    split <;> norm_num
  intro x hx
  unfold Model.Head.segments at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show h.d < 2 ^ 41
    omega
  · show h.d < 2 ^ 41
    omega
  · show L.JV < 2 ^ 41
    omega
  · show L.JV < 2 ^ 41
    omega
  · exact hR
  · show L.JV < 2 ^ 41
    omega
  · show h.d < 2 ^ 41
    omega
  · exact hJa
  · show L.JV - L.JVa < 2 ^ 41
    omega

section Segments
variable {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
  (hy : Model.Head.layout h tauFC = .ok L) {R : Model.Head.Run} (e1 : R.h = h) (e2 : R.L = L)
include hy e1 e2

/-- **Each of the nine names has a call and a segment of its length, with one column for each
entry.** -/
theorem segHas_of_layout (x : String × String × ℕ) (hx : x ∈ Model.Head.segments h L) :
    SegHas R x.1 x.2.2 := by
  have A := admittedH_of_layout hy
  subst e1 e2
  obtain ⟨q, g, name, kind, asks, fl, hq, hp, hg, hgm, hn, -⟩ := seg_of_admitted A x hx
  have hlt : g.n < 2 ^ (Model.topBit + 1) := by rw [hn]; exact segments_lt A x hx
  exact ⟨q, g, hq, hg, hn,
    ((place_aligned name kind asks fl 0 g hgm (by simp) hlt).size).trans hn⟩

/-- **A segment whose length is a whole number of blocks is aligned on blocks.** -/
theorem segLaid_of_layout (x : String × String × ℕ) (hx : x ∈ Model.Head.segments h L)
    (hd : h.S2 ∣ x.2.2) : SegLaid R x.1 x.2.2 := by
  have A := admittedH_of_layout hy
  subst e1 e2
  obtain ⟨q, g, name, kind, asks, fl, hq, hp, hg, hgm, hn, hl⟩ := seg_of_admitted A x hx
  have hlt : g.n < 2 ^ (Model.topBit + 1) := by rw [hn]; exact segments_lt A x hx
  have hd' : 2 ^ R.h.ls ∣ g.n := by rw [hn]; exact hd
  refine ⟨q, g, hq, hg, hn, ?_, hl⟩
  rw [hp]
  exact place_aligned name kind asks fl R.h.ls g hgm hd' hlt

/-- **The eight segments that are read by blocks**, each with its length. -/
theorem eight_of_layout :
    SegLaid R "NF" h.d ∧ SegLaid R "NFH" h.d ∧ SegLaid R "CNF" h.d ∧ SegLaid R "HD0" L.JV ∧
      SegLaid R "HD1" L.JV ∧ SegLaid R "HD2" L.JV ∧ SegLaid R "HE0" L.JVa ∧
      SegLaid R "HE1" (L.JV - L.JVa) := by
  have A := admittedH_of_layout hy
  have hJ : h.S2 ∣ L.JV := by rw [A.JV]; exact dvd_roundUp _ _
  have hE : h.S2 ∣ L.JV - L.JVa := Nat.dvd_sub hJ A.SVa
  exact ⟨segLaid_of_layout hy e1 e2 ("NF", "R16", h.d) (by simp [Model.Head.segments]) A.Sd,
    segLaid_of_layout hy e1 e2 ("NFH", "R16", h.d) (by simp [Model.Head.segments]) A.Sd,
    segLaid_of_layout hy e1 e2 ("CNF", "FC", h.d) (by simp [Model.Head.segments]) A.Sd,
    segLaid_of_layout hy e1 e2 ("HD0", "R16", L.JV) (by simp [Model.Head.segments]) hJ,
    segLaid_of_layout hy e1 e2 ("HD1", "R16", L.JV) (by simp [Model.Head.segments]) hJ,
    segLaid_of_layout hy e1 e2 ("HD2", "R8", L.JV) (by simp [Model.Head.segments]) hJ,
    segLaid_of_layout hy e1 e2 ("HE0", "FE", L.JVa) (by simp [Model.Head.segments]) A.SVa,
    segLaid_of_layout hy e1 e2 ("HE1", "FE", L.JV - L.JVa) (by simp [Model.Head.segments]) hE⟩

/-- The ledger's segment, whose entries are read one by one. -/
theorem row_of_layout : SegHas R "ROW" (Model.ledNRH h.XL) :=
  segHas_of_layout hy e1 e2 ("ROW", "R8", Model.ledNRH h.XL) (by simp [Model.Head.segments])

end Segments

#print axioms laid_of_layout
#print axioms reqFits_of_covered
#print axioms reqFits_of_instance
#print axioms alike_of_reqFits
#print axioms instance_of_covered
#print axioms SegLaid.fit
#print axioms segHas_of_layout
#print axioms segLaid_of_layout
#print axioms eight_of_layout
#print axioms row_of_layout
#print axioms AdmittedH.JV_iff
#print axioms laid_ref
#print axioms layout_of_public

end OnBytes.Road.Hd
