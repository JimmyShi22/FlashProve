-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPartsAtX.lean: THE OUTPUT HEAD's FOUR PARTS AT A REQUEST MADE OF AN
INSTANCE
(no carried record): they give the library's Policy.HeadCl. The like of Law/LibLetters.lean's
headCl_at,
which takes a record and three equations that tie it to the instance: here the kind's letter Request
is made of the instance itself, so these equations hold by the make.

WHY. The table of joints' parts of the head's relation ride from the borders at which they are
closed
back to the chain's start: so they may read a record through the request alone.

  reqX x           the kind's letter Request, of an instance: its tokens below T (0 from T on), r,
  e.
  reqX_congr, rider_any_token, idnPlain_wh   reqX reads no reply; the rider's two lines read no
  token
                   and no stored weight; "idn" reads no stored weight.
  requestOf_words  at a record whose request's words are requestWordsOf x: the same.
  requestOf_eq     at a record whose request is the instance's: requestOf s = reqX x: AN EQUATION.
  same_atX, more_atX   the two records of letters of Law/LibJoin.lean at it.
  okStart_atX      the kind's test on the request says yes at it, where the instance has the
                   request's form (Head3) and the sizes are the full ones.
  idnPlain_req, parts_of_plain, idn_atX   the part "idn" on the sizes, the policy, the request and
                   the cells alone (Law/IdnPlain.lean) reads of the request r and e alone; it gives
                   HeadParts' two fields at any token; what the head's law closes in front at a
                   record whose two positions are the instance's is that part at reqX x.
  headCl_atX       MAIN: HeadParts at (sizesOf h, the policy of parOf h work, reqX x, the token x.y)
                   gives Policy.HeadCl (Hd.npOf h) (Hd.polOf h) Wz x (cellsN c).

WHAT IT IS NOT. An implication. PREMISES THAT STAY: FullH h (the full size alone) · h.digSh = 8 ·
the
tests on the plan · Head3 x · tab is the library's EX on 16 bits · c.Wh is the index's output matrix
·
HeadParts itself. That cellsN c is what the committed integers spell: not here. No chance in it.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibLetters
import Johnson.Desc.Kinds.Law.IdnPlain
import Johnson.Desc.Kinds.Law.K06Glue
import Johnson.Flat.Instance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model (AcceptancePolicy Mat ppref Instance)

/-- The kind's letter Request, of an instance: its tokens below T (0 from T on, as a carried
record's
reader of the request's words has it), r and e. -/
@[reducible] def reqX (x : Instance ppref) : Request :=
  { tok := fun t => if t < ppref.T then x.tok t else 0, r := x.r, e := x.e }

namespace Came

open OnBytes (E)
open Inst.Model.Head (Req)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)
open Norm (lt ls d lPd S2 T)

theorem same_atX (h : OnBytes.Model.Head.Shape) (work : Nat) (x : Instance ppref) (hF : FullH h) :
    @Same (sizesOf h) (parOf h work).policy (reqX x) (Req.of (OnBytes.Road.Hd.polOf h) x) :=
  @Same.mk (sizesOf h) (parOf h work).policy (reqX x) _
    (by show 2 ^ h.lt = 1024; rw [hF.lt]) rfl rfl rfl rfl rfl

theorem more_atX (h : OnBytes.Model.Head.Shape) (pol : AcceptancePolicy) (x : Instance ppref) (hF : FullH h)
    (h8 : h.digSh = 8) : @More (sizesOf h) (reqX x) ⟨x.y.val⟩ (Req.of pol x) :=
  @More.mk (sizesOf h) (reqX x) ⟨x.y.val⟩ _ h8
    (by
      unfold JVa
      rw [jv_at h hF]
      rfl)
    (fun t => by
      show x.tok (t + 1) = if t + 1 < 2 ^ h.lt then
        (if t + 1 < ppref.T then x.tok (t + 1) else 0) else x.y.val
      rw [hF.lt]
      by_cases ht : t + 1 < 2 ^ 10
      · rw [if_pos ht, if_pos (show t + 1 < ppref.T from ht)]
      · have ht' : ¬ t + 1 < ppref.T := ht
        rw [if_neg ht]
        unfold Instance.tok
        rw [dif_neg ht'])

/-- The kind's test on the request, at an instance that has the request's form. -/
theorem okStart_atX (h : OnBytes.Model.Head.Shape) (work : Nat) (x : Instance ppref)
    (hF : FullH h) (h3 : Inst.Model.Head3 x) : (parOf h work).okStart (reqX x) = true := by
  show (Decidable.decide (x.r < x.e) && Decidable.decide (x.e ≤ 2 ^ h.lt) &&
    (List.range (2 ^ h.lt)).all fun t =>
      Decidable.decide ((if t < ppref.T then x.tok t else 0) < h.V)) = true
  rw [hF.lt, hF.V]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨h3.1, h3.2.1⟩, fun t ht => ?_⟩
  have ht' : t < ppref.T := ht
  rw [if_pos ht']
  unfold Instance.tok
  rw [dif_pos ht']
  exact (x.prompt ⟨t, ht'⟩).isLt

/-- **A RECORD WHOSE REQUEST IS THE INSTANCE's HAS THE INSTANCE's LETTER Request: AN EQUATION**: T +
2
words; the two positions; the tokens below T. So every sentence at the record's letters is, by
rewriting, the sentence at reqX x. -/
theorem requestOf_eq (s : VerifiableInference.Desc.First.S) (x : Instance ppref)
    (hsz : s.req.size = ppref.T + 2) (hr : s.rowR = x.r) (he : s.rowE = x.e)
    (htok : ∀ t, t < ppref.T → s.tokv.getD t 0 = x.tok t) : requestOf s = reqX x := by
  have hT : s.tokv.size = ppref.T := by
    unfold VerifiableInference.Desc.First.S.tokv VerifiableInference.Desc.First.S.reqT
    simp [hsz]
  show ({ tok := fun i => s.tokv.getD i 0, r := s.rowR, e := s.rowE } : Request) = _
  rw [hr, he]
  congr 1
  funext t
  by_cases ht : t < ppref.T
  · rw [if_pos ht, htok t ht]
  · rw [if_neg ht]
    simp [Array.getD, hT, ht]

/-- Of n words and two more: word t below n, cut to the first n and read as a number. -/
theorem words_tok {n : Nat} (f : Fin n → UInt32) (a b : UInt32) (t : Nat) (ht : t < n) :
    ((((Array.ofFn f) ++ #[a, b]).extract 0 n).map (·.toNat)).getD t 0 = (f ⟨t, ht⟩).toNat := by
  have h1 : t < ((((Array.ofFn f) ++ #[a, b]).extract 0 n).map (·.toNat)).size := by
    simp
    omega
  rw [Array.getD, dif_pos h1]
  simp

/-- **A RECORD WHOSE REQUEST's WORDS ARE THE INSTANCE's REQUEST FILE's** (requestWordsOf:
the T tokens, then r and e) **HAS THE INSTANCE's LETTER Request.** -/
theorem requestOf_words (s : VerifiableInference.Desc.First.S) (x : Instance ppref)
    (h : s.req = OnBytes.Flat.requestWordsOf x) : requestOf s = reqX x := by
  have hsz : s.req.size = ppref.T + 2 := by
    rw [h]
    unfold OnBytes.Flat.requestWordsOf
    simp
  have hT : s.reqT = ppref.T := by
    unfold VerifiableInference.Desc.First.S.reqT
    rw [hsz]
    rfl
  have small : ∀ n, n ≤ 202048 → (UInt32.ofNat n).toNat = n := by
    intro n hn
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  refine requestOf_eq s x hsz ?_ ?_ fun t ht => ?_
  · unfold VerifiableInference.Desc.First.S.rowR
    rw [hT, h]
    unfold OnBytes.Flat.requestWordsOf
    have e : ((Array.ofFn fun t : Fin ppref.T => UInt32.ofNat (x.prompt t).val) ++
        #[UInt32.ofNat x.r, UInt32.ofNat x.e]).getD ppref.T 0 = UInt32.ofNat x.r := by
      simp [Array.getD]
    rw [e]
    exact small _ (by
      have := x.rF.isLt
      have h2 : x.r < ppref.T + 1 := this
      have h3 : ppref.T = 1024 := rfl
      omega)
  · unfold VerifiableInference.Desc.First.S.rowE
    rw [hT, h]
    unfold OnBytes.Flat.requestWordsOf
    have e : ((Array.ofFn fun t : Fin ppref.T => UInt32.ofNat (x.prompt t).val) ++
        #[UInt32.ofNat x.r, UInt32.ofNat x.e]).getD (ppref.T + 1) 0 = UInt32.ofNat x.e := by
      simp [Array.getD]
    rw [e]
    exact small _ (by
      have h2 : x.e ≤ ppref.T := x.e_le
      have h3 : ppref.T = 1024 := rfl
      omega)
  · unfold VerifiableInference.Desc.First.S.tokv
    rw [hT, h]
    unfold OnBytes.Flat.requestWordsOf Instance.tok
    rw [dif_pos ht]
    rw [words_tok (fun t : Fin ppref.T => UInt32.ofNat (x.prompt t).val) _ _ t ht]
    exact small _ (by
      have := (x.prompt ⟨t, ht⟩).isLt
      have h3 : ppref.V = 202048 := rfl
      omega)

/-- reqX reads of an instance its prompt and its two positions: NOT THE REPLY. -/
theorem reqX_congr (x x' : Instance ppref) (hp : x.prompt = x'.prompt) (hr : x.r = x'.r)
    (he : x.e = x'.e) : reqX x = reqX x' := by
  show ({ tok := fun t => if t < ppref.T then x.tok t else 0, r := x.r, e := x.e } : Request) =
    { tok := fun t => if t < ppref.T then x'.tok t else 0, r := x'.r, e := x'.e }
  rw [hr, he]
  congr 1
  funext t
  by_cases ht : t < ppref.T
  · rw [if_pos ht, if_pos ht]
    unfold Instance.tok
    rw [dif_pos ht, dif_pos ht, hp]
  · rw [if_neg ht, if_neg ht]

/-- **THE RIDER's TWO LINES READ NO TOKEN AND NO STORED WEIGHT**: where they are 0 at every position
at one token and cells, they are at every token and at all cells with the same table of integers. -/
theorem rider_any_token [Sizes] [Policy] [Request] (sT y y' : Nat)
    (hplan : (letI : Token := ⟨y⟩
      planOk sT) = true) (c c' : Cells) (hc : c.cell = c'.cell)
    (hq : letI : Token := ⟨y⟩
      ∀ t, t < T → clipAt c (corner 0 t) = 0 ∧ tableAt c (corner 0 t) = 0) :
    letI : Token := ⟨y'⟩
    ∀ t, t < T → clipAt c' (corner 0 t) = 0 ∧ tableAt c' (corner 0 t) = 0 := by
  intro t ht
  obtain ⟨h1, h2⟩ := hq t ht
  have P1 : @PlanFacts _ _ := @planFacts _ _ _ ⟨y⟩ sT hplan
  have e1 := congrArg rd h1
  have e2 := congrArg rd h2
  rw [@rd_clip _ _ _ ⟨y⟩ c t ht, rd_zero] at e1
  rw [@rd_table _ _ _ ⟨y⟩ c t P1 ht, rd_zero] at e2
  obtain ⟨cell, Wh⟩ := c
  obtain ⟨cell', Wh'⟩ := c'
  simp only at hc
  subst hc
  letI : Token := ⟨y'⟩
  constructor
  · apply zero_of_rd (okE_clipAt _ _)
    rw [rd_clip ht]
    exact e1
  · apply zero_of_rd (okE_tableAt _ _)
    rw [rd_table P1 ht]
    exact e2

/-- "idn" reads the cells' two tables of integers alone: not the stored weights. -/
theorem idnPlain_wh (sz : Sizes) (pol : Policy) (q : Request) (c c' : NCells)
    (h1 : c.cell = c'.cell) (h2 : c.stream = c'.stream) (hq : IdnPlain sz pol q c) :
    IdnPlain sz pol q c' := by
  obtain ⟨⟨cell, Wh⟩, stream⟩ := c
  obtain ⟨⟨cell', Wh'⟩, stream'⟩ := c'
  simp only at h1 h2
  subst h1
  subst h2
  exact hq

/-- "idn" (Law/IdnPlain.lean) reads of the request its two positions alone. -/
theorem idnPlain_req (sz : Sizes) (pol : Policy) (q q' : Request) (hr : q.r = q'.r)
    (he : q.e = q'.e) (c : NCells) (hq : IdnPlain sz pol q c) : IdnPlain sz pol q' c := by
  obtain ⟨tok, r, e⟩ := q
  obtain ⟨tok', r', e'⟩ := q'
  simp only at hr he
  subst hr
  subst he
  exact hq

/-- From "idn" on the sizes, the policy, the request and the cells alone back to the two fields of
HeadParts, at any token. -/
theorem parts_of_plain [sz : Sizes] [pol : Policy] [rq : Request] [Token] (c : NCells)
    (hq : IdnPlain sz pol rq c) :
    (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
      ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  obtain ⟨h1, h2, h3⟩ := hq
  refine ⟨⟨?_, ?_⟩, h1⟩
  · apply zero_of_rd (show OnBytes.okE (meanAt c.toCells) = true from okE_addMul _ _ _)
    rw [rd_mean]
    exact h2
  · apply zero_of_rd (show OnBytes.okE (countAt c.toCells) = true from okE_addMul _ _ _)
    rw [rd_count]
    exact h3

/-- **WHAT THE HEAD's LAW CLOSES IN FRONT, AT A RECORD WHOSE TWO POSITIONS ARE THE INSTANCE's, IS
"idn" AT THE REQUEST MADE OF THE INSTANCE.** -/
theorem idn_atX (h : OnBytes.Model.Head.Shape) (iU3 work : Nat)
    (s : VerifiableInference.Desc.First.S) (x : Instance ppref) (c : NCells)
    (hr : s.rowR = x.r) (he : s.rowE = x.e)
    (hf : FrontIdn (parOf h work) (seatAt h iU3) s c) :
    IdnPlain (sizesOf h) (parOf h work).policy (reqX x) c :=
  idnPlain_req _ _ (requestOf s) (reqX x) hr he c
    (idnPlain_of_front (parOf h work) (seatAt h iU3) s c hf)

/-- **THE FOUR PARTS AT A REQUEST MADE OF THE INSTANCE GIVE HeadCl.** -/
theorem headCl_atX (h : OnBytes.Model.Head.Shape) (work : Nat) (x : Instance ppref) (Wz : Mat)
    (floor : Nat) (tab : Nat → Nat) (c : NCells) (hF : FullH h) (h8 : h.digSh = 8)
    (hplan : (parOf h work).ok = true) (h3 : Inst.Model.Head3 x)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (P : @HeadParts (sizesOf h) (parOf h work).policy (reqX x) ⟨x.y.val⟩ floor tab c) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf h) (OnBytes.Road.Hd.polOf h) Wz x (cellsN c) :=
  @headCl_of_parts (sizesOf h) (parOf h work).policy (reqX x) ⟨x.y.val⟩ h.tabS floor tab c
    (OnBytes.Road.Hd.polOf h) Wz x hplan (okStart_atX h work x hF h3)
    (by
      show x.y.val < h.V
      rw [hF.V]
      exact x.y.isLt)
    (same_atX h work x hF)
    (wide_at h hF (by
      letI := sizesOf h
      letI : Policy := (parOf h work).policy
      letI := reqX x
      letI : Token := ⟨x.y.val⟩
      exact (planFacts (sT := h.tabS) hplan).hF))
    (more_atX h _ x hF h8) htab hW P

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.okStart_atX
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.reqX_congr
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rider_any_token
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.idnPlain_wh
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.requestOf_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.requestOf_words
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.idn_atX
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.parts_of_plain
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCl_atX
