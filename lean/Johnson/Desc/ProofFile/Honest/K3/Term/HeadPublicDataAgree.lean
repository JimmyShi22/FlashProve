-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/HeadPublicDataAgree.lean: the lookup on the output head's
calls, at the filling's own public data. The filling lays the head's public data with the covered
positions and checked tokens that reqAt reads off the instance; the trace's theorems stand at
pubHAt. These two records are not equal as structures. This file shows that everything the keys and
the bits read of them agrees at a request that instOf reads, and carries the theorems on keys and
bits over to a served request.

  HeadPublicDataAgree P Q: what the keys read of two records of the head's public data agrees:
    the shape, the layout, the border, the weights' layout; whether a position is covered; whether
    it has a cost; and the checked token at a covered position.
  headKeysAgreeWherePublicDataAgree, headJointKeysAgreeWherePublicDataAgree,
    headLookAgreesWherePublicDataAgree, ownHeadAgreesWherePublicDataAgree: then the keys agree: the
    library's kvH_agree.
  requestCoveredPositionsAgree: at a request that instOf reads, in the goals' scope, coveredOfInst
    returns, and its covered positions, positions with a cost and checked tokens are the request's.
  requestHeadDataAgrees, headKeysAtTheRequest, headLookAtTheRequest: the same for reqAt's record.
  headLookMeetsAtTheRequest, headLookAtTheSite, headLookMeetsAtTheSiteShape, headMidAtTheRequest:
    keys and bits are honest at
    the filling's own term, and the specification's relation holds at a site on the head's calls.

Limits. In the goals' scope and at the full size alone. Nothing here says that an input holds the
honest trace: hC and hW are premises. Nothing on any property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MeetsMid
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull
import Johnson.Desc.ProofFile.Honest.K3.Law.AtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteShapes
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ShapeIsFsPaid
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites
import Johnson.Desc.ProofFile.Honest.K3.LotFilled
import Johnson.Desc.ProofFile.Honest.K3.WitReq
import Johnson.Desc.ProofFile.InstOfInScope
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Road.Ends.HeadWit
import Johnson.HonestTrace.FullPlanesRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term

open OnBytes.Ends.H (PubH NameH kvH keyH)
open OnBytes.Model (Head.Covered Head.winOf)
open OnBytes.Model.Verify (words32)
open OnBytes.HonestTrace (cellOf entryOf pubHAt theTrace ServesAt)
open OnBytes.Road.Hd (covReq)
open _root_.Inst.Model (Instance ppref)
open OnBytes.Flat (requestWordsOf)
open VerifiableInference.Desc.First (S)

/-! ## 1 What the keys read of the head's public data -/

/-- What the keys and the bits read of two records of the head's public data agrees. -/
structure HeadPublicDataAgree (P Q : PubH) : Prop where
  sameShape : P.h = Q.h
  sameLayout : P.L = Q.L
  sameBorder : P.b = Q.b
  sameWeightsLayout : P.lay = Q.lay
  sameCovered : ∀ t, P.cov.hOn.getD t false = Q.cov.hOn.getD t false
  sameCosted : ∀ t, P.cov.hOnC.getD t false = Q.cov.hOnC.getD t false
  sameCheckedToken : ∀ t, P.cov.hOn.getD t false = true → P.win.getD t 0 = Q.win.getD t 0

section
variable {R : Type} [Field R] {P Q : PubH}

/-- **Where the public data agree, so does every key of every call, at every reading of the cells.**
The library's `kvH_agree` (Johnson/HonestTrace/FullPlanesRun.lean) at Q. -/
theorem headKeysAgreeWherePublicDataAgree (A : HeadPublicDataAgree P Q) (cell : NameH → R) :
    kvH P cell = kvH Q cell := by
  have e : P = { Q with cov := P.cov, win := P.win } := by
    obtain ⟨h, L, b, c, w, y⟩ := P
    obtain ⟨h', L', b', c', w', y'⟩ := Q
    obtain ⟨e1, e2, e3, e4, -, -, -⟩ := A
    dsimp only at e1 e2 e3 e4
    subst e1 e2 e3 e4
    rfl
  have positions : 0 < Q.h.T := Nat.two_pow_pos _
  have agree : OnBytes.HonestTrace.AgreeCov Q P.cov P.win := fun t _ =>
    ⟨A.sameCovered t, A.sameCosted t,
      fun c => A.sameCheckedToken t ((A.sameCovered t).trans c)⟩
  exact (congrArg (fun D => kvH D cell) e).trans
    (OnBytes.HonestTrace.kvH_agree Q positions agree cell)

/-- The joint keys agree. -/
theorem headJointKeysAgreeWherePublicDataAgree (A : HeadPublicDataAgree P Q) (cell : NameH → R) :
    keyH P cell = keyH Q cell := by
  rw [OnBytes.Ends.H.keyH_eq, OnBytes.Ends.H.keyH_eq, A.sameLayout,
    headKeysAgreeWherePublicDataAgree A cell]

end

/-- **The head's look at a public record depends on what the keys read alone.** -/
theorem headLookAgreesWherePublicDataAgree (X : OnBytes.Model.Verify.Public) {P Q : PubH}
    (A : HeadPublicDataAgree P Q) (C : Cells) (W : Weights) :
    lookH X P C W = lookH X Q C W := by
  unfold lookH
  rw [headJointKeysAgreeWherePublicDataAgree A, A.sameShape, A.sameLayout]

/-- The filling's own look at the head, at two records that agree. -/
theorem ownHeadAgreesWherePublicDataAgree {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH pubH' : Xi → PubH) (y : Xi)
    (A : HeadPublicDataAgree (pubH y) (pubH' y)) (C : Cells) (W : Weights) :
    (ownSources X cells weights pubH).head y C W = (ownSources X cells weights pubH').head y C W := by
  show (⟨fun theta n => keyH (pubH y) (ownH X C.cell W.entry (linkH X)) theta n,
      fun u j => OnBytes.Ends.H.bitsH (pubH y).h (pubH y).L.fs (ownH X C.cell W.entry (linkH X))
        (u * 32 + j)⟩ : LookIn) =
    ⟨fun theta n => keyH (pubH' y) (ownH X C.cell W.entry (linkH X)) theta n,
      fun u j => OnBytes.Ends.H.bitsH (pubH' y).h (pubH' y).L.fs (ownH X C.cell W.entry (linkH X))
        (u * 32 + j)⟩
  rw [headJointKeysAgreeWherePublicDataAgree A, A.sameShape, A.sameLayout]

/-! ## 2 The values at a request -/

/-- An entry of a mapped range. -/
theorem entryOfMappedRange {α : Type} (f : ℕ → α) (n t : ℕ) (d : α) :
    ((Array.range n).map f).getD t d = if t < n then f t else d := by
  by_cases h : t < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- An entry of an array with one entry set. -/
theorem entryAfterSetting (a : Array ℕ) (i v j : ℕ) (hij : i ≠ j) :
    (a.setIfInBounds i v).getD j 0 = a.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  rw [if_neg hij]

/-- The entry that was set. -/
theorem entrySet (a : Array ℕ) (i v : ℕ) (h : i < a.size) :
    (a.setIfInBounds i v).getD i 0 = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]
  rfl

/-- **Where the four tests pass, the covered positions are there, entry by entry.** -/
theorem coveredAtOfGoodWords {T V y r e : ℕ} {s : S} (hy : y < V) (hsize : s.req.size = T + 2)
    (hall : ∀ v ∈ (s.req.extract 0 T).map (·.toNat), v < V)
    (hr : (s.req.getD T 0).toNat = r) (he : (s.req.getD (T + 1) 0).toNat = e) (hre : r < e)
    (heT : e ≤ T) :
    ∃ cov : Head.Covered, s.coveredAt T V y = .ok cov ∧
      (∀ t, cov.hOn.getD t false = if t < T then decide (r ≤ t) && decide (t < e) else false) ∧
      (∀ t, cov.hOnC.getD t false =
        if t < T then (decide (r ≤ t) && decide (t < e)) && decide (t + 1 < T) else false) ∧
      (∀ t, cov.hWin.getD t 0 = if t < T then
        (if (decide (r ≤ t) && decide (t < e)) = true then
          (if t + 1 < T then ((s.req.extract 0 T).map (·.toNat)).getD (t + 1) 0 else y) else 0)
        else 0) ∧
      cov.hWin.size = T := by
  have c1 : ¬ ((!decide (y < V)) = true) := by simpa using hy
  have c2 : ¬ ((!(s.req.size == T + 2)) = true) := by simpa using hsize
  have c3 : ¬ ((!(((s.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V))) = true) := by
    have a : (((s.req.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true :=
      Array.all_eq_true_iff_forall_mem.2 fun v hv => decide_eq_true (hall v hv)
    rw [a]
    decide
  have c4 : ¬ ((decide (r ≥ e) || decide (e > T)) = true) := by
    have a : ¬ r ≥ e := by omega
    have b : ¬ e > T := by omega
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    exact ⟨a, b⟩
  unfold S.coveredAt
  dsimp only
  rw [hr, he, if_neg c1, if_neg c2, if_neg c3, if_neg c4]
  refine ⟨_, rfl, fun t => ?_, fun t => ?_, fun t => ?_, ?_⟩
  · exact entryOfMappedRange _ _ _ _
  · exact entryOfMappedRange _ _ _ _
  · exact entryOfMappedRange _ _ _ _
  · simp

section
variable {Zp : ProofFile.Pub} {ξ : ProofFile.Inst} {x : Instance ppref}

/-- The reply that is asked about is the instance's token. -/
theorem askedTokIsTheReply (hx : ProofFile.instOf ξ = some x) : askedTok ξ = x.y.val := by
  unfold askedTok
  rw [(ProofFile.instOf_words hx).2]
  show (UInt32.ofNat x.y.val).toNat = _
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.y.isLt (by decide))

/-- **At the numbers of the reference sizes: coveredOfInst returns at a request that instOf reads,
and what it returns agrees with the request.** -/
theorem requestCoveredPositionsAtTheSizes (windowSize : Zp.p.X.T = 1024)
    (vocabularySize : Zp.p.X.P.h.V = 202048) (headPositions : Zp.p.X.hS.T = 1024)
    (hx : ProofFile.instOf ξ = some x) :
    ∃ cov, coveredOfInst Zp ξ = .ok cov ∧
      (∀ t, cov.hOn.getD t false = (covReq x).hOn.getD t false) ∧
      (∀ t, cov.hOnC.getD t false = (covReq x).hOnC.getD t false) ∧
      ∀ t, cov.hOn.getD t false = true →
        (Head.winOf cov Zp.p.X.hS.T (askedTok ξ)).getD t 0 =
          ((Array.range 1024).map x.w).getD t 0 := by
  have hy := askedTokIsTheReply hx
  have hre : x.r < x.e := (ProofFile.instOf_bytes hx).2.2.1
  have heT : x.e ≤ 1024 := x.e_le
  obtain ⟨r0, r1, r2, r3⟩ := ProofFile.reads_withReq hx Zp.s₀
  have hreq : (Zp.s₀.withReq (words32 ξ.pub.request)).req = requestWordsOf x :=
    (ProofFile.instOf_words hx).1
  have hsize : (Zp.s₀.withReq (words32 ξ.pub.request)).req.size = 1024 + 2 := by
    rw [hreq, OnBytes.Flat.size_requestWordsOf]
    rfl
  have wr : ((Zp.s₀.withReq (words32 ξ.pub.request)).req.getD 1024 0).toNat = x.r := by
    have e := r1
    unfold S.rowR at e
    rw [r0] at e
    exact e
  have we : ((Zp.s₀.withReq (words32 ξ.pub.request)).req.getD (1024 + 1) 0).toNat = x.e := by
    have e := r2
    unfold S.rowE at e
    rw [r0] at e
    exact e
  have wt : ∀ i, (((Zp.s₀.withReq (words32 ξ.pub.request)).req.extract 0 1024).map (·.toNat)).getD
      i 0 = if k : i < ppref.T then (x.prompt ⟨i, k⟩).val else 0 := by
    intro i
    have e := r3 i
    unfold S.tokv at e
    rw [r0] at e
    exact e
  have wlt : ∀ v ∈ ((Zp.s₀.withReq (words32 ξ.pub.request)).req.extract 0 1024).map (·.toNat),
      v < 202048 := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
    have g := wt i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at g
    have g' : (((Zp.s₀.withReq (words32 ξ.pub.request)).req.extract 0 1024).map (·.toNat))[i] =
        if k : i < ppref.T then (x.prompt ⟨i, k⟩).val else 0 := g
    rw [g']
    split
    · exact (x.prompt _).isLt
    · decide
  obtain ⟨cov, ret, on, onC, win, size⟩ := coveredAtOfGoodWords (T := 1024) (V := 202048)
    (y := x.y.val) (r := x.r) (e := x.e) (s := Zp.s₀.withReq (words32 ξ.pub.request)) x.y.isLt hsize
    wlt wr we hre heT
  refine ⟨cov, ?_, fun t => ?_, fun t => ?_, fun t c => ?_⟩
  · unfold coveredOfInst
    rw [windowSize, vocabularySize, hy]
    exact ret
  · rw [on t]
    show _ = ((Array.range 1024).map fun t => decide (x.r ≤ t ∧ t < x.e)).getD t false
    rw [entryOfMappedRange]
    by_cases ht : t < 1024
    · rw [if_pos ht, if_pos ht, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
    · rw [if_neg ht, if_neg ht]
  · rw [onC t]
    show _ = ((Array.range 1024).map fun t => decide (x.r ≤ t ∧ t < min x.e 1023)).getD t false
    rw [entryOfMappedRange]
    by_cases ht : t < 1024
    · rw [if_pos ht, if_pos ht, Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    · rw [if_neg ht, if_neg ht]
  · have ht : t < 1024 := by
      by_contra ht
      rw [on t, if_neg ht] at c
      cases c
    have hon : (decide (x.r ≤ t) && decide (t < x.e)) = true := by
      rw [on t, if_pos ht] at c
      exact c
    have value : x.w t = if t + 1 < 1024 then
        (((Zp.s₀.withReq (words32 ξ.pub.request)).req.extract 0 1024).map (·.toNat)).getD (t + 1) 0
        else x.y.val := by
      by_cases h1 : t + 1 < 1024
      · have h2 : t + 1 < ppref.T := h1
        rw [if_pos h1, wt (t + 1), dif_pos h2]
        show x.tok (t + 1) = _
        unfold Instance.tok
        rw [dif_pos h2]
      · have h2 : ¬ t + 1 < ppref.T := h1
        rw [if_neg h1]
        show x.tok (t + 1) = _
        unfold Instance.tok
        rw [dif_neg h2]
    have plain : cov.hWin.getD t 0 = x.w t := by
      rw [win t, if_pos ht, if_pos hon, value]
    rw [entryOfMappedRange, if_pos ht, headPositions, hy]
    unfold Head.winOf
    split
    · by_cases e : 1024 - 1 = t
      · subst e
        rw [entrySet _ _ _ (by rw [size]; omega)]
        have h1 : ¬ (1024 - 1 + 1 < 1024) := by omega
        rw [value, if_neg h1]
      · rw [entryAfterSetting _ _ _ _ e]
        exact plain
    · exact plain

end

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : _root_.Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {Zp : ProofFile.Pub}
  {ξ : ProofFile.Inst} {x : Instance ppref}

/-- In scope the head's number of positions is 1,024. -/
theorem headPositionsInScope (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) : Zp.p.X.hS.T = 1024 := by
  have e : Zp.p.X.hS.lt = 10 := (Meaning.HeadS.sizes_in_scope hZ hR h).1
  show 2 ^ Zp.p.X.hS.lt = 1024
  simp [e]

/-- **In the goals' scope, at a request that instOf reads: coveredOfInst returns, and whether a
position is covered, whether it has a cost and the checked token at a covered position are the
request's.** -/
theorem requestCoveredPositionsAgree (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (hx : ProofFile.instOf ξ = some x) :
    ∃ cov, coveredOfInst Zp ξ = .ok cov ∧
      (∀ t, cov.hOn.getD t false = (covReq x).hOn.getD t false) ∧
      (∀ t, cov.hOnC.getD t false = (covReq x).hOnC.getD t false) ∧
      ∀ t, cov.hOn.getD t false = true →
        (Head.winOf cov Zp.p.X.hS.T (askedTok ξ)).getD t 0 =
          ((Array.range 1024).map x.w).getD t 0 :=
  requestCoveredPositionsAtTheSizes (ProofFile.window_in_scope hZ hR h) (ProofFile.vocab_in_scope hZ hR h)
    (headPositionsInScope hZ hR h) hx

/-- **The filling's public data at the head agrees with the trace's.** -/
theorem requestHeadDataAgrees (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (hx : ProofFile.instOf ξ = some x) :
    HeadPublicDataAgree (headPub Zp.p.X (reqAt Zp ξ).1 (reqAt Zp ξ).2) (pubHAt Zp.p.X x) := by
  obtain ⟨cov, ret, a, b, c⟩ := requestCoveredPositionsAgree hZ hR h hx
  have e : reqAt Zp ξ = (cov, Head.winOf cov Zp.p.X.hS.T (askedTok ξ)) := by
    unfold reqAt
    rw [ret]
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, a, b, c⟩

/-- **Every key of every call at the filling's public data is the key at the trace's.** -/
theorem headKeysAtTheRequest {R : Type} [Field R] (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (hx : ProofFile.instOf ξ = some x) (cell : NameH → R) :
    kvH (headPub Zp.p.X (reqAt Zp ξ).1 (reqAt Zp ξ).2) cell = kvH (pubHAt Zp.p.X x) cell :=
  headKeysAgreeWherePublicDataAgree (requestHeadDataAgrees hZ hR h hx) cell

/-- The head's look at the filling's public data is the look at the trace's. -/
theorem headLookAtTheRequest (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (hx : ProofFile.instOf ξ = some x) (C : Cells) (W : Weights) :
    lookH Zp.p.X (headPub Zp.p.X (reqAt Zp ξ).1 (reqAt Zp ξ).2) C W =
      lookH Zp.p.X (pubHAt Zp.p.X x) C W :=
  headLookAgreesWherePublicDataAgree _ (requestHeadDataAgrees hZ hR h hx) C W

/-! ## 3 The head's part of the end -/

variable {i : Cm.Idx}

/-- **The keys and bits of the filling's own look at the head are honest, at a served request.** -/
theorem headLookMeetsAtTheRequest {W₀ Tr' : Type} (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (S : ServesAt Zp.p.X i x) (hx : ProofFile.instOf ξ = some x) (cells : Tr' → Cells)
    (weights : W₀ → Weights) :
    ((tiedOwnSources Zp.p.X cells weights (reqAt Zp)).head ξ
        ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩).Meets
      Zp.p.X.HLy.fs Zp.p.X.hS.lmbH := by
  have e := ownHeadAgreesWherePublicDataAgree Zp.p.X cells weights
    (fun y => headPub Zp.p.X (reqAt Zp y).1 (reqAt Zp y).2) (fun _ => pubHAt Zp.p.X x) ξ
    (requestHeadDataAgrees hZ hR h hx) ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩
  show ((ownSources Zp.p.X cells weights
    (fun y => headPub Zp.p.X (reqAt Zp y).1 (reqAt Zp y).2)).head ξ
      ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩).Meets _ _
  rw [e]
  exact ownH_meets (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h S)
    (OnBytes.HonestTrace.lookPub_in_scope hZ hR h)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h S)
    (OnBytes.HonestTrace.planesLaid_in_scope hZ hR h i x) cells weights _ ξ rfl

variable {W₀ Rc Tr' : Type}

/-- **At a site on the head's calls, what the row is handed is the filling's own look, which is
honest at the plan's shape and the site's lm.** -/
theorem headLookAtTheSite (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (S : ServesAt Zp.p.X i x) (s : Site) (hs : s ∈ lookSites Zp) (hd : s.digits = false)
    (hc : s.caller = .head) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (t : Local W₀ Rc ProofFile.Inst Tr') (hC : cells t.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (hx : ProofFile.instOf t.x = some x)
    (heard : List Fmt.Drawn) :
    ∃ (fs : OnBytes.Model.Forest.Shape) (Lk : LookIn), fsOf Zp.p.X s = some fs ∧
      askOf (tiedOwnSources Zp.p.X cells weights (reqAt Zp)) (whoOf s) t heard = Lk.hidden ∧
      Lk.Meets fs s.p.lm := by
  obtain ⟨e1, e2, e3⟩ := Law.Spec.site_head Zp s hs hd hc
  refine ⟨Zp.p.X.HLy.fs, (tiedOwnSources Zp.p.X cells weights (reqAt Zp)).head t.x
    ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩, e1, ?_, ?_⟩
  · rw [e3]
    show ((tiedOwnSources Zp.p.X cells weights (reqAt Zp)).head t.x (cells t.trace)
      (weights t.w₀)).hidden = _
    rw [hC, hW]
  · rw [e2]
    exact headLookMeetsAtTheRequest hZ hR h S hx cells weights

/-- The same at the site's own shape. -/
theorem headLookMeetsAtTheSiteShape (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (S : ServesAt Zp.p.X i x) (s : Site) (hs : s ∈ lookSites Zp) (hd : s.digits = false)
    (hc : s.caller = .head) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (t : Local W₀ Rc ProofFile.Inst Tr') (hC : cells t.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (hx : ProofFile.instOf t.x = some x)
    (heard : List Fmt.Drawn) :
    ∃ Lk : LookIn,
      askOf (tiedOwnSources Zp.p.X cells weights (reqAt Zp)) (whoOf s) t heard = Lk.hidden ∧
      Lk.Meets s.shape s.p.lm := by
  obtain ⟨fs, Lk, e1, e2, e3⟩ := headLookAtTheSite hZ hR h S s hs hd hc cells weights t hC hW hx heard
  have hB : fsOf Zp.p.X s = some s.shape := Law.AtThr.shapeIsFs_of_public h s hs
  have hsh : fs = s.shape := Option.some.inj (e1.symm.trans hB)
  subst hsh
  exact ⟨Lk, e2, e3⟩

/-- **The specification's relation at the site's data, at a site on the head's calls.** -/
theorem headMidAtTheRequest (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (S : ServesAt Zp.p.X i x) (s : Site) (hs : s ∈ lookSites Zp) (hd : s.digits = false)
    (hc : s.caller = .head) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (t : Local W₀ Rc ProofFile.Inst Tr') (hC : cells t.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩)
    (hW : weights t.w₀ = ⟨entryOf i⟩) (hx : ProofFile.instOf t.x = some x)
    (heard ds : List Fmt.Drawn) :
    (Law.siteData s (askOf (tiedOwnSources Zp.p.X cells weights (reqAt Zp)) (whoOf s) t) heard
      ds).Mid := by
  obtain ⟨Lk, e2, e3⟩ :=
    headLookMeetsAtTheSiteShape hZ hR h S s hs hd hc cells weights t hC hW hx heard
  have hok : FoNums.ok s.shape = true := (FastLaw.sites_ok Zp s hs).2
  show (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
    (askOf (tiedOwnSources Zp.p.X cells weights (reqAt Zp)) (whoOf s) t heard)
    (ptsOf s.at_.face s.at_.base (heard ++ ds))).Mid
  rw [e2]
  exact Law.mid_of_meets Lk s.shape s.p.lm s.p.first hok e3 _

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.headKeysAgreeWherePublicDataAgree
#print axioms ProofFile.Honest.K3.Term.headJointKeysAgreeWherePublicDataAgree
#print axioms ProofFile.Honest.K3.Term.headLookAgreesWherePublicDataAgree
#print axioms ProofFile.Honest.K3.Term.ownHeadAgreesWherePublicDataAgree
#print axioms ProofFile.Honest.K3.Term.requestCoveredPositionsAgree
#print axioms ProofFile.Honest.K3.Term.requestHeadDataAgrees
#print axioms ProofFile.Honest.K3.Term.headKeysAtTheRequest
#print axioms ProofFile.Honest.K3.Term.headLookAtTheRequest
#print axioms ProofFile.Honest.K3.Term.headLookMeetsAtTheRequest
#print axioms ProofFile.Honest.K3.Term.headLookAtTheSite
#print axioms ProofFile.Honest.K3.Term.headLookMeetsAtTheSiteShape
#print axioms ProofFile.Honest.K3.Term.headMidAtTheRequest
