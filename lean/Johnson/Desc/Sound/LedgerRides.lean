-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LedgerRides.lean: AT THE LEDGER OF A PROOF FILE's SHARED CHAIN, AT THE TABLE's
FILES' OWN FILLING (meaningSigS, promSigS: Johnson/Desc/Sound/BordersSharedFill.lean): A MESSAGE's
PIN RIDES BACK, AND ITS PROMISE ("every leaf is shown; the record holds the sample; no collision")
RIDES ON, PAST ANY BLOCK IN FRONT OF WHICH ITS TREE WAS SENT AND WHICH LEAVES ITS SAMPLE. A tool for
every kind's files that owe a clause (ClauseAt, LedgerClause.lean). No kind is named.

  SentBefore N p l k x m   the four comparisons of numbers for the message m at block k: its tree's
                  number is at least lo, below the tops of both borders, below the piece's base.
  noCollJT_of_smp, pinJT_of_smp   a promise of "no collision", and a pin, go from a record to
                  another that holds the same samples.
  pin_rides       **the pin rides back** from border k + 1 to border k.
  noColl_rides    **the promise rides on** from border k to border k + 1.
  frames_of_pins  ALL RIDERS AT A BLOCK: the pins by pin_rides; every other shared item (the kinds'
                  files' letters) by a premise.
  shape_mem       the one book-keeping clause of the promise at border k is shape k.
  prom_rides      THE WHOLE SHARED PROMISE AT A BLOCK THAT SENDS NOTHING: "no collision" by
                  noColl_rides; the stored table's promise and the book-keeping's step by premises.
What is not claimed. PREMISES: SentBefore (numbers of the plan and the tiling) · the two records
hold the same samples at the members of ms.
Nothing on soundness.

-/
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.LedgerCols
import Johnson.Desc.Sound.LedgerClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Shared

/-- A promise of "no collision" goes from a record to another that holds the same samples. -/
theorem noCollJT_of_smp (cs : OnBytes.Codes) {A Xi : Type} (G : FileDescription Xi)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a a' : A) (y : Strs)
    (hsm : ∀ x ∈ ms, smp a' x.1 x.2 = smp a x.1 x.2) (h : noCollJT cs G smp ms j t a y) :
    noCollJT cs G smp ms j t a' y := fun x hx hs => by
  obtain ⟨z, hz, r⟩ := h x hx hs
  exact ⟨z, (hsm x hx).trans hz, r⟩

/-- A pin goes from a record to another that holds the same samples. -/
theorem pinJT_of_smp (cs : OnBytes.Codes) {A Xi Cells Tok : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a a' : A) (y : Strs) (w : Wit Cells Tok MsgT)
    (hsm : ∀ x ∈ ms, smp a' x.1 x.2 = smp a x.1 x.2) (h : pinJT cs G arr smp ms j t a y w) :
    pinJT cs G arr smp ms j t a' y w :=
  ⟨h.1, fun x hx hs => by
    obtain ⟨z, hz, r⟩ := h.2 x hx hs
    exact ⟨z, (hsm x hx).trans hz, r⟩⟩

variable {P₁ S₂ Cl Xi Cells Tok : Type} {C : CK} {Fr : Frame} (cs : OnBytes.Codes)
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells)
  (stOf : S₂ → OnBytes.Statement) (bookOf : S₂ → OnBytes.TreeBook)
  (N : NumbersS) (Mg : MeaningS S₂ P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
  (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))

/-- The four comparisons of numbers for the message m at block k. -/
structure SentBefore (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (m : Msg2) :
    Prop where
  lo : N.lo ≤ (N.tenant m).1
  front : (N.tenant m).1 < hiAt k p l
  behind : (N.tenant m).1 < hiAt (k + 1) p l
  base : (N.tenant m).1 < x.base

/-- **The pin rides back.** -/
theorem pin_rides (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (m : Msg2)
    (hB : SentBefore N p l k x m) (a b : (P₁ × S₂) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds))
    (hout : x.ior.red.out a τ = some b)
    (hsm : ∀ z ∈ ms, smp₂ a.1.2 z.1 z.2 = smp₂ b.1.2 z.1 z.2) (w : Wit Cells Tok MsgT)
    (h : muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin m) (k + 1)
      ((actQ N p l (k + 1)).2 b) w) :
    muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin m) k ((actQ N p l k).2 a) w :=
  pinJT_of_smp cs G arr smp₂ ms _ _ b.1.2 a.1.2 _ w hsm
    (pinJT_col cs G arr smp₂ ms _ _ b.1.2 _ _ w
      (fun q => cols_stay N p l k x a b τ hout _ q hB.lo hB.front hB.behind hB.base) h)

/-- **The promise rides on.** -/
theorem noColl_rides (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (m : Msg2)
    (hB : SentBefore N p l k x m) (a b : (P₁ × S₂) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds))
    (hout : x.ior.red.out a τ = some b)
    (hsm : ∀ z ∈ ms, smp₂ b.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2)
    (h : (PromS.noColl m).holds N (promSigS cs G smp₂ ms stOf bookOf Pm) ((actQ N p l k).2 a).1
      (strsOfAct Fr ((actQ N p l k).2 a))) :
    (PromS.noColl m).holds N (promSigS cs G smp₂ ms stOf bookOf Pm) ((actQ N p l (k + 1)).2 b).1
      (strsOfAct Fr ((actQ N p l (k + 1)).2 b)) := by
  have hc : ∀ q, (strsOfAct Fr ((actQ N p l (k + 1)).2 b)).col (N.tenant m).1 q =
      (strsOfAct Fr ((actQ N p l k).2 a)).col (N.tenant m).1 q := fun q =>
    (cols_stay N p l k x a b τ hout _ q hB.lo hB.front hB.behind hB.base).symm
  obtain ⟨h1, h3⟩ := h
  exact ⟨shownJT_col cs G ms _ _ _ _ hc h1,
    noCollJT_of_smp cs G smp₂ ms _ _ a.1.2 b.1.2 _ hsm
      (noCollJT_col cs G smp₂ ms _ _ a.1.2 _ _ hc h3)⟩

/-- **The pin rides back**, where the two records hold the same samples AT THE MEMBERS THAT SIT AT
THE MESSAGE's SEAT: so also past a sending, which gives other members their samples. -/
theorem pin_ridesAt (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (m : Msg2)
    (hB : SentBefore N p l k x m) (a b : (P₁ × S₂) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds))
    (hout : x.ior.red.out a τ = some b)
    (hsm : ∀ z ∈ ms, SitsAt z (N.tenant m).1 (N.tenant m).2 →
      smp₂ a.1.2 z.1 z.2 = smp₂ b.1.2 z.1 z.2) (w : Wit Cells Tok MsgT)
    (h : muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin m) (k + 1)
      ((actQ N p l (k + 1)).2 b) w) :
    muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin m) k ((actQ N p l k).2 a) w := by
  have h1 := pinJT_col cs G arr smp₂ ms _ _ b.1.2 _ _ w
    (fun q => cols_stay N p l k x a b τ hout _ q hB.lo hB.front hB.behind hB.base) h
  exact ⟨h1.1, fun z hz hs => by
    obtain ⟨v, hv, r⟩ := h1.2 z hz hs
    exact ⟨v, (hsm z hz hs).trans hv, r⟩⟩

/-- **The promise rides on**, under the like. -/
theorem noColl_ridesAt (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)) (m : Msg2)
    (hB : SentBefore N p l k x m) (a b : (P₁ × S₂) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds))
    (hout : x.ior.red.out a τ = some b)
    (hsm : ∀ z ∈ ms, SitsAt z (N.tenant m).1 (N.tenant m).2 →
      smp₂ b.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2)
    (h : (PromS.noColl m).holds N (promSigS cs G smp₂ ms stOf bookOf Pm) ((actQ N p l k).2 a).1
      (strsOfAct Fr ((actQ N p l k).2 a))) :
    (PromS.noColl m).holds N (promSigS cs G smp₂ ms stOf bookOf Pm) ((actQ N p l (k + 1)).2 b).1
      (strsOfAct Fr ((actQ N p l (k + 1)).2 b)) := by
  have hc : ∀ q, (strsOfAct Fr ((actQ N p l (k + 1)).2 b)).col (N.tenant m).1 q =
      (strsOfAct Fr ((actQ N p l k).2 a)).col (N.tenant m).1 q := fun q =>
    (cols_stay N p l k x a b τ hout _ q hB.lo hB.front hB.behind hB.base).symm
  obtain ⟨h1, h3⟩ := h
  refine ⟨shownJT_col cs G ms _ _ _ _ hc h1, fun z hz hs => ?_⟩
  obtain ⟨v, hv, r⟩ := noCollJT_col cs G smp₂ ms _ _ a.1.2 _ _ hc h3 z hz hs
  exact ⟨v, (hsm z hz hs).trans hv, r⟩

variable (Oc : P₁ → Strs → Prop) (split : Bool)

/-- **All riders at a block**: the form in which clause_of_own asks them, at the identity. -/
theorem frames_of_pins (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (on : (P₁ × S₂) × Fr.E.Str → Prop)
    (hB : ∀ m, openSh split k (.pin m) → SentBefore N p l k x m)
    (hsm : ∀ a τ b, on a → x.ior.red.out a τ = some b →
      ∀ z ∈ ms, smp₂ a.1.2 z.1 z.2 = smp₂ b.1.2 z.1 z.2)
    (hother : ∀ a τ b w i, on a → x.ior.red.out a τ = some b → openSh split k i →
      ¬ insSh split k i → (∀ m, i ≠ .pin m) →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i (k + 1) ((actQ N p l (k + 1)).2 b) w →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i k ((actQ N p l k).2 a) w) :
    ∀ a τ b w i, on a → x.ior.red.out a τ = some b → openSh split k i → ¬ insSh split k i →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i (k + 1) ((actQ N p l (k + 1)).2 b) w →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i k ((actQ N p l k).2 a) w := by
  intro a τ b w i ha hout ho hi h
  by_cases hp : ∃ m, i = .pin m
  · obtain ⟨m, rfl⟩ := hp
    exact pin_rides cs G arr smp₂ ms decT₂ N Mg p l k x m (hB m ho) a b τ hout (hsm a τ b ha hout)
      w h
  · exact hother a τ b w i ha hout ho hi (fun m e => hp ⟨m, e⟩) h

/-- The one book-keeping clause of the promise at border k is shape k. -/
theorem shape_mem (k j : ℕ) (h : PromS.shape j ∈ promsAt split k) : j = k := by
  unfold promsAt at h
  rcases List.mem_append.1 h with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · simpa using h2
    · obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 h2
      cases i <;> simp at hi
  · split at h1 <;> simp at h1

/-- **The whole shared promise at a block that sends nothing.** -/
theorem prom_rides (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (hsub : ∀ m, PromS.noColl m ∈ promsAt split (k + 1) → PromS.noColl m ∈ promsAt split k)
    (hnl : PromS.nothingLeft ∉ promsAt split (k + 1))
    (hB : ∀ m, PromS.noColl m ∈ promsAt split (k + 1) → SentBefore N p l k x m)
    (a b : (P₁ × S₂) × Fr.E.Str) (τ : Iop.Tr (uLT C x.ds)) (hout : x.ior.red.out a τ = some b)
    (hsm : ∀ z ∈ ms, smp₂ b.1.2 z.1 z.2 = smp₂ a.1.2 z.1 z.2)
    (htab : Pm.tablePromise a.1.2 (strsOfAct Fr ((actQ N p l k).2 a)) →
      Pm.tablePromise b.1.2 (strsOfAct Fr ((actQ N p l (k + 1)).2 b)))
    (hshape : Pm.shape k a.1.2 = true → Pm.shape (k + 1) b.1.2 = true)
    (h : promQ N (promSigS cs G smp₂ ms stOf bookOf Pm) split p l k ((actQ N p l k).2 a)) :
    promQ N (promSigS cs G smp₂ ms stOf bookOf Pm) split p l (k + 1)
      ((actQ N p l (k + 1)).2 b) := by
  intro c hc
  cases c with
  | tablePromise => exact htab (h .tablePromise (by simp [promsAt]))
  | shape j =>
    obtain rfl := shape_mem split (k + 1) j hc
    exact hshape (h (.shape k) (by simp [promsAt]))
  | noColl m =>
    exact noColl_rides cs G smp₂ ms stOf bookOf N Pm p l k x m (hB m hc) a b τ hout hsm
      (h (.noColl m) (hsub m hc))
  | nothingLeft => exact absurd hc hnl

end VerifiableInference.Desc.Sound
