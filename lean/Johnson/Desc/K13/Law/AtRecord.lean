-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtRecord.lean: WHAT KIND K13's TWO JOINED BLOCKS DO TO THE FIRST CHAIN's
RECORD: the batching's block (`atM3 P`) and W's commitment with the kind's block behind it
(`atM4 P (K1.sendAtS P')`; Johnson/Desc/K13/AtS.lean). Definitions and statements with their
proofs. It names no table of joints.
Main names:
  `atM3_rec`: where the batching's block says yes: the chain stood in the finish; behind, the record
    is the one in front but for the statement, the debt of rows (none) and "here" (the chain's end).
    `atM3_failed`: so a mark stays, and none is laid. `atM3_book`: the book, and the number of
    messages, are as they were.
  `StepM3`, `stepM3_keeps`: two records with a public part between which that block's decision has
    said yes; such a step keeps every relation on statements that the ground's functions keep.
  `piece_step`: where a piece says yes, its block's step has said yes. General in the piece.
  `atM4_mid`, `atM4_rec`: where the other block says yes: the chain stood, and stands, at its end;
    no count of rows waits behind; the mark, what the links left and the rows on the table are as
    they were. `atM4_laid`: from `FrontOk` in front: `EvalLaid` and `FrontOk` behind.
    `atM4_booked`: the book as a sending leaves it (`K1.Booked`,
    Johnson/Desc/K1/Law/BookAtRecord.lean).
  `isSend_atM4`: that block is a sending (`K1.IsSend`).
  `StepM4`, `StepM4.decide`: two records between which its step has said yes.
  `atM3_retype`, `atM4_retype`: the blocks typed at no claims and carried to another type of claims
    (`Block.retype`: so a lot's table lays them) say yes only where the blocks at that type do.

What is not claimed. That a chain holds these blocks. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.Bools
import Johnson.Desc.K13.Law.K1Pin
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K1.Law.HereAtRecord
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Ground (GroundQuiet)

/-! ## 1 The batching's block -/

section
variable {Cl : Type}

/-- **Where the joined block says yes**: the chain stood in the finish; the record behind is the one
in front but for the statement, the debt of rows and "here". -/
theorem atM3_rec {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ (f : First.FinOwn) (st' : Statement) (o : First.MemOwn), s.here = .fin f ∧
      s' = { s with st := st', rowsOwed := none, here := .mem o } := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  have he := frontB_ok atS P h1
  obtain ⟨p, out, hp, _, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  cases hs : s.here with
  | fin f =>
    have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
    rw [e1] at he
    have e2 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } := by
      rw [← Option.some.inj he]
      simp only [S.enterMem, hs]
    subst e2
    obtain rfl := Option.some.inj hp
    obtain rfl := Option.some.inj hp'
    exact ⟨f, _, _, rfl, rfl⟩
  | _ =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he

/-- A mark stays, and none is laid. -/
theorem atM3_failed {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    s'.failed = s.failed := by
  obtain ⟨_, _, _, _, rfl⟩ := atM3_rec h
  rfl

/-- The book, and the number of messages, are as they were. -/
theorem atM3_book {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    s'.book = s.book ∧ s'.st.oracles.size = s.st.oracles.size := by
  refine ⟨?_, sameAll_size (atM3_same h)⟩
  obtain ⟨_, _, _, _, rfl⟩ := atM3_rec h
  rfl

end

/-- Two records of the table between which the joined block's own decision has said yes; the public
part is one. -/
def StepM3 {Pp : Type} (Cl : Type) (P : Where) (x x' : Pp × S) : Prop :=
  x'.1 = x.1 ∧ ∃ rs gs, (atM3 (Cl := Cl) P).decide x.2 rs gs = .ok x'.2

/-- A step keeps every relation on statements that the ground's functions keep. -/
theorem stepM3_keeps {Pp Cl : Type} {P : Where} {R : Statement → Statement → Prop}
    (H : GroundQuiet R) {x x' : Pp × S} (h : StepM3 Cl P x x') : R x.2.st x'.2.st := by
  obtain ⟨rs, gs, hdec⟩ := h.2
  exact atM3_keeps H P _ _ _ _ hdec

/-! ## 2 W's commitment with the kind's block behind it -/

/-- **Where a piece says yes, its block's step has said yes.** General in the piece. -/
theorem piece_step {T Cl W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    {a b : T × F.E.Str} {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) :
    ∃ rs cols n, p.b.step F.ft a.1 rs cols = .ok (b.1, n) := by
  have hb' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none).map
      (fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  split at hb'
  · cases hrun : p.run a.1 (sView C p.stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      obtain rfl := Option.some.inj hb'
      obtain ⟨_, n, hst, _⟩ := one_ok hrun
      exact ⟨_, _, n, hst⟩
  · cases hb'

section
variable {Cl : Type}

/-- The joined block's yes, cut in two. -/
theorem atM4_mid {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    ∃ s₁ g₁ rs₂ g₂, (K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] g₁ = .ok s₁ ∧
      (rowsB (Cl := Cl) atS P).decide s₁ rs₂ g₂ = .ok s' := by
  have h' : ((K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] _).bind (fun m =>
      (rowsB (Cl := Cl) atS P).decide m _ _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h'
  exact ⟨s₁, _, _, _, h1, h2⟩

/-- The block behind W's commitment lays no debt of rows where none stood. -/
theorem rowsB_owed {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s')
    (h0 : s.rowsOwed = none) : s'.rowsOwed = none := by
  obtain ⟨p, l, o, hp, _, _, hb1⟩ := rowsB_ok atS P h
  obtain ⟨m₀, hs, _⟩ := get_mem hp
  simp only [atS, hs] at hp
  rw [hb1, ← Option.some.inj hp]
  simp [atS, hs, h0]

/-- **Where the joined block says yes.** -/
theorem atM4_rec {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    (∃ o, s'.here = .mem o) ∧ s'.rowsOwed = none ∧ s'.failed = s.failed ∧ s'.out = s.out ∧
      s'.rows = s.rows := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨a, ids, _, _, _, _, ho, _, hf, hw⟩ := K1.sendAtS_here P' s s₁ _ g₁ h1
  have hr := (K1.sendAtS_rows P' s s₁ r₁ r₂ g₁ h1).2
  have hr2 := rowsB_rows h2
  have hw2 := rowsB_owed h2 hw
  obtain ⟨m₀, l, o, owed, _, _, _, rfl⟩ := rowsB_at h2
  exact ⟨⟨_, rfl⟩, hw2, hf, ho, hr2.trans hr⟩

/-- From the promise of the record in front: what the block leaves in the public record, and the
promise again. -/
theorem atM4_laid {F : Frame} {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') (y y' : F.E.Str)
    (hon : FrontOk P ((s, y) : S × F.E.Str)) :
    EvalLaid P s' ∧ FrontOk P ((s', y') : S × F.E.Str) := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨hc, _, hl⟩ := sendAtS_keepsEnd (Cl := Cl) P' s s₁ [r₁, r₂] g₁ rfl h1
  have hon₁ : FrontOk P ((s₁, y) : S × F.E.Str) := by
    intro l hl'
    have e : linAt s = some l := by rw [← hl]; exact hl'
    obtain ⟨h3, h4⟩ := hon l e
    refine ⟨h3, ?_⟩
    show P.lin.kCol ≤ (linLayW s₁.st.codes P.lin).bits
    rw [hc]
    exact h4
  have hE := rowsB_lays h2 y hon₁
  refine ⟨hE, ?_⟩
  obtain ⟨l, row, _, _, hl₁, hcl, hb, _⟩ := hE
  intro l' hl'
  have e : l = l' := Option.some.inj (hl₁.symm.trans hl')
  subst e
  exact ⟨⟨row, hcl⟩, hb⟩

/-- The same shape, mark, sample rows and pad: so the same shape, mark and sample rows. -/
theorem sameMsgs_of_all {St St' : Statement} (h : SameAll St St') : K1.SameMsgs St St' := by
  refine ⟨h.1, fun j => ?_⟩
  have e := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row ×
    List (OnBytes.Part × ℕ) => (t.1, t.2.1, t.2.2.1)) (h.2 j)
  simpa [sampleOf, Option.map_map, Function.comp_def] using e

/-- **The joined block is a sending.** -/
theorem isSend_atM4 (P : Where) (P' : K1.Par) :
    K1.IsSend P' (fun s : S => s.st) (atM4 (Cl := Cl) P (K1.sendAtS P')) :=
  K1.isSend_andThen P' _ _ _ _ (K1.isSend_sendAtS P') rfl
    fun _ _ _ _ h => sameMsgs_of_all (rowsB_same h)

/-- **The book as a sending leaves it.** -/
theorem atM4_booked {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    K1.Booked P' s.book s.st.oracles.size s'.book s'.st.oracles.size := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  have hb := K1.sendAtS_booked P' s s₁ r₁ r₂ g₁ h1
  have hn := sameAll_size (rowsB_same h2)
  obtain ⟨m₀, l, o, owed, _, _, _, rfl⟩ := rowsB_at h2
  rw [hn]
  exact hb

end

/-- Two records of the table between which the joined block's step has said yes; the public part is
one. -/
def StepM4 {Pp : Type} (Cl : Type) (P : Where) (P' : K1.Par) (x x' : Pp × S) : Prop :=
  x'.1 = x.1 ∧ ∃ ft rs cols n,
    (atM4 (Cl := Cl) P (K1.sendAtS P')).step ft x.2 rs cols = .ok (x'.2, n)

/-- A step holds a yes of the decision on two rounds. -/
theorem StepM4.decide {Pp Cl : Type} {P : Where} {P' : K1.Par} {x x' : Pp × S}
    (h : StepM4 Cl P P' x x') : ∃ r₁ r₂ gs,
      (atM4 (Cl := Cl) P (K1.sendAtS P')).decide x.2 [r₁, r₂] gs = .ok x'.2 := by
  obtain ⟨ft, rs, cols, n, hst⟩ := h.2
  obtain ⟨hfit, gs, hd⟩ := K1.step_ok ft _ _ _ rs cols n hst
  have hl : (rs.map noDigest).length = 2 := by
    rw [List.length_map]
    exact roundsFit_length _ _ hfit
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, rs.map noDigest = [r₁, r₂] := by
    match rs.map noDigest, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  rw [e] at hd
  exact ⟨r₁, r₂, gs, hd⟩

/-! ## 3 At another type of claims -/

theorem atM3_retype {Cl : Type} (P : Where) :
    ((atM3 (Cl := Unit) P).retype : Block S Cl).UnderR (atM3 P) :=
  ⟨rfl, fun _ _ _ _ h => h⟩

theorem atM4_retype {Cl : Type} (P : Where) (P' : K1.Par) :
    ((atM4 (Cl := Unit) P (K1.sendAtS P')).retype : Block S Cl).UnderR
      (atM4 P (K1.sendAtS P')) :=
  ⟨rfl, fun _ _ _ _ h => h⟩

end VerifiableInference.Desc.K13.Law
