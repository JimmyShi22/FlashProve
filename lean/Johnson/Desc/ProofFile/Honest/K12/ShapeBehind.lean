-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ShapeBehind.lean

What it proves. Wherever the fold over the eight sub-protocols of the linear claim's shared rounds
returns from the chain's first state, the key's sizes fit, so the shape of the state behind is one
term of the plan, endOf Q sentU, whatever the key, the rounds and the columns. So the shape of what
the seat of the test on G_u enters there is the term doorU (endOf Q sentU). A state with that shape
and no field element but 0 and 1 is written out (fallU): what the seat enters at the lift of
endOf Q sentU; its shape is the same term. Behind the test on G_u the shape of what the seat of the
test on G_omega enters is what the library's testCore returns at that term.
Premises, all on the plan: from key_of_fold on: blocks Q = some bs, withU Q.S = some sentU and
sharedSplitNeeded (so the case of two codes alone); at onGu_core and shape_behind_nine besides: the
test's parameters have early = true and answers = 1.

Names.
  endOf   the shape behind "SPLIT", from the shape of the chain's first state at the library's
      written key: a term of the plan and of what goes out with o_u.
  laysRec_key   where "(rec_gamma)"'s function returns, the key's sizes fit.
  key_of_fold   where the fold over the eight returns, the key's sizes fit.
  endAt_endOf, sh_behind_eight_plan   the shape behind the eight is endOf.
  shape_at_U_plan   the shape of what the seat of the test on G_u enters.
  fallU, shape_fallU   a state of that shape made of the shape alone.
  onGu_core   the seated test on G_u on shapes.
  shape_behind_nine   the shape of what the seat of the test on G_omega enters behind it.

By what. sh_behind_eight, eight_of, eight_steps (MarksBehind.lean); upTo_step, endAt
(Johnson/Desc/K14/Shape/End.lean); keyB_eq (Lin.lean); first_shape (Run.lean); lift, sh2_lift
(Up.lean); doorU, door_enter, door_enterO (Door.lean); Eight.back3
(Johnson/Desc/K14/Honest/StepsBack.lean); testCore, k12_core_sh
(Johnson/Desc/K12/Honest/Shape/TestCore.lean); inside_ok (Johnson/Desc/K12/SeatLaws.lean).

Limits.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- endOf is a term with code. It is evaluated nowhere here.
- fallU is no state that a run reaches. Nothing is said of it here but its shape. Whether it passes
  the three tests that read the rows (stTidyB, stPlainB, claimsB) is not shown here.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.MarksBehind
import Johnson.Desc.K14.Shape.Up

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Desc.K14
open VerifiableInference.Desc VerifiableInference.Desc.Ground VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Keeps VerifiableInference.Desc.K12
open VerifiableInference.Desc.Own (keyFits)
open Desc.K14.Shape (Sh2 sh2 linSh endAt upTo upTo_step doorU door_enter door_enterO keyB keyB_eq
  first_shape lift sh2_lift)
open H2K.JointK (Gs Blk')
open Desc.K14.Honest (Eight firstW)
open ProofFile.Honest.Sh (testSh TestSh testCore k12_core_sh)

/-- **The shape behind "SPLIT", a term of the plan.** -/
def endOf (Q : P14) (sentU : Array OracleNotice) : Sh2 := upTo Q sentU 9 (sh2 (firstW Q))

/-- Where "(rec_gamma)"'s function returns, the key's sizes fit. -/
theorem laysRec_key (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    keyFits d.loc.key p.S.fold.index = true := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, hg, _⟩ := obind_ok h
  have hok : Ground.ok (laysRecL p d.loc) = true := by
    by_contra hno
    simp [guard, hno] at hg
  simp only [Ground.ok, laysRecL, List.all_cons, Bool.and_eq_true] at hok
  exact hok.1

/-- **Where the fold over the eight returns, the key's sizes fit.** -/
theorem key_of_fold (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) :
    keyFits key Q.par.S.fold.index = true := by
  obtain ⟨B, rfl⟩ := eight_of Q bs hb
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, R1, R2, R3, R4, R5, R6, R7, R8, C1, C2, C3, C4, C5, C6, C7,
    C8, n1, n2, n3, n4, n5, n6, n7, n8, h1, h2, h3, -, -, -, -, -⟩ := eight_steps h
  have e1 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d1 R1 C1 n1).1 rfl h1
  have e2 := (upTo_step hU hS B ft (sh2 (first Q.codes key)) _ d2 R2 C2 n2).2.1 e1 h2
  obtain ⟨-, -, k⟩ := B.back3 hU ft d2 d3 R3 C3 n3 h3
  have k1 := laysRec_key Q.par d2 d3 _ k
  rw [← keyB_eq] at k1
  have e : keyB (sh2 d2).lin Q.par.S.fold.index = true := k1
  rw [e2] at e
  have e' : keyB (linSh (first Q.codes key).loc) Q.par.S.fold.index = true := e
  rw [keyB_eq] at e'
  exact e'

/-- At a key whose sizes fit the two terms are one. -/
theorem endAt_endOf (Q : P14) (sentU : Array OracleNotice) (key : TableKey)
    (hk : keyFits key Q.par.S.fold.index = true) : endAt Q sentU key = endOf Q sentU := by
  unfold endAt endOf
  rw [first_shape Q key hk]

/-- **The shape behind the eight is one term of the plan.** -/
theorem sh_behind_eight_plan (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) : sh2 r.1 = endOf Q sentU := by
  rw [sh_behind_eight Q bs hb sentU hU hS ft key rs cols r h,
    endAt_endOf Q sentU key (key_of_fold Q bs hb sentU hU hS ft key rs cols r h)]

/-- **The shape of what the seat of the test on G_u enters is one term of the plan.** -/
theorem shape_at_U_plan (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) r.1 = .ok t) :
    testSh t = doorU (endOf Q sentU) := by
  rw [door_enter r.1 t ht, sh_behind_eight_plan Q bs hb sentU hU hS ft key rs cols r h]

/-- A state of that shape, made of the shape alone: what the seat of the test on G_u enters at the
lift of the term. -/
def fallU (Q : P14) (sentU : Array OracleNotice) : T12 :=
  { st := (lift (endOf Q sentU)).st, book := (lift (endOf Q sentU)).book
    roots := (lift (endOf Q sentU)).roots, g := (lift (endOf Q sentU)).loc.gU, pass := .nothing
    mask := (lift (endOf Q sentU)).loc.firstMask }

theorem shape_fallU (Q : P14) (sentU : Array OracleNotice) :
    testSh (fallU Q sentU) = doorU (endOf Q sentU) := by
  have h := door_enter (lift (endOf Q sentU)) (fallU Q sentU) rfl
  rw [h, sh2_lift]

/-! ## Through the test on G_u -/

/-- **The seated test on G_u on shapes**: the core's shape behind is the library's function of the
core's shape in front; what the kind notes stays. -/
theorem onGu_core (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') :
    testCore p (coreSh ⟨d.st, d.book, d.roots⟩) d.loc.gU d.loc.firstMask =
        some (coreSh ⟨d'.st, d'.book, d'.roots⟩) ∧ d'.loc = d.loc := by
  obtain ⟨t, t', h1, h2, h3⟩ := (Seat.inside_ok _ _ _ d d' rs gs).1 h
  obtain rfl := Except.ok.inj h1
  obtain rfl := Except.ok.inj h3
  have c : testCore p (coreSh ⟨d.st, d.book, d.roots⟩) d.loc.gU d.loc.firstMask =
      some (coreSh ⟨t'.st, t'.book, t'.roots⟩) :=
    k12_core_sh p he ha { st := d.st, book := d.book, roots := d.roots, g := d.loc.gU
                          pass := .nothing, mask := d.loc.firstMask } t' rs gs h2
  exact ⟨c, rfl⟩

/-- **The shape of what the seat of the test on G_omega enters, wherever the fold over the eight and
the test on G_u returns**: the library's function testCore returns at the plan's term, and the shape
is what it returns, with the plan's number of G_omega, nothing passed and no mask. -/
theorem shape_behind_nine (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (sentU : Array OracleNotice) (hU : withU Q.S = some sentU)
    (hS : Q.S.sharedSplitNeeded = true) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (x : St × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks ft (bs ++ [Seat.onGu (proximityTestKind guardedProximityTestParts p)]) (first Q.codes key) rs cols = .ok x)
    (ht : Seat.enter (·.gOmega) (fun _ => none) x.1 = .ok t) :
    ∃ c, testCore p (endOf Q sentU).core (endOf Q sentU).lin.gU (endOf Q sentU).lin.firstMask =
        some c ∧ testSh t = ⟨c, (endOf Q sentU).lin.gOmega, .nothing, none⟩ := by
  obtain ⟨d8, rs', cols', h8, h9⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
  have e8 := sh_behind_eight_plan Q bs hb sentU hU hS ft key rs cols _ h8
  obtain ⟨_, d9, k9, s9, h9⟩ := foldBlocks_cons_ok.1 h9
  simp only [foldBlocks, Except.ok.injEq] at h9
  subst h9
  obtain ⟨_, _, e9⟩ := ChainEnd.step_decide _ _ _ _ _ _ _ s9
  obtain ⟨c9, l9⟩ := onGu_core p he ha d8 d9 _ _ e9
  have e8' : sh2 d8 = endOf Q sentU := e8
  have c9' : testCore p (sh2 d8).core (sh2 d8).lin.gU (sh2 d8).lin.firstMask =
      some (coreSh ⟨d9.st, d9.book, d9.roots⟩) := c9
  rw [e8'] at c9'
  refine ⟨_, c9', ?_⟩
  obtain rfl := Except.ok.inj ht
  show (⟨coreSh ⟨d9.st, d9.book, d9.roots⟩, d9.loc.gOmega, .nothing, none⟩ : TestSh) = _
  rw [l9]
  show (⟨coreSh ⟨d9.st, d9.book, d9.roots⟩, (sh2 d8).lin.gOmega, .nothing, none⟩ : TestSh) = _
  rw [e8']

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.endOf
#print axioms ProofFile.Honest.K12.Light.laysRec_key
#print axioms ProofFile.Honest.K12.Light.key_of_fold
#print axioms ProofFile.Honest.K12.Light.endAt_endOf
#print axioms ProofFile.Honest.K12.Light.sh_behind_eight_plan
#print axioms ProofFile.Honest.K12.Light.shape_at_U_plan
#print axioms ProofFile.Honest.K12.Light.fallU
#print axioms ProofFile.Honest.K12.Light.shape_fallU
#print axioms ProofFile.Honest.K12.Light.onGu_core
#print axioms ProofFile.Honest.K12.Light.shape_behind_nine
