-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallGoodOfToy.lean: `RunsLaw` HAS MEMBERS, THE BOOL `goodAt` IS TRUE AT
THEM, AND `batFall_few_bool` BITES. Statements and proofs at made-up segments, at the real type of states
`First.S`, K9's own batching and the frame's own gatherer. No goal is stated.

THE FIRST MEMBER: the segment of Honest/K9/Toy.lean (`laws`, `bool`, `count_le2`).
THE SECOND MEMBER (`laws'`, `bool'`, `count_le'`, `count_pos'`): a segment whose run of claims
  - HANGS ON chi: the first claim's constant is chi itself;
  - REFUSES AT ONE chi: at chi = 3 the gatherer answers nothing;
  - HAS A CLAIM UNDER A HIGHER POWER (eqFirst = some 0), which names no slot and whose constant is chi;
  - HAS A MERGE: a third slot, the merge's, which no claim names.
So `same` is met by claims that are NOT the same at two challenges, and `gathered` does not answer
everywhere. n = 3; the plan has three claims: at most 3 * 2 readings; at least one: chi = 1.
NOT SHOWN: a run that turns the state or the ledger's side (the toy's run hands the state on as it came);
a segment at which `same` fails; the Bool false at two challenges. The refusal at chi = 3 is by words.
A TOY: nothing on a segment of the protocol. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallGoodOf
import Johnson.Desc.ProofFile.Honest.K9.FallFewToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9.Toy
open OnBytes OnBytes.Model
open VerifiableInference.Desc (claimsInBy Claim Block Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (batch mergeOf atS drawAlone drawnClean drawn ledgerEmpty Where)

/-! ## The first member -/

theorem yields (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h : gathered pw gat (sD held) x = some y) :
    y.2.1.F = Fx x ∧ y.2.2 = [cl0, cl1] ∧ mergeOf y.1 = none := by
  have h1 := gathered_toy x
  rw [h] at h1
  have h2 := Option.some.inj h1
  exact ⟨congrArg (·.1) h2, congrArg (·.2.1) h2, congrArg (·.2.2) h2⟩

theorem laws : RunsLaw pw gat (sD held) where
  ledger := fun x y h => by
    obtain ⟨e, _, _⟩ := yields x y h
    rw [e]
    exact ⟨rfl, rfl, emptyX x⟩
  same := fun x x' y y' h h' => by
    obtain ⟨e1, e2, e3⟩ := yields x y h
    obtain ⟨f1, f2, f3⟩ := yields x' y' h'
    rw [e1, e2, e3, f1, f2, f3]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem bool : (gathered pw gat (sD held) oneE).map (goodAt 2) = some true := by decide +kernel

theorem count_le2 : Prob.cnt Speaks ≤ 2 * (2 - 1) := by
  have hb := bool
  cases hq : gathered pw gat (sD held) oneE with
  | none => rw [hq] at hb; exact nomatch hb
  | some y =>
    rw [hq] at hb
    have h := batFall_few_bool pw gat (sD held) laws 2 oneE y hq (Option.some.inj hb)
    rw [(yields oneE y hq).1] at h
    exact h

/-! ## The second member -/

/-- The claims where chi is drawn: the first one's constant is chi; the third stands under a higher
power, names no slot, and has chi as its constant. -/
def clsAt (x : E) : List Claim :=
  [{ form := { cl0.form with const := x } }, cl1, { form := Aff.ofConst x, eqFirst := some 0 }]

/-- The run of claims. -/
def runC (_ : Nat) (s : S) : Except String (List Claim × S) :=
  match s.fork? with
  | some F =>
    if F.theta == e 3 then .error "the toy's run refuses at chi = 3" else .ok (clsAt F.theta, s)
  | none => .error "no segment"

def hearC : Block S Claim := { hearB with claims := [("own", runC)] }

def lkC : Link S Claim := { lk with hear := [hearC] }

def gatC : S → Except String (List Claim × S) := claimsInBy lkC.each lkC.hear lkC.order

/-- Three slots, all filled; the plan has three claims. -/
def FC : Fork :=
  { planClaimsF := 3, ns := 3, next := 3, LS := #[zeroE, zeroE, zeroE]
    vp := #[e 607, e 1204, e 5], mf := #[beta, beta, beta], gotF := #[true, true, true] }

def tlC : HTailF2 := { slotB := 3, eqFirst := #[0] }

/-- The state in front of the draw, with the merge's end value under slot 2. -/
def sC : S := withMerge 2 { base.enterLay LD FC tlC with st := stD }

def pwC : Where := { pw with rows := 3 }

def FxC (x : E) : Fork :=
  { t2FillL FC LD.list with theta := x, thetaDrawnF := true, kapMapF := Array.replicate 3 false }

def partC : VerifiableInference.Desc.K9.Part :=
  { owed := none, used := 3, laid := some 0, L := LD, F := FC,
    d := { st := stD, book := sC.book, roots := sC.roots, opened := [], loc := () } }

theorem clean_C (x : E) : drawnClean 3 x none 3 LD FC =
    .ok ⟨some 3, { LD with list := { LD.list with used := 3 }, handed := true }, FxC x⟩ := by
  have hE : ledgerEmpty FC = true := by decide +kernel
  have hd : drawn 3 x none 3 LD FC =
      .ok ⟨some 3, { LD with list := { LD.list with used := 3 }, handed := true }, FxC x⟩ := rfl
  unfold drawnClean
  rw [hd, hE]
  rfl

/-- The book-keeping behind the draw. -/
def LDh : LinkCtx := { LD with list := { LD.list with used := 3 }, handed := true }

/-- The state behind the draw of x. -/
def tC (x : E) : S := atS.set sC { partC with owed := some 3, L := LDh, F := FxC x }

theorem draw_C (x : E) :
    (drawAlone (Cl := Claim) atS pwC).decide sC [⟨[], drawnOne x⟩] [] = .ok (tC x) := by
  have h1 : (drawAlone (Cl := Claim) atS pwC).decide sC [⟨[], drawnOne x⟩] [] =
      (drawnClean 3 x none 3 LD FC).bind fun o =>
        .ok (atS.set sC { partC with owed := o.owed, L := o.L, F := o.F }) := rfl
  rw [h1, clean_C]
  rfl

/-- The run behind the draw, as one `if`. -/
theorem run_C (x : E) : runC 0 (tC x) =
    if x == e 3 then .error "the toy's run refuses at chi = 3" else .ok (clsAt x, tC x) := rfl

/-- The frame's gatherer at this segment is the one run. -/
theorem gat_ok (t : S) (y : List Claim × S) (h : runC 0 t = .ok y) : gatC t = .ok y := by
  have e1 : gatC t = VerifiableInference.Desc.claimsInStep lkC.each lkC.hear ([], t) (0, "own") := rfl
  rw [e1]
  have hl : VerifiableInference.Desc.named ("own" ++ ": no such run")
      ((lkC.hear[0]?).bind fun b => b.claims.lookup "own") = .ok runC := rfl
  unfold VerifiableInference.Desc.claimsInStep
  dsimp only
  rw [hl]
  simp only [Except.bind]
  have h' : runC ([] : List Claim).length t = _ := h
  rw [h']
  rfl

theorem gat_no (t : S) (m : String) (h : runC 0 t = .error m) : gatC t = .error ("own: " ++ m) := by
  have e1 : gatC t = VerifiableInference.Desc.claimsInStep lkC.each lkC.hear ([], t) (0, "own") := rfl
  rw [e1]
  have hl : VerifiableInference.Desc.named ("own" ++ ": no such run")
      ((lkC.hear[0]?).bind fun b => b.claims.lookup "own") = .ok runC := rfl
  unfold VerifiableInference.Desc.claimsInStep
  dsimp only
  rw [hl]
  simp only [Except.bind]
  have h' : runC ([] : List Claim).length t = _ := h
  rw [h']
  rfl

theorem gathered_C_no (x : E) (hx : (x == e 3) = false) :
    (gathered pwC gatC sC x).map (fun y => (y.2.1.F, y.2.2, mergeOf y.1)) =
      some (FxC x, clsAt x, some 2) := by
  have hg : gatC (tC x) = .ok (clsAt x, tC x) := by
    apply gat_ok
    rw [run_C, hx]
    rfl
  unfold gathered
  simp only [draw_C, hg]
  rfl

theorem gathered_C_yes (x : E) (hx : (x == e 3) = true) : gathered pwC gatC sC x = none := by
  have hg : gatC (tC x) = .error ("own: " ++ "the toy's run refuses at chi = 3") := by
    apply gat_no
    rw [run_C, hx]
    rfl
  unfold gathered
  simp only [draw_C, hg]

theorem yieldsC (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h : gathered pwC gatC sC x = some y) :
    y.2.1.F = FxC x ∧ y.2.2 = clsAt x ∧ mergeOf y.1 = some 2 := by
  cases hx : x == e 3 with
  | true => rw [gathered_C_yes x hx] at h; exact nomatch h
  | false =>
    have h1 := gathered_C_no x hx
    rw [h] at h1
    have h2 := Option.some.inj h1
    exact ⟨congrArg (·.1) h2, congrArg (·.2.1) h2, congrArg (·.2.2) h2⟩

theorem emptyC (x : E) (j : Nat) : (FxC x).LS.getD j zeroE = zeroE := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- **The second member**: the claims hang on chi, the gatherer refuses at one chi, a claim stands
under a higher power, and there is a merge. -/
theorem laws' : RunsLaw pwC gatC sC where
  ledger := fun x y h => by
    obtain ⟨e1, _, _⟩ := yieldsC x y h
    rw [e1]
    exact ⟨rfl, rfl, emptyC x⟩
  same := fun x x' y y' h h' => by
    obtain ⟨e1, e2, e3⟩ := yieldsC x y h
    obtain ⟨f1, f2, f3⟩ := yieldsC x' y' h'
    rw [e1, e2, e3, f1, f2, f3]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The claims at two challenges are not the same. -/
theorem claims_differ : (clsAt oneE).map (·.form.const) ≠ (clsAt (e 5)).map (·.form.const) := by
  decide +kernel

/-- At chi = 3 the gatherer answers nothing. -/
theorem refuses_at_three : gathered pwC gatC sC (e 3) = none := gathered_C_yes (e 3) rfl

theorem bool' : (gathered pwC gatC sC oneE).map (goodAt 3) = some true := by decide +kernel

/-- The set that is counted, at the second member. -/
def Speaks' (y : GE) : Prop :=
  ∃ x : E, ρ.val x = y ∧
    (batFallTest (batch atS pwC gatC) 3 (fun _ _ => none) (fun _ => none) sC
      [drawnOne x]).isSome = true

theorem count_le' : Prob.cnt Speaks' ≤ 3 * (3 - 1) := by
  have hb := bool'
  cases hq : gathered pwC gatC sC oneE with
  | none => rw [hq] at hb; exact nomatch hb
  | some y =>
    rw [hq] at hb
    have h := batFall_few_bool pwC gatC sC laws' 3 oneE y hq (Option.some.inj hb)
    rw [(yieldsC oneE y hq).1] at h
    exact h

theorem speaks_at_one' :
    (batFallTest (batch atS pwC gatC) 3 (fun _ _ => none) (fun _ => none) sC
      [drawnOne oneE]).isSome = true := by decide +kernel

theorem silent_at_five :
    (batFallTest (batch atS pwC gatC) 3 (fun _ _ => none) (fun _ => none) sC
      [drawnOne (e 5)]).isSome = false := by decide +kernel

/-- At chi = 5 the batching says yes: the silence there is not a refusal's. -/
theorem returns_at_five : (behindBat (batch atS pwC gatC) sC [drawnOne (e 5)]).isSome = true := by
  decide +kernel

theorem count_pos' : 0 < Prob.cnt Speaks' := by
  haveI : Nonempty {y : GE // Speaks' y} := ⟨⟨ρ.val oneE, oneE, rfl, speaks_at_one'⟩⟩
  exact Nat.card_pos

/-- A control: with the merge's slot named by a claim the Bool is false. -/
theorem bool_control :
    VerifiableInference.Desc.K9H.slotsLive 3 (some 1) (clsAt oneE) = false := by decide +kernel

end ProofFile.Honest.K9.Toy

#print axioms ProofFile.Honest.K9.Toy.laws
#print axioms ProofFile.Honest.K9.Toy.bool
#print axioms ProofFile.Honest.K9.Toy.count_le2
#print axioms ProofFile.Honest.K9.Toy.laws'
#print axioms ProofFile.Honest.K9.Toy.claims_differ
#print axioms ProofFile.Honest.K9.Toy.refuses_at_three
#print axioms ProofFile.Honest.K9.Toy.bool'
#print axioms ProofFile.Honest.K9.Toy.count_le'
#print axioms ProofFile.Honest.K9.Toy.speaks_at_one'
#print axioms ProofFile.Honest.K9.Toy.silent_at_five
#print axioms ProofFile.Honest.K9.Toy.returns_at_five
#print axioms ProofFile.Honest.K9.Toy.count_pos'
#print axioms ProofFile.Honest.K9.Toy.bool_control
#print axioms ProofFile.Honest.K9.Toy.yields
#print axioms ProofFile.Honest.K9.Toy.clsAt
#print axioms ProofFile.Honest.K9.Toy.runC
#print axioms ProofFile.Honest.K9.Toy.hearC
#print axioms ProofFile.Honest.K9.Toy.lkC
#print axioms ProofFile.Honest.K9.Toy.gatC
#print axioms ProofFile.Honest.K9.Toy.FC
#print axioms ProofFile.Honest.K9.Toy.tlC
#print axioms ProofFile.Honest.K9.Toy.sC
#print axioms ProofFile.Honest.K9.Toy.pwC
#print axioms ProofFile.Honest.K9.Toy.FxC
#print axioms ProofFile.Honest.K9.Toy.partC
#print axioms ProofFile.Honest.K9.Toy.clean_C
#print axioms ProofFile.Honest.K9.Toy.LDh
#print axioms ProofFile.Honest.K9.Toy.tC
#print axioms ProofFile.Honest.K9.Toy.draw_C
#print axioms ProofFile.Honest.K9.Toy.run_C
#print axioms ProofFile.Honest.K9.Toy.gat_ok
#print axioms ProofFile.Honest.K9.Toy.gat_no
#print axioms ProofFile.Honest.K9.Toy.gathered_C_no
#print axioms ProofFile.Honest.K9.Toy.gathered_C_yes
#print axioms ProofFile.Honest.K9.Toy.yieldsC
#print axioms ProofFile.Honest.K9.Toy.emptyC
#print axioms ProofFile.Honest.K9.Toy.Speaks'
