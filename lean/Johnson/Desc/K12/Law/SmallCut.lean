-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SmallCut.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition` (Johnson/Desc/K12/Law/ChainHolds.lean), from Booleans that run without Mathlib
beneath: the test of Johnson/Desc/K12/Law/SmallOk.lean (`smallOkB`) is the test of
Johnson/Desc/K12/Law/SmallOfPlaces.lean (`smallOk`), by a lemma. Statements and proofs.

Main names:
  `toBr`, `toBr2`: a computed bracket (four numbers) as the record `Br` of
    Johnson/Bridge/BaseCodesAt.lean.
  `nValsB_eq`, `ok_toBr`, `roundN_eq`, `choose2_eq`, `brN_eq`, `lastCl_eq`, `stepCl_eq`,
    `smallCl_eq`: piece by piece, each definition of SmallOk.lean is that of SmallOfPlaces.lean at
    `sgOf a`, `r s.st` and `toBr2 (B s.st)`.
  `smallOk_eq`: `smallOk (fun s => r s.st) (fun s => toBr2 (B s.st)) p = smallOkB r B p`.
  `k12Condition_native`: `pubOk p K`, `spendOk p`, `johOk p r` and `smallOkB r B p` give
    `K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K (2⁻¹ ^ 128)`, by
    `k12Condition_of_four` of SmallOfPlaces.lean. There is no premise beside the four Booleans. r
    and B are letters: any radii and brackets at which the four say yes.
What `K12Condition` is worth (ChainHolds.lean, OwnMask.lean): the place's own chain over its
declared rounds has `Chain.Holds`, and each round's count is at most 2⁻¹ ^ 128 of that round's
written verifier messages.
Limits. No soundness of a release and no level of security is claimed. (1) One round's share, test
bits among the messages: W of the 128 bits are work; no sum over rounds. (2) The round "BAT" stands
in front of the chain and is not in it. (3) Of the chain, not of the block: «no witness within the
first stage's radius» and «the block's yes gives the chain's» are premises of what spends the
condition. (4) The first stage's radius stands in that statement: to pick r is to pick what is said
of the committed word. (5) The counts behind `Sg.flC` and `Sg.flZ` rest on the theorem on codes, and
so on the files under ThirdParty/, adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15). (6) That the Booleans say yes at a
place is a run's word. No text that runs asks `johOk` or `smallOkB`.
Sources. SmallOfPlaces.lean was written with six files of Johnson/Bridge/ open, and
it calls two of their names (`Br`, `below_of_num`). This file takes no run of their text; it names
`Br` and its four fields.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SmallOfPlaces
import Johnson.Desc.K12.Law.SmallOk
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open Cb
open VerifiableInference.Desc.K12 (P12)
open Johnson.Bridge (Br)

/-- A computed bracket as the record of four numbers. -/
def toBr (b : BrN) : Br := ⟨b.m, b.a, b.b, b.N⟩

def toBr2 (b : BrN × BrN) : Br × Br := (toBr b.1, toBr b.2)

theorem nValsB_eq : ∀ ds : List Fmt.Draw, nValsB ds = nVals ds
  | [] => rfl
  | .elem :: ds => by show _ * nValsB ds = _ * nVals ds; rw [nValsB_eq ds]
  | .elemNZ :: ds => by show _ * nValsB ds = _ * nVals ds; rw [nValsB_eq ds]
  | .pos _ :: ds => by show _ * nValsB ds = _ * nVals ds; rw [nValsB_eq ds]
  | .trits _ :: ds => by show _ * nValsB ds = _ * nVals ds; rw [nValsB_eq ds]
  | .sealed :: ds => by show _ * nValsB ds = _ * nVals ds; rw [nValsB_eq ds]

theorem ok_toBr (w : BrN) (n k e : ℕ) : (toBr w).ok n k e = w.ok n k e := by
  unfold Br.ok BrN.ok cntLeB CntLe toBr
  simp only [Bool.decide_and, Bool.and_assoc]

theorem roundN_eq (w : WR) (count : ℕ) : roundB w count = roundN w count := by
  unfold roundB roundN
  simp only [nValsB_eq]

theorem choose2_eq (n : ℕ) : n.choose 2 = choose2 n := Nat.choose_two_right n

theorem brN_eq (a : Fmt.M1.Stage) (e : ℕ) (b : BrN × BrN) :
    brB (sgOf a) e (toBr2 b) = brN a e b := by
  unfold brB brN toBr2
  rw [ok_toBr, ok_toBr]
  rfl

theorem lastCl_eq (a : Fmt.M1.Stage) (e : ℕ) (b : BrN × BrN) (dL dB' : WR) :
    lastCl (sgOf a) e (toBr2 b) dL dB' = lastClB a e b dL dB' := by
  unfold lastCl lastClB
  rw [brN_eq, roundN_eq, roundN_eq]
  rfl

theorem stepCl_eq (a a' : Fmt.M1.Stage) (e e' : ℕ) (b : BrN × BrN) (dE dT dS dC : WR) :
    stepCl (sgOf a) (sgOf a') e e' (toBr2 b) dE dT dS dC = stepClB a a' e e' b dE dT dS dC := by
  unfold stepCl stepClB
  rw [brN_eq, roundN_eq, roundN_eq, roundN_eq, roundN_eq, roundN_eq, choose2_eq]
  rfl

theorem smallCl_eq (r : Fmt.M1.Stage → ℕ) (B : Fmt.M1.Stage → BrN × BrN) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (a : Fmt.M1.Stage) (l : List WR),
    smallCl (fun s => r s.st) (fun s => toBr2 (B s.st)) j a rest l = smallClB r B j a rest l
  | [], j, a, l => by
    rcases l with _ | ⟨dL, _ | ⟨dB', _ | ⟨x, l'⟩⟩⟩
    · simp only [smallCl, smallClB]
    · simp only [smallCl, smallClB]
    · simp only [smallCl, smallClB]
      rw [lastCl_eq]
      rfl
    · simp only [smallCl, smallClB]
  | b :: rest, j, a, l => by
    rcases l with _ | ⟨dE, _ | ⟨dT, l'⟩⟩
    · simp only [smallCl, smallClB]
    · simp only [smallCl, smallClB]
    · simp only [smallCl, smallClB]
      rcases hd : (dT :: l').drop (kk a) with _ | ⟨dS, _ | ⟨dC, l''⟩⟩
      · rfl
      · rfl
      · show tag j (stepCl _ _ _ _ _ dE dT dS dC) ++ smallCl _ _ (j + 1) b rest l'' = _
        rw [stepCl_eq, smallCl_eq r B rest (j + 1) b l'']
        rfl

/-- **The two tests are one**: `smallOkB` at radii r and brackets B is `smallOk` at rad := fun s =>
r s.st and the same brackets as records. -/
theorem smallOk_eq (r : Fmt.M1.Stage → ℕ) (B : Fmt.M1.Stage → BrN × BrN) (p : P12) :
    smallOk (fun s => r s.st) (fun s => toBr2 (B s.st)) p = smallOkB r B p := by
  unfold smallOk smallOkB smallAll smallAllB
  rcases p.nums.stages with _ | ⟨a, rest⟩
  · rfl
  · rcases writtenOf p.nums with _ | (_ | ⟨w0, l⟩)
    · rfl
    · rfl
    · show ok (smallCl _ _ 0 a rest l) = ok (smallClB r B 0 a rest l)
      rw [smallCl_eq]

/-- **The condition from four Booleans without Mathlib beneath**: `pubOk p K`, `spendOk p`, `johOk p
r` and `smallOkB r B p` give `K12Condition` at the library's Johnson letters, the radii r and the
bound 2⁻¹ ^ 128. -/
theorem k12Condition_native (r : Fmt.M1.Stage → ℕ) (B : Fmt.M1.Stage → BrN × BrN)
    (p : P12) (K : Codes)
    (hp : pubOk p K = true) (hs : spendOk p = true) (hj : johOk p r = true)
    (hm : smallOkB r B p = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) p K ((2 : ENNReal)⁻¹ ^ 128) :=
  k12Condition_of_four r (fun s => toBr2 (B s.st)) p K hp hs hj (by rw [smallOk_eq]; exact hm)

end H2K.Pub

#print axioms H2K.Pub.smallOk_eq
#print axioms H2K.Pub.k12Condition_native
