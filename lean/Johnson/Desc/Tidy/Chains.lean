-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Tidy/Chains.lean: along a chain whose blocks' steps each keep "tidy in front, tidy
behind" (`TidyStay`, Johnson/Desc/Tidy/Stay.lean) a tidy statement stays tidy; and which blocks of
the first and of the shared chain are shown to be such. Statements with their proofs.
Main names:
  `fold_tidy`, `chainAt_tidy`: **the rule**: general in the record, in the reader of the statement
    and in the list of blocks; `chainAt_tidy_start`: from the empty statement.
  `OursFirst b`: b is one of five blocks (K1's, K13's) of the first chain that turn the statement:
    W's sending; a segment's later moment; the first segment's opening; the joined block at the
    batching's place; W's commitment with the own group and (Eval) behind it.
  `oursFirst_steps`: **each of these keeps it.**
  `first_tidy`: so the first chain's last statement is tidy, if every other block of the list keeps
    it: a named premise, left to each block's files.
  `shared_steps`, `shared_tidy`: **the shared chain**: every block of its flat list keeps it, if the
    proximity tests' blocks do (a named premise: left to K12's files) and the last leaves the
    record; so the shared chain's last statement is tidy.

What is not claimed. That a description's first chain is made of such blocks. The blocks that leave
the statement as it is (the two quiet steps, the chain's end) keep it for that reason: their own
laws say that they leave it. Nothing on soundness.

-/
import Johnson.Desc.Tidy.Stay
import Johnson.Desc.Tidy.K1Steps
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K14.Quiet
import Johnson.Desc.K14.FlatList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps
open OnBytes
open OnBytes.Means (Tidy)
open VerifiableInference.Desc.Ground (By TidyStay groundQuiet_tidy admitOn_tidy)

variable {T Cl : Type}

/-- **Along a fold of blocks whose steps keep it, at a plan that passes.** -/
theorem fold_tidy (st : T → Statement) (ft : Nat) (bs : List (Block T Cl))
    (hb : ∀ b ∈ bs, Steps (By TidyStay st) b) (hp : ∀ b ∈ bs, b.planOk = true) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : T × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs s rs cols = .ok r) (hT : Tidy (st s)) : Tidy (st r.1) :=
  foldBlocks_steps (By TidyStay st) (fun _ x => x) (fun _ _ _ x y z => y (x z)) ft bs hb hp s rs
    cols r h hT

/-- The same of a chain's decision. -/
theorem chainAt_tidy (st : T → Statement) (name : String) (ft : Nat) (bs : List (Block T Cl))
    (hb : ∀ b ∈ bs, Steps (By TidyStay st) b) (hp : ∀ b ∈ bs, b.planOk = true) (s s' : T)
    (v : Fmt.View) (h : chainAt name ft bs s v = .ok s') (hT : Tidy (st s)) : Tidy (st s') :=
  fold_tidy st ft bs hb hp s _ _ (s', [], []) (chainAt_fold name ft bs s s' v h) hT

/-- From the empty statement. -/
theorem chainAt_tidy_start (st : T → Statement) (name : String) (ft : Nat)
    (bs : List (Block T Cl)) (hb : ∀ b ∈ bs, Steps (By TidyStay st) b)
    (hp : ∀ b ∈ bs, b.planOk = true) (s s' : T) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') (codes : Codes)
    (hs : st s = { codes := codes, oracles := #[], groups := #[] }) : Tidy (st s') :=
  chainAt_tidy st name ft bs hb hp s s' v h (hs ▸ Tidy.start codes)

end VerifiableInference.Desc.Keeps

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Means (Tidy)
open VerifiableInference.Desc.Ground (By TidyStay groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.Keeps (Steps steps_of_decides steps_of_fits andThen_fits
  chainAt_tidy_start)

variable {Cl : Type}

/-- Five blocks (K1's, K13's) of the first chain that turn the statement. -/
inductive OursFirst : Block S Cl → Prop
  | send (P : K1.Par) : OursFirst (K1.sendAtS P)
  | commit (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
      OursFirst (K1.commitAtS P link moment arrays)
  | opening (q : Params.First) (gp : GPar) : OursFirst (K1.firstSegmentOpening q gp)
  | batching (p : K13.Where) : OursFirst (K13.atM3 p)
  | commitW (p : K13.Where) (P : K1.Par) : OursFirst (K13.atM4 p (K1.sendAtS P))

/-- **Each of these keeps "tidy in front, tidy behind".** -/
theorem oursFirst_steps {b : Block S Cl} (h : OursFirst b) :
    Steps (By TidyStay fun s : S => s.st) b := by
  cases h with
  | send P => exact K1.sendAtS_steps groundQuiet_tidy admitOn_tidy P
  | commit P link moment arrays =>
    exact K1.commitAtS_steps groundQuiet_tidy admitOn_tidy P link moment arrays
  | opening q gp => exact K1.firstAtS_steps groundQuiet_tidy admitOn_tidy q gp
  | batching p => exact steps_of_decides (K13.atM3_keeps groundQuiet_tidy p)
  | commitW p P =>
    exact steps_of_fits (andThen_fits _ (fun _ _ _ x y z => y (x z)) _ _ _ rfl
      (K1.sendAtS_fits groundQuiet_tidy admitOn_tidy P)
      (K13.rowsB_keeps groundQuiet_tidy K13.atS _ K13.atS_lensSt p))

/-- **The first chain's last statement is tidy**, if every other block of the list keeps it. -/
theorem first_tidy (name : String) (ft : Nat) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, OursFirst b ∨ Steps (By TidyStay fun s : S => s.st) b)
    (hp : ∀ b ∈ bs, b.planOk = true) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') (codes : Codes)
    (hs : s.st = { codes := codes, oracles := #[], groups := #[] }) : Tidy s'.st :=
  chainAt_tidy_start (fun s : S => s.st) name ft bs
    (fun b hm => (hb b hm).elim oursFirst_steps id) hp s s' v h codes hs

end VerifiableInference.Desc.First

namespace Desc.K14
open OnBytes
open OnBytes.Means (Tidy)
open VerifiableInference.Desc
open VerifiableInference.Desc.Ground (By TidyStay groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.Keeps (Steps Decides steps_of_decides chainAt_tidy_start)

/-- **Every block of the shared chain's flat list keeps it**, if the tests' blocks do and the last
leaves the record. -/
theorem shared_steps (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (ht : ∀ b ∈ tests, Steps (By TidyStay fun d : St => d.st) b)
    (hl : Decides (By TidyStay fun d : St => d.st) (last (blocksOr P ++ tests))) :
    ∀ b ∈ (chainOf c P tests last).blocksInOrder, Steps (By TidyStay fun d : St => d.st) b := by
  intro b hb
  rcases flat_mem c P tests last b hb with ⟨b', hb', rfl⟩ | ⟨b', hb', rfl⟩ | rfl
  · refine steps_bare ?_
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact frontBlock_steps groundQuiet_tidy c
    · exact blocksOr_steps groundQuiet_tidy admitOn_tidy P b' hb'
  · exact steps_bare (ht b' hb')
  · exact steps_bare (steps_of_decides hl)

/-- **The shared chain's last statement is tidy.** -/
theorem shared_tidy (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (ht : ∀ b ∈ tests, Steps (By TidyStay fun d : St => d.st) b)
    (hl : Decides (By TidyStay fun d : St => d.st) (last (blocksOr P ++ tests)))
    (hp : ∀ b ∈ (chainOf c P tests last).blocksInOrder, b.planOk = true) (name : String) (ft : Nat)
    (s s' : St) (v : Fmt.View) (h : chainAt name ft (chainOf c P tests last).blocksInOrder s v = .ok s')
    (codes : Codes) (hs : s.st = { codes := codes, oracles := #[], groups := #[] }) :
    Tidy s'.st :=
  chainAt_tidy_start (fun d : St => d.st) name ft _ (shared_steps c P tests last ht hl) hp s s' v h
    codes hs

end Desc.K14
