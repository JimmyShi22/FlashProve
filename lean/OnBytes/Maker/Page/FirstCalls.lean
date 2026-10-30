-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FirstCalls.lean: the first value and the run's value of a chain that the strict
reader has read, written out as the format's own hash calls: the reader's side of the first call of
each of a file's three chains.

Statements and proofs, at any function h for the hash. OnBytes/Maker/ReadTrace.lean says that a
chain's head was made by `Fmt.startChainW` from the parameters' digest, the statement and the random
bytes. Here that call is opened. A page that lays a typed verifier's first query of a chain onto the
format's strings has to give these very calls.

Main names:
  `pdOf h S`: the parameters' digest: the call 169.
  `start_some`: a head that was made from random bytes rnd: they have 32 bytes; the run's value is
    the call 172 at the label, on the parameters' digest and rnd; it is not 32 zero bytes; the first
    value is the call 160 at the label, on `Fmt.firstBytes` of the parameters' digest, the
    statement, no record and the run's value.
  `RandIs S b i rnd`: rnd are the description's random bytes: the 32 bytes of b from i on, or the
    bytes that the description gives.
  `readX_first`: a chain that the strict reader has read under a description with random bytes.
  `HeadIs h S o label st rnd`: the same in one record, with the label, the statement and the random
    bytes named. `head_ofX`: at a description made by `Params.describeWith`, at any h.
  `three_first`: the three chains of a file (`ThreeRead`, OnBytes/Maker/ThreeRead.lean), at the
    format's hash: the first and the third have their random bytes in the file, the shared chain's
    are the binding tree's root as read.
Under "there is" stands rnd alone, fixed by `RandIs`.
Limits: nothing is said of any page or of any typed query here. `three_first` speaks at the format's
hash `Fmt.formatHash`, at which the program reads; for a reading at another h: `head_ofX`. No file beside
this one calls `readChain_first`. At a letter p the labels `p.lab₂` and `p.lab₃` are any numbers:
they are the format's at `Key.tailPublic` and `Proof.tailPublic` alone. Nothing on soundness.


-/
import OnBytes.Maker.ReadRuns
import OnBytes.Maker.ThreeRead

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
open OnBytes.Params (Rounds)

/-- The parameters' digest of a description. -/
def pdOf (h : HId) (S : Fmt.SpecX) : ByteArray := h 169 0 1 Fmt.zero32 S.base.params

/-- **A head that was made from random bytes.** -/
theorem start_some (h : HId) (lab : ℕ) (pd st rnd : ByteArray) (hd : Fmt.ChainHead)
    (e : Fmt.startChainW (m := Id) h lab pd st (some rnd) = some hd) :
    lab < 2 ^ 32 ∧ rnd.size = 32 ∧ hd.run = some (h 172 0 lab Fmt.zero32 (pd ++ rnd)) ∧
      Fmt.runOk (h 172 0 lab Fmt.zero32 (pd ++ rnd)) = true ∧
      hd.rho0 = h 160 0 lab Fmt.zero32
        (Fmt.firstBytes pd st ByteArray.empty (some (h 172 0 lab Fmt.zero32 (pd ++ rnd)))) := by
  unfold Fmt.startChainW at e
  split at e
  · rename_i hl
    dsimp only at e
    split at e
    · rename_i hs
      simp only [idb] at e
      split at e
      · rename_i hr
        simp only [idp] at e
        obtain rfl := Option.some.inj e
        exact ⟨hl, hs, rfl, hr, rfl⟩
      · cases e
    · cases e
  · cases e

/-- rnd are the description's random bytes. -/
def RandIs (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (rnd : ByteArray) : Prop :=
  match S.base.rand with
  | .inFile => Fmt.slice b i 32 = some rnd
  | .given x => x = rnd
  | .none => False

/-- **A chain that the strict reader has read under a description with random bytes**: its run's
value and its first value, as the format's calls. -/
theorem readX_first (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hr : S.base.rand ≠ .none) :
    ∃ rnd, RandIs S b i rnd ∧ rnd.size = 32 ∧
      o.run = some (h 172 0 S.base.label Fmt.zero32 (pdOf h S ++ rnd)) ∧
      o.rho0 = h 160 0 S.base.label Fmt.zero32
        (Fmt.firstBytes (pdOf h S) S.base.statement ByteArray.empty o.run) := by
  obtain ⟨x, i0, h1, h2, -⟩ := readX_trace h S seen b i o j e
  have hx : ∃ rnd, x = some rnd ∧ RandIs S b i rnd := by
    unfold Fmt.rndOf at h1
    unfold RandIs
    cases hS : S.base.rand with
    | none => exact absurd hS hr
    | given y =>
      rw [hS] at h1
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h1)
      exact ⟨y, rfl, rfl⟩
    | inFile =>
      rw [hS] at h1
      cases hs : Fmt.slice b i 32 with
      | none => rw [hs] at h1; cases h1
      | some z =>
        rw [hs] at h1
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h1)
        exact ⟨z, rfl, rfl⟩
  obtain ⟨rnd, rfl, hR⟩ := hx
  obtain ⟨-, a2, a3, -, a5⟩ := start_some h _ _ _ rnd ⟨o.run, o.rho0⟩ h2
  have a3' : o.run = some (h 172 0 S.base.label Fmt.zero32 (pdOf h S ++ rnd)) := a3
  refine ⟨rnd, hR, a2, a3', ?_⟩
  rw [a3']
  exact a5

/-- The same of the reader that the program runs. -/
theorem readChain_first (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (hr : S.base.rand ≠ .none) :
    ∃ rnd, RandIs S b i rnd ∧ rnd.size = 32 ∧
      o.run = some (Fmt.formatHash 172 0 S.base.label Fmt.zero32 (pdOf Fmt.formatHash S ++ rnd)) ∧
      o.rho0 = Fmt.formatHash 160 0 S.base.label Fmt.zero32
        (Fmt.firstBytes (pdOf Fmt.formatHash S) S.base.statement ByteArray.empty o.run) :=
  readX_first Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e) hr

/-- What is said of one chain's head: the random bytes rnd, the label and the statement named. -/
structure HeadIs (h : HId) (S : Fmt.SpecX) (o : Fmt.ChainOut) (label : ℕ) (st rnd : ByteArray) :
    Prop where
  label_eq : S.base.label = label
  statement_eq : S.base.statement = st
  size : rnd.size = 32
  run : o.run = some (h 172 0 label Fmt.zero32 (pdOf h S ++ rnd))
  rho0 : o.rho0 = h 160 0 label Fmt.zero32 (Fmt.firstBytes (pdOf h S) st ByteArray.empty o.run)

/-- The label of a description that is returned is the argument. -/
theorem describeWith_label {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.label = label := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

/-- The statement of a description that is returned is the argument. -/
theorem describeWith_st {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) : S.base.statement = st := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]

/-- One chain that the strict reader has read, at any h, under a description made by
`Params.describeWith`. -/
theorem head_ofX (h : HId) {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (hS : Params.describeWith g label st rand R ft = some S) (hn : rand ≠ .none) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∃ rnd, RandIs S b i rnd ∧ HeadIs h S o label st rnd := by
  obtain ⟨rnd, h1, h2, h3, h4⟩ := readX_first h S seen b i o j e
    (by rw [describeWith_rand hS]; exact hn)
  rw [describeWith_label hS] at h3 h4
  rw [describeWith_st hS] at h4
  exact ⟨rnd, h1, describeWith_label hS, describeWith_st hS, h2, h3, h4⟩

/-- The same of the reader that the program runs. -/
theorem head_of {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand} {R : Rounds}
    {ft : ℕ} {S : Fmt.SpecX} (hS : Params.describeWith g label st rand R ft = some S)
    (hn : rand ≠ .none) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : readChain S seen b i = some (o, j)) :
    ∃ rnd, RandIs S b i rnd ∧ HeadIs Fmt.formatHash S o label st rnd :=
  head_ofX Fmt.formatHash hS hn seen b i o j ((readChain_eq S seen b i).symm.trans e)

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray}

/-- **The heads of the three chains of a file as read.** The first and the third chain have their
random bytes in the file; the shared chain's are the binding tree's root as read. -/
theorem three_first (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁) :
    (∃ rnd, Fmt.slice file i 32 = some rnd ∧ HeadIs Fmt.formatHash S₁ r.first.out l₁ x₁ rnd) ∧
      HeadIs Fmt.formatHash S₂ r.shared.out p.lab₂
        (Params.Shared.statement p.table r.place.root) r.place.root ∧
      ∃ rnd, Fmt.slice file r.shared.next 32 = some rnd ∧
        HeadIs Fmt.formatHash S₃ r.second.out p.lab₃ (Params.Second.statement seal1 seal2)
          rnd := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃ (Proof.secondFirstTree r.first) =
        some S₃ := T.second_spec
  obtain ⟨n1, a1, b1⟩ := head_of hS₁ (fun e => by cases e) _ _ _ _ _ T.first_read
  obtain ⟨n2, a2, b2⟩ := head_of hS₂ (fun e => by cases e) _ _ _ _ _ T.shared_read
  obtain ⟨n3, a3, b3⟩ := head_of hS₃ (fun e => by cases e) _ _ _ _ _ T.second_read
  unfold RandIs at a1 a2 a3
  rw [describeWith_rand hS₁] at a1
  rw [describeWith_rand hS₂] at a2
  rw [describeWith_rand hS₃] at a3
  have a2' : r.place.root = n2 := a2
  subst a2'
  exact ⟨⟨n1, a1, b1⟩, b2, n3, a3, b3⟩

end

end OnBytes.Maker.Page
