-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/AtOracle.lean: the three chains of a file that the verifier program's reader has
read are read with the same outcome by the strict reader at the hash that the realised oracle on
byte strings induces, within bounds on file and descriptions that can be tested.

Statements and proofs. The program reads at the format's own hash `Fmt.formatHash`. The laws on a typed
verifier under fixed oracle functions speak of the hash `Fmt.HO O` that a function O on byte strings
induces. At O := `Fmt.oracle` the two agree on the hash's domain, and the library shows that the
strict reader's calls lie in that domain within the bounds `OnBytes.Tie.smallFX`
(OnBytes/Tie/StoredDom.lean, `readChainX_HO`). Here that law is called at the three chains.

Main names:
  `read_atOracle`: one chain.
  `SmallThree S₁ S₂ S₃ file`: the bounds at the three descriptions.
  `three_atOracle`: the three chains of `ThreeRead` (OnBytes/Maker/ThreeRead.lean), each from the
    record of vertices that the chain before it left.
  `three_firstO`: the three chains' heads (`HeadIs`, OnBytes/Maker/Page/FirstCalls.lean) at that
    hash.
  `oracle_32`: every answer of the realised oracle has 32 bytes (the library's `Fmt.size_oracle`).
Under "there is" stands rnd, twice, in `three_firstO`: fixed by the file's 32 bytes at the chain's
first byte.
Limits: the bounds are a premise: a test on the descriptions and the file's length. Nothing is said
at another O. Nothing on any page or typed query. At a letter p the labels `p.lab₂` and `p.lab₃` are
any numbers: they are the format's at `Key.tailPublic` and `Proof.tailPublic` alone. Nothing on
soundness.


-/
import OnBytes.Maker.Page.FirstCalls
import OnBytes.Tie.StoredDom

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Tie OnBytes.Maker
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
open OnBytes.Params (Rounds)

/-- **One chain**: what the program's reader has read, the strict reader reads at the hash over the
realised oracle. -/
theorem read_atOracle (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut)
    (j : ℕ) (e : readChain S seen b i = some (o, j)) (hS : smallFX S b = true) :
    Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle) S seen b i = some (o, j) := by
  rw [readChainX_HO S seen b i hS]
  exact (readChain_eq S seen b i).symm.trans e

/-- Every answer of the realised oracle has 32 bytes. -/
theorem oracle_32 : ∀ s, (Fmt.oracle s).size = 32 := Fmt.size_oracle

/-- The bounds at the three descriptions. -/
def SmallThree (S₁ S₂ S₃ : Fmt.SpecX) (file : ByteArray) : Prop :=
  smallFX S₁ file = true ∧ smallFX S₂ file = true ∧ smallFX S₃ file = true

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray}

/-- **The three chains of a file, at the hash over the realised oracle.** -/
theorem three_atOracle
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (hs : SmallThree S₁ S₂ S₃ file) :
    Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle) S₁ [] file i =
        some (r.first.out, r.first.next) ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle) S₂ r.first.out.seen file r.place.next =
        some (r.shared.out, r.shared.next) ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle) S₃ r.shared.out.seen file r.shared.next =
        some (r.second.out, r.second.next) :=
  ⟨read_atOracle _ _ _ _ _ _ T.first_read hs.1, read_atOracle _ _ _ _ _ _ T.shared_read hs.2.1,
    read_atOracle _ _ _ _ _ _ T.second_read hs.2.2⟩

/-- **The heads of the three chains, at the hash over the realised oracle.** -/
theorem three_firstO
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ .inFile R₁ 0 = some S₁)
    (hs : SmallThree S₁ S₂ S₃ file) :
    (∃ rnd, Fmt.slice file i 32 = some rnd ∧
        HeadIs (Fmt.HO Fmt.oracle) S₁ r.first.out l₁ x₁ rnd) ∧
      HeadIs (Fmt.HO Fmt.oracle) S₂ r.shared.out p.lab₂
        (Params.Shared.statement p.table r.place.root) r.place.root ∧
      ∃ rnd, Fmt.slice file r.shared.next 32 = some rnd ∧
        HeadIs (Fmt.HO Fmt.oracle) S₃ r.second.out p.lab₃
          (Params.Second.statement seal1 seal2) rnd := by
  obtain ⟨e₁, e₂, e₃⟩ := three_atOracle T hs
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃ (Proof.secondFirstTree r.first) =
        some S₃ := T.second_spec
  obtain ⟨n1, a1, b1⟩ := head_ofX _ hS₁ (fun e => by cases e) _ _ _ _ _ e₁
  obtain ⟨n2, a2, b2⟩ := head_ofX _ hS₂ (fun e => by cases e) _ _ _ _ _ e₂
  obtain ⟨n3, a3, b3⟩ := head_ofX _ hS₃ (fun e => by cases e) _ _ _ _ _ e₃
  unfold RandIs at a1 a2 a3
  rw [describeWith_rand hS₁] at a1
  rw [describeWith_rand hS₂] at a2
  rw [describeWith_rand hS₃] at a3
  have a2' : r.place.root = n2 := a2
  subst a2'
  exact ⟨⟨n1, a1, b1⟩, b2, n3, a3, b3⟩

end

end OnBytes.Maker.Page
