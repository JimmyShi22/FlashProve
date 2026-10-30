-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Seam/ReaderWith.lean: a front verifier (`PortArmsC`, Johnson/Top/OnFilesPortC.lean) with
another reader: the typed key and the typed proof's part for the link are laid by a second
algorithm; the rest of what is returned is that of the front verifier's own reader. General in the
input r.

Why. The entry file's arm reads of what the reader returns the key and the part for the link alone
(`liftEC`, Johnson/Top/OnFilesArmsC.lean). But the key file's arm and the commitment ID's part read
the key too, and the proof file's arm reads the key's first component and the link's root and
record. So a front verifier whose key and link are laid anew owes its other parts at new arguments.
Here that debt gets one name: `AgreesKeyLink`.

Main names.
  `KeyLink r`: a typed key and a part for the link. `p.withKeyLink mk m`: p with the new reader.
  `parsed_withKeyLink`: what it returns at g. `budget_withKeyLink`: its budget, m + p.n:
    `front_sound` (Johnson/Top/FrontParts.lean) reads its ε at the adversary's queries plus this
    budget, and its δ at the adversary's queries alone.
  `p.AgreesKeyLink mk`: where p says yes at g, the key, the link's root and the link's record that
    p's own reader returns at g are those that mk returns at g. A proposition by definition.
  `agrees_withKeyLink`: a front verifier whose own reader is already made so agrees, by definition.
  What it carries: `left_withKeyLink`, Johnson/Top/Seam/ReaderWithLeft.lean [not in this library];
  so here read: not proved in this library.
  `queryBound_andThen`: the budget of one algorithm run behind another.

What is not claimed. r, p, mk, m are letters. That any p agrees with any mk. The link's third
component (the proof string for the entry file's arm) is not asked to agree. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.FrontParts

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference

/-- A budget of queries holds at every larger number. -/
theorem queryBound_mono_det {α : Type} : ∀ (a : DeterministicAlgorithm α) (s t : ℕ), s ≤ t →
    a.toRandomized.QueryBound s → a.toRandomized.QueryBound t
  | .done _, _, _, _, _ => trivial
  | .query _ _, 0, _, _, h => h.elim
  | .query _ _, s + 1, 0, hst, _ => absurd hst (Nat.not_succ_le_zero s)
  | .query _ k, s + 1, t + 1, hst, h =>
    fun r => queryBound_mono_det (k r) s t (Nat.le_of_succ_le_succ hst) (h r)

/-- One algorithm, then another on its result: the budgets add. -/
theorem queryBound_andThen {α β : Type} : ∀ (a : DeterministicAlgorithm α)
    (f : α → DeterministicAlgorithm β) (m k : ℕ), a.toRandomized.QueryBound m →
    (∀ x, (f x).toRandomized.QueryBound k) → (a.andThen f).toRandomized.QueryBound (m + k)
  | .done x, f, m, k, _, hf => queryBound_mono_det (f x) k (m + k) (Nat.le_add_left k m) (hf x)
  | .query _ _, _, 0, _, h, _ => h.elim
  | .query _ nx, f, m + 1, k, h, hf => by
    rw [Nat.succ_add]
    exact fun r => queryBound_andThen (nx r) f m k (h r) hf

end VerifiableInference

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A typed key, and a typed proof's part for the link: root, record, proof string. -/
abbrev KeyLink (r : InputArmsC) : Type :=
  (r.C × KeyRoot 256 r.L) × (Dig 256 × r.L.Rec × Option (OneProtocolProof 256 (batLC r.L r.aL)))

/-- The key file's arm reads of the typed proof the test's string alone. -/
theorem liftKC_congr (r : InputArmsC) {k k' : r.C × KeyRoot 256 r.L} (x : r.X)
    {π π' : OfflineLinkOnlineProof 256 r.L r.aT r.aL} (hk : k = k') (ht : π.piT = π'.piT) :
    liftKC r k x π = liftKC r k' x π' := by
  unfold liftKC
  rw [hk, ht]

/-- The proof file's arm reads of the typed proof the link's root and record, the copy's number and
the session's string. -/
theorem liftPC_congr (r : InputArmsC) {k k' : r.C × KeyRoot 256 r.L} (x : r.X)
    {π π' : OfflineLinkOnlineProof 256 r.L r.aT r.aL} (hk : k = k') (h1 : π.link.1 = π'.link.1)
    (h2 : π.link.2.1 = π'.link.2.1) (hc : π.copy = π'.copy) (hb : π.piB = π'.piB) :
    liftPC r k x π = liftPC r k' x π' := by
  unfold liftPC
  rw [hk, h1, h2, hc, hb]

variable {r : InputArmsC} (p : PortArmsC r)
  (mk : List Token → List Token → p.Files → DeterministicAlgorithm (KeyLink r)) (m : ℕ)

/-- p with another reader: run mk; run p's own reader; return what that returns, with the typed key
and the typed proof's part for the link replaced by mk's. Verifier, exception and price stay; the
budget of queries is m + p.n, m a letter for mk's. -/
def PortArmsC.withKeyLink : PortArmsC r :=
  { p with
    n := m + p.n
    reader := fun prompt output F =>
      (mk prompt output F).andThen fun kl =>
        (p.reader prompt output F).andThen fun v =>
          .done (v.1, (kl.1, { v.2.2 with link := kl.2 })) }

/-- What the new reader returns at g. -/
theorem parsed_withKeyLink (g : Hash) (prompt output : List Token) (F : p.Files) :
    (p.withKeyLink mk m).parsed g prompt output F =
      ((p.parsed g prompt output F).1, (((mk prompt output F).evaluate g).1,
        { (p.parsed g prompt output F).2.2 with
          link := ((mk prompt output F).evaluate g).2 })) := by
  unfold PortArmsC.parsed PortArmsC.withKeyLink
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  rfl

/-- Its budget of queries, from mk's and p's own. -/
theorem budget_withKeyLink
    (hm : ∀ prompt output F, (mk prompt output F).toRandomized.QueryBound m)
    (hp : ∀ prompt output F, (p.reader prompt output F).toRandomized.QueryBound p.n)
    (prompt output : List Token) (F : p.Files) :
    ((p.withKeyLink mk m).reader prompt output F).toRandomized.QueryBound (p.withKeyLink mk m).n :=
  queryBound_andThen _ _ m p.n (hm prompt output F) fun _ =>
    queryBound_andThen _ _ p.n 0 (hp prompt output F) fun _ => trivial

/-- Where p says yes at g: the key, the link's root and the link's record that p's own reader
returns at g are those that mk returns at g. -/
def PortArmsC.AgreesKeyLink : Prop :=
  ∀ (g : Hash) (c : Commitment) (prompt output : List Token) (F : p.Files),
    p.Yes g c prompt output F →
    (p.parsed g prompt output F).2.1 = ((mk prompt output F).evaluate g).1 ∧
      (p.parsed g prompt output F).2.2.link.1 = ((mk prompt output F).evaluate g).2.1 ∧
      (p.parsed g prompt output F).2.2.link.2.1 = ((mk prompt output F).evaluate g).2.2.1

/-- A front verifier whose own reader is already made so agrees with mk: by definition. -/
theorem agrees_withKeyLink : (p.withKeyLink mk m).AgreesKeyLink mk := by
  intro g c prompt output F _
  rw [parsed_withKeyLink]
  exact ⟨rfl, rfl, rfl⟩

end VerifiableInference.OnPublicFiles
