-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/TwinClose.lean: from the record of a proof file's reading to the equation of the
reader that is written over a monad with the hash as a letter (`M.Proof.readProof`,
OnBytes/ChecksWithHashAsArgument/M/Proof/File.lean), at the identity monad and any hash h at which the five hashing
steps of the reading have the outcome in the record, which is the program's, made at `Fmt.formatHash`; and so
at `Fmt.HO Fmt.oracle`, the hash over the realised oracle on strings, at a file that the verifier
program's reader has read.

Statements and proofs. Glue. The twin's strict reader at the identity monad is the library's at
every hash (`EngineAtId.readChain_id`, OnBytes/ChecksWithHashAsArgument/M/Chain/EngineAtId.lean).
The library's reads one outcome at `Fmt.HO Fmt.oracle` and at `Fmt.formatHash` within the bounds `SmallThree`
(`readAt_O`, OnBytes/Maker/Page/CollidesOracle.lean). The record is `ThreeRead`
(OnBytes/Maker/ThreeRead.lean).

Main names:
  `Ret w s a s'`: the reading w, run from the record of vertices s, returns a and leaves s'.
  `ret_pure`, `ret_bind`, `ret_need`, `ret_needM`, `ret_guard`, `ret_readNamed`, `ret_readTail`.
  `twin_returns`: at a letter h: the head's equation, the test on the first chain's parameters, the
    first description, the record, the three readings at h (`ReadAt h`), the place at h and the
    table's key at h give `fromStart (M.Proof.readProof (m := Id) h ..) = .ok r`.
  `twin_returns_O`: at `Fmt.HO Fmt.oracle`, from the equation of the program's reader.
The two named hypotheses of `twin_returns_O`, beside the bounds:
  `place`   the twin's reading of the place in the binding tree at `Fmt.HO Fmt.oracle` gives what
            the program's gives;
  `key`     the same for the table's key.
Both say that the calls of these two steps lie in the hash's domain; the key's hang on no file.
  `twin_returns_O32`: the two paid by OnBytes/Tie/PlaceDom.lean, from 32 bytes of the
    configuration's digest and 32 bytes of the table's root.
Limits: one direction, from the program's record to the twin's equation: the one that a tie needs.
The other, from the twin's equation at h to each letter of a record, is not here. `twin_returns` can
be called only at an h that agrees with `Fmt.formatHash` on every call of this file's reading, since its
record holds these calls' outcomes at `Fmt.formatHash`. `Fmt.HO Fmt.oracle` is `Fmt.formatHash` on the hash's domain
alone (Fmt/Rules23.lean), so the bounds cannot be dropped for free. Nothing at a drawn function.
Nothing on soundness.

-/
import OnBytes.Maker.Page.CollidesOracle
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Files
import OnBytes.Tie.PlaceDom

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker
open OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open OnBytes.TwoPort

/-! ## A reading that returns -/

/-- The reading w, run from the record of vertices s, returns a and leaves s'. -/
def Ret {α : Type} (w : M.Proof.Reading Id α) (s : Session) (a : α) (s' : Session) : Prop :=
  (w s).run = (Except.ok (a, s') : Except String (α × Session))

theorem ret_pure {α : Type} (a : α) (s : Session) :
    Ret (pure a : M.Proof.Reading Id α) s a s := rfl

theorem ret_bind {α β : Type} {w : M.Proof.Reading Id α} {g : α → M.Proof.Reading Id β}
    {s s' s'' : Session} {a : α} {b : β} (hw : Ret w s a s') (hg : Ret (g a) s' b s'') :
    Ret (w >>= g) s b s'' := by
  unfold Ret at hw hg ⊢
  rw [M.Proof.Reading.run_bind, hw]
  exact hg

theorem ret_need {α : Type} (why : String) {x : Option α} {a : α} (s : Session)
    (hx : x = some a) : Ret (M.Proof.need (m := Id) why x) s a s := by
  subst hx
  rfl

theorem ret_needM {α : Type} (why : String) {x : Id (Option α)} {a : α} (s : Session)
    (hx : x = (some a : Option α)) : Ret (M.Proof.needM (m := Id) why x) s a s := by
  subst hx
  rfl

theorem ret_guard {β : Type} {c : Prop} [Decidable c] (e : String)
    {g : PUnit → M.Proof.Reading Id β} {s s'' : Session} {b : β} (hc : ¬ c)
    (hg : Ret (g PUnit.unit) s b s'') :
    Ret (if c then throw e >>= g else pure PUnit.unit >>= g) s b s'' := by
  rw [if_neg hc]
  exact ret_bind (ret_pure _ _) hg

/-- A chain: where the library's strict reader at h returns, the twin's named reading returns. -/
theorem ret_readNamed (h : HId) (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : ℕ)
    (s : Session) (cr : ChainRead)
    (e : Fmt.readChainX (m := Id) h S s.seen b i = some (cr.out, cr.next))
    (v : cr.view = OnBytes.viewOf S cr.out) :
    Ret (M.Proof.readNamed (m := Id) h front S b i) s cr ⟨cr.out.seen⟩ := by
  have hin : (M.readIn (m := Id) h S b i s).run =
      (some (cr, ⟨cr.out.seen⟩) : Option (ChainRead × Session)) := by
    unfold M.readIn
    show (match M.readChain (m := Id) h S s.seen b i with
      | none => _
      | some (o, j) => _) = _
    rw [M.EngineAtId.readChain_id, e]
    obtain ⟨o, vw, n⟩ := cr
    dsimp only at v
    subst v
    rfl
  unfold Ret M.Proof.readNamed
  show (match (M.readIn (m := Id) h S b i s).run with
    | some y => _
    | none => _) = _
  rw [hin]
  rfl

/-- The tail. -/
theorem ret_readTail (h : HId) {p : TailPublic} {dry : FirstEnd} {b : ByteArray} {r : TailRead}
    {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds}
    {S₃ : Fmt.SpecX} (e1 : r.first.seal = some seal1)
    (e2 : M.Proof.readPlace (m := Id) h p.binding p.shared.given.cfg seal1 b r.first.next =
      (some r.place : Option Place))
    (e3 : M.tableKey (m := Id) h p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index
      p.table 0 = (some r.key : Option TableKey))
    (e4 : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (R₂, dry2))
    (e5 : p.shared.describe p.lab₂ p.table r.place.root R₂ = some S₂)
    (e6 : Fmt.readChainX (m := Id) h S₂ r.first.out.seen b r.place.next =
      some (r.shared.out, r.shared.next))
    (v6 : r.shared.view = OnBytes.viewOf S₂ r.shared.out) (e7 : r.shared.seal = some seal2)
    (e8 : (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) =
      some R₃)
    (e9 : p.second.describe p.lab₃ seal1 seal2 R₃ (secondFirstTree r.first) = some S₃)
    (e10 : Fmt.readChainX (m := Id) h S₃ r.shared.out.seen b r.shared.next =
      some (r.second.out, r.second.next))
    (v10 : r.second.view = OnBytes.viewOf S₃ r.second.out) :
    Ret (M.Proof.readTail (m := Id) h p dry r.first b) ⟨r.first.out.seen⟩ r
      ⟨r.second.out.seen⟩ := by
  unfold M.Proof.readTail
  dsimp only
  refine ret_bind (ret_need _ _ e1) ?_
  refine ret_bind (ret_needM _ _ e2) ?_
  refine ret_bind (ret_needM _ _ e3) ?_
  refine ret_bind (ret_need _ _ e4) ?_
  refine ret_bind (ret_need _ _ e5) ?_
  refine ret_bind (ret_readNamed h _ _ _ _ _ r.shared e6 v6) ?_
  refine ret_bind (ret_need _ _ e7) ?_
  refine ret_bind (ret_need _ _ e8) ?_
  refine ret_bind (ret_need _ _ e9) ?_
  refine ret_bind (ret_readNamed h _ _ _ _ _ r.second e10 v10) ?_
  exact ret_pure _ _

/-! ## The proof file -/

section
variable (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ) (request words : ByteArray)
  (block : Blk FirstEnd) (file : ByteArray)

/-- **At a letter: the record, with its five hashing steps at h, gives the twin's equation at h.**
-/
theorem twin_returns (h : HId) {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX}
    {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX}
    {R₃ : Rounds} {S₃ : Fmt.SpecX}
    (hi : readProofHead c.first.given.plan.field file = .ok (copy, i))
    (hpar : (c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32) = false)
    (hS : c.first.describe table copy request words R₁ = some S₁)
    (T : ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2
      R₂ dry2 S₂ R₃ S₃)
    (A : ReadAt h S₁ S₂ S₃ file i r)
    (place : M.Proof.readPlace (m := Id) h (tailPublic c table).binding
      (tailPublic c table).shared.given.cfg seal1 file r.first.next =
        (some r.place : Option Place))
    (key : M.tableKey (m := Id) h (tailPublic c table).shared.given.plan.field
      (tailPublic c table).shared.given.cfg (tailPublic c table).lin.fold.index
      (tailPublic c table).table 0 = (some r.key : Option TableKey)) :
    M.Proof.Reading.fromStart (M.Proof.readProof (m := Id) h c table copy request words block file)
        =
      (Except.ok r : Except String TailRead) := by
  have R : Ret (M.Proof.readProof (m := Id) h c table copy request words block file) Session.start r
      ⟨r.second.out.seen⟩ := by
    unfold M.Proof.readProof
    dsimp only
    rw [hi]
    dsimp only
    refine ret_bind (ret_pure _ _) ?_
    dsimp only
    refine ret_guard _ (by simp) ?_
    refine ret_guard _ (by rw [hpar]; exact Bool.false_ne_true) ?_
    refine ret_bind (ret_need _ _ T.first_dry) ?_
    refine ret_bind (ret_need _ _ hS) ?_
    refine ret_bind (ret_readNamed h _ _ _ _ _ r.first A.first T.first_view) ?_
    refine ret_bind (ret_readTail h T.first_seal place key T.shared_dry T.shared_spec A.shared
      T.shared_view T.shared_seal T.second_rounds T.second_spec A.second T.second_view) ?_
    refine ret_guard _ (by
      have hw : r.next = file.size := T.whole
      simp [hw]) ?_
    exact ret_pure _ _
  unfold M.Proof.Reading.fromStart
  show Except.map _ (M.Proof.readProof (m := Id) h c table copy request words block file
    Session.start).run = _
  rw [R]
  rfl

/-- **At the hash over the realised oracle, at a file that the program's reader has read.** small:
the bounds at whatever three descriptions the record of this reading holds. -/
theorem twin_returns_O (r : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r)
    (small : ∀ i, readProofHead c.first.given.plan.field file = .ok (copy, i) →
      SmallAt (tailPublic c table) block (firstStart c.first) c.first.given Params.labelFirst
        (Params.First.statement table copy request words) file i r)
    (place : ∀ seal1, r.first.seal = some seal1 →
      M.Proof.readPlace (m := Id) (Fmt.HO Fmt.oracle) (tailPublic c table).binding
          (tailPublic c table).shared.given.cfg seal1 file r.first.next =
        readPlace (tailPublic c table).binding (tailPublic c table).shared.given.cfg seal1 file
          r.first.next)
    (key : M.tableKey (m := Id) (Fmt.HO Fmt.oracle) (tailPublic c table).shared.given.plan.field
        (tailPublic c table).shared.given.cfg (tailPublic c table).lin.fold.index
        (tailPublic c table).table 0 =
      tableKey (tailPublic c table).shared.given.plan.field (tailPublic c table).shared.given.cfg
        (tailPublic c table).lin.fold.index (tailPublic c table).table 0) :
    M.Proof.Reading.fromStart
        (M.Proof.readProof (m := Id) (Fmt.HO Fmt.oracle) c table copy request words block file) =
      (Except.ok r : Except String TailRead) := by
  obtain ⟨s', hs'⟩ := fromStart_returns h₀
  obtain ⟨i₀, _, _, _, _, f⟩ := readProof_open _ _ _ _ _ _ _ _ _ _ hs'
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃, S₃, hi, hS, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h₀
  exact twin_returns c table copy request words block file (Fmt.HO Fmt.oracle) hi f.params_ok hS T
    (readAt_O T (small i hi _ _ _ _ _ _ _ _ _ _ hS T))
    ((place seal1 T.first_seal).trans T.place_read) (key.trans T.key_made)

/-- **The same, with the place and the key paid** (OnBytes/Tie/PlaceDom.lean): what is left is the
bounds, 32 bytes of the configuration's digest and 32 bytes of the table's root. -/
theorem twin_returns_O32 (r : TailRead)
    (h₀ : (readProof c table copy request words block file).fromStart = .ok r)
    (small : ∀ i, readProofHead c.first.given.plan.field file = .ok (copy, i) →
      SmallAt (tailPublic c table) block (firstStart c.first) c.first.given Params.labelFirst
        (Params.First.statement table copy request words) file i r)
    (hc : c.shared.given.cfg.size = 32) (hr : table.root.size = 32) :
    M.Proof.Reading.fromStart
        (M.Proof.readProof (m := Id) (Fmt.HO Fmt.oracle) c table copy request words block file) =
      (Except.ok r : Except String TailRead) :=
  twin_returns_O c table copy request words block file r h₀ small
    (fun _ _ => Tie.readPlaceM_O _ _ _ _ _ hc) (Tie.tableKeyM_O _ _ _ _ _ hr hc)

end

end OnBytes.Maker.Page
