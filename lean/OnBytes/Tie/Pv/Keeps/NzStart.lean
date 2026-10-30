-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/NzStart.lean: the property `NzCtx` (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean), at the
reading in the library's field, of the context from which the first chain's block is run on the view
that the strict reader has made of a proof file.

Statements and proofs. The reader tests that the description's rounds have the plan's entries, one
by one, and each round that it reads has drawn what the format's rule gives at that entry
(OnBytes/Tie/Pv/Keeps/NzRead.lean). The block starts from the same entries.
Main names:
  `rbind_ok`, `need_ok`: what it says of a reading within a session that it has returned.
  `readIn_nz`: a chain that was read under a description of the second field: the k-th round of its
    view against the k-th entry of the description's plan.
  `readProof_first`: a proof file that was read: its first chain was read under a description made
    of the first chain's parameter bytes, in the second field.
  `nzCtx_start`: `NzCtx Reading.gl` at the start.
Limits: the reading in the library's field alone. Nothing on the two later chains.
-/
import OnBytes.Chain.ReaderLaws
import OnBytes.Proof.File
import OnBytes.Tie.Pv.Keeps.KeepsChain
import OnBytes.Tie.Pv.Keeps.NzRead
import OnBytes.Tie.Pv.Psc.Run.NzCtx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Nz

open OnBytes OnBytes.Model OnBytes.L5

theorem forall2_get {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (k : Nat) (y : β), l₂[k]? = some y → ∃ x, l₁[k]? = some x ∧ R x y
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons (a := a) h1 _, 0, y, h => by
    obtain rfl : _ = y := Option.some.inj h
    exact ⟨a, rfl, h1⟩
  | _, _, .cons _ h2, k + 1, y, h => forall2_get h2 k y h

/-- A chain that was read: the k-th round of its view against the k-th entry of the plan. -/
theorem readIn_nz (S : Fmt.SpecX) (hf : S.base.plan.field = .two) (b : ByteArray) (i : Nat)
    (s s' : Session) (cr : ChainRead) (h : readIn S b i s = some (cr, s')) (k : Nat)
    (e : Fmt.Entry) (r : Fmt.RoundView) (he : S.base.plan.rounds[k]? = some e)
    (hr : cr.view.rounds[k]? = some r) : Road.NzAt Reading.gl e r.drawn := by
  unfold readIn at h
  split at h
  · cases h
  · rename_i o j hq
    cases h
    rw [readChain_eq] at hq
    obtain ⟨hok, hall⟩ := readChainX_out Fmt.formatHash S s.seen b i o j hq
    have hent : S.base.rounds.map (·.entry) = S.base.plan.rounds := by
      have h1 := hok
      simp only [Fmt.SpecX.ok, Fmt.Spec.ok, Bool.and_eq_true, beq_iff_eq] at h1
      tauto
    have hr' : (Fmt.viewX S o).rounds[k]? = some r := by
      rw [← viewOf_eq]
      exact hr
    have hr2 : (o.rounds.toList.map fun x : Fmt.RoundOut =>
        (⟨Fmt.noRoots x.vals, x.drawn⟩ : Fmt.RoundView))[k]? = some r := hr'
    rw [List.getElem?_map] at hr2
    obtain ⟨ro, hro, rfl⟩ := Option.map_eq_some_iff.1 hr2
    obtain ⟨x, hx, row, hd⟩ := forall2_get hall k ro hro
    have hx1 : S.base.rounds[k]? = some x.1 := (List.getElem?_zip_eq_some.1 hx).1
    have he' : x.1.entry = e := by
      rw [← hent, List.getElem?_map, hx1] at he
      exact Option.some.inj he
    refine Road.nzAt_gl e _ fun hz y hy => ?_
    have hy' : y ∈ (Fmt.drawRound .two e x.1.kind row).elems := by
      rw [← he', ← hf, ← hd]
      exact hy
    exact drawRound_good e x.1.kind hz row y hy'

/-! ## Readings within a session -/

theorem rbind_ok {α β : Type} (x : Proof.Reading α) (f : α → Proof.Reading β) (s : Session)
    (y : β × Session) :
    (x >>= f) s = .ok y ↔ ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok y := by
  show (StateT.bind x f) s = .ok y ↔ _
  simp only [StateT.bind]
  show Except.bind (x s) _ = .ok y ↔ _
  cases x s with
  | error e => simp [Except.bind]
  | ok v =>
    obtain ⟨a, s1⟩ := v
    simp [Except.bind]

theorem need_ok {α : Type} (why : String) (x : Option α) (s s' : Session) (a : α) :
    Proof.need why x s = .ok (a, s') ↔ x = some a ∧ s' = s := by
  unfold Proof.need
  cases x with
  | none => simp
  | some b => simp [eq_comm]

theorem rpure_ok {α : Type} (a b : α) (s s' : Session) :
    (pure a : Proof.Reading α) s = .ok (b, s') ↔ b = a ∧ s' = s := by
  show (Except.ok (a, s) : Except String (α × Session)) = .ok (b, s') ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem rthrow_ne {α : Type} (e : String) (s : Session) (y : α × Session) :
    (throw e : Proof.Reading α) s ≠ .ok y := by
  intro h
  cases h

theorem rthrow_bind_ne {α β : Type} (e : String) (f : α → Proof.Reading β) (s : Session)
    (y : β × Session) : ((throw e : Proof.Reading α) >>= f) s ≠ .ok y := by
  intro h
  obtain ⟨_, _, h0, _⟩ := (rbind_ok _ _ _ _).1 h
  exact rthrow_ne _ _ _ h0

/-- The tail's reading hands the first chain on as it got it. -/
theorem readTail_first (p : Proof.TailPublic) (dry : Proof.FirstEnd) (first : ChainRead)
    (b : ByteArray) (s s' : Session) (r : Proof.TailRead)
    (h : Proof.readTail p dry first b s = .ok (r, s')) : r.first = first := by
  unfold Proof.readTail at h
  simp only [rbind_ok, rpure_ok] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    rfl, _⟩ := h
  rfl

/-- A description of a first chain has the plan of the chain's parameter bytes. -/
theorem describe_plan (p : Params.First) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (rs : Params.Rounds) (S : Fmt.SpecX)
    (h : p.describe table copy request words rs = some S) : S.base.plan = p.given.plan := by
  unfold Params.First.describe Params.describeWith Params.Given.describe at h
  dsimp only at h
  split at h
  · cases h
    rfl
  · cases h

/-- A proof file that was read: its first chain was read under a description made of the first
chain's parameter bytes, in the second field. -/
theorem readProof_first (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk Proof.FirstEnd) (file : ByteArray)
    (r : Proof.ProofRead)
    (h : (Proof.readProof c table copy request words block file).fromStart = .ok r) :
    c.first.given.plan.field = .two ∧ ∃ rs S i s s',
      c.first.describe table copy request words rs = some S ∧
        readIn S file i s = some (r.first, s') := by
  unfold Proof.Reading.fromStart at h
  cases hw : Proof.readProof c table copy request words block file Session.start with
  | error e => rw [hw] at h; cases h
  | ok y =>
    obtain ⟨r', sE⟩ := y
    rw [hw] at h
    obtain rfl : r' = r := Except.ok.inj h
    unfold Proof.readProof at hw
    cases hh : Proof.readProofHead c.first.given.plan.field file with
    | error e =>
      simp only [hh] at hw
      exact absurd hw (rthrow_bind_ne _ _ _ _)
    | ok x0 =>
      simp only [hh] at hw
      obtain ⟨x, s1, h1, hw⟩ := (rbind_ok _ _ _ _).1 hw
      obtain ⟨madeOn, i⟩ := x
      dsimp only at hw
      split at hw
      · exact absurd hw (rthrow_bind_ne _ _ _ _)
      · obtain ⟨_, s2, _, hw⟩ := (rbind_ok _ _ _ _).1 hw
        split at hw
        · exact absurd hw (rthrow_bind_ne _ _ _ _)
        · rename_i hn
          obtain ⟨_, s3, _, hw⟩ := (rbind_ok _ _ _ _).1 hw
          obtain ⟨⟨rs, dry⟩, s4, _, hw⟩ := (rbind_ok _ _ _ _).1 hw
          dsimp only at hw
          obtain ⟨S, s5, h5, hw⟩ := (rbind_ok _ _ _ _).1 hw
          obtain ⟨first, s6, h6, hw⟩ := (rbind_ok _ _ _ _).1 hw
          obtain ⟨r1, s7, h7, hw⟩ := (rbind_ok _ _ _ _).1 hw
          split at hw
          · exact absurd hw (rthrow_bind_ne _ _ _ _)
          · obtain ⟨_, s8, _, hw⟩ := (rbind_ok _ _ _ _).1 hw
            obtain ⟨rfl, _⟩ := (rpure_ok _ _ _ _).1 hw
            have hf : c.first.given.plan.field = .two := by
              simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hn
              exact hn.1
            refine ⟨hf, rs, S, i, s5, s6, ((need_ok _ _ _ _ _).1 h5).1, ?_⟩
            rw [readTail_first _ _ _ _ _ _ _ h7]
            unfold Proof.readNamed at h6
            split at h6
            · rename_i y hy
              cases h6
              exact hy
            · cases h6

/-- `NzCtx`, at the reading in the library's field, of the context from which the first chain's
block is run on the view of a proof file that was read. -/
theorem nzCtx_start (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk Proof.FirstEnd) (file : ByteArray)
    (r : Proof.ProofRead)
    (h : (Proof.readProof c table copy request words block file).fromStart = .ok r) :
    Road.NzCtx Reading.gl (startOf (Proof.firstStart c.first) r.first.view) := by
  obtain ⟨hf, rs, S, i, s, s', hS, hr⟩ := readProof_first c table copy request words block file r h
  have hp := describe_plan c.first table copy request words rs S hS
  refine ⟨rfl, fun k e rv he hv => ?_⟩
  exact readIn_nz S (by rw [hp]; exact hf) file i s s' r.first hr k e rv (by rw [hp]; exact he) hv

end OnBytes.Tie.Pv.Keeps.Nz

#print axioms OnBytes.Tie.Pv.Keeps.Nz.readIn_nz
#print axioms OnBytes.Tie.Pv.Keeps.Nz.readProof_first
#print axioms OnBytes.Tie.Pv.Keeps.Nz.nzCtx_start
