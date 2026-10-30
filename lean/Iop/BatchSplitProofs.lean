-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchSplitProofs.lean: the proofs of the statements of Iop/BatchSplit.lean (prover messages sent
in parts, each in a separate round).
  `splitPropsB`: `BatchProtocol.Props` after a split of rounds (statement and hypotheses:
    Iop/BatchSplit.lean).
  `splitFmtB`: `RoundSplits.Fmt` and `ExtShared` after a split (statement and hypotheses:
    Iop/BatchSplit.lean).
As Iop/SplitProofs.lean, whose lemmas for one slot's transcript are used, and after
Iop/BatchPullProofs.lean. Helpers: namespace `Iop.BatchSplit`. (Words of this library:
lean/GLOSSARY.md.)

The one new idea is the state function of the soundness property `SndB` (Snd-B) on the prefixes of
the new transcripts (`BatchSplit.merge`). A prefix that ends inside a prover message of the old
protocol is given the state of the old prefix before that message.
Then a part that does not complete the message, and the empty challenge after it, do not change the
state, so the new rounds have the error 0, for one slot and jointly; the part that completes the
message changes the state as the whole message did in the old protocol, so it never changes 0 to 1.

Notation: `SndBL` (Iop/Batch.lean): (Snd-B), late form: see its docstring; `early : X → X` (a field
of `BatchProtocol`, Iop/Batch.lean): what of an instance layer 1 (the compiler) writes into the first query of
the chain of a slot of Batch; `late : Option ℕ` (there): the round of Batch (counted from 0) into
whose query layer 1 writes the whole instance; none: there is no such round;
`APlan.LoTo P A Z n : Prop` (Iop/BatchSplit.lean): every first part that is split off one of the
rounds 0, .., n is a local round; `SwitchLaw n s S0 S1 : Prop` (this file): if the state S0 is 0
before the prover message of round n, so is the state S1; `DView Q : Type` (Iop/InteractiveOracleProof.lean): the
disclosed view; `BatchPull.slotOut` (Iop/BatchPullProofs.lean): see its docstring;
`RAnn.Coherent a : Prop` (Iop/Batch.lean): the data of an annotation fit together.
-/
import Iop.BatchSplit
import Iop.SplitProofs
import Iop.BatchSound
import Iop.BatchPullProofs

namespace Iop
open Prob
open scoped ENNReal

namespace BatchSplit

/-! ## 1. One annotated split -/

section OneCut
variable {r : Round} {c : RCut r} {a : RAnn r} (b : ACut c a)

theorem rd_join_inl (hc : c.OK) (x : c.fst.Msg) (y : c.snd.Msg) (p : c.PosA) :
    r.rd (c.join x y).1 (c.pos (.inl p)) = c.rdA x.1 p := by
  show r.rd (c.orc.symm (x.1, y.1)) (c.pos (.inl p)) = c.rdA x.1 p
  rw [hc.rdA, Equiv.apply_symm_apply]

theorem rd_join_inr (hc : c.OK) (x : c.fst.Msg) (y : c.snd.Msg) (p : c.PosB) :
    r.rd (c.join x y).1 (c.pos (.inr p)) = c.rdB y.1 p := by
  show r.rd (c.orc.symm (x.1, y.1)) (c.pos (.inr p)) = c.rdB y.1 p
  rw [hc.rdB, Equiv.apply_symm_apply]

variable {b}

theorem join_symm (hb : b.OK) (x0 : b.A.M0) (y0 : b.B.M0) (xj : b.A.Mj) (yj : b.B.Mj) :
    a.join (b.m0.symm (x0, y0)) (b.mj.symm (xj, yj)) =
      c.join (b.ann1.join x0 xj) (b.ann2.join y0 yj) := by
  rw [hb.join, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable (b)

/-- The four components of the two parts are non-empty types. -/
theorem nonempty_parts : Nonempty b.A.M0 ∧ Nonempty b.B.M0 ∧ Nonempty b.A.Mj ∧ Nonempty b.B.Mj :=
  ⟨⟨(b.m0 (a.split (r.dOrc, r.dPlain)).1).1⟩, ⟨(b.m0 (a.split (r.dOrc, r.dPlain)).1).2⟩,
   ⟨(b.mj (a.split (r.dOrc, r.dPlain)).2).1⟩, ⟨(b.mj (a.split (r.dOrc, r.dPlain)).2).2⟩⟩

variable {b}

/-- Under `c.OK`, `b.OK`, `a.Coherent`: the annotations of the two parts are coherent. -/
theorem coherent_cut (hc : c.OK) (hb : b.OK) (ha : a.Coherent) :
    b.ann1.Coherent ∧ b.ann2.Coherent := by
  obtain ⟨⟨x0⟩, ⟨y0⟩, ⟨xj⟩, ⟨yj⟩⟩ := nonempty_parts b
  refine ⟨⟨hb.plainA, fun m0 mj mj' p hp => ?_, fun m0 m0' mj p hp => ?_⟩,
    ⟨hb.plainB, fun m0 mj mj' p hp => ?_, fun m0 m0' mj p hp => ?_⟩⟩
  · have h := ha.rd_shared (b.m0.symm (m0, y0)) (b.mj.symm (mj, yj)) (b.mj.symm (mj', yj))
      (c.pos (.inl p)) ((hb.ownA p).symm.trans hp)
    rw [join_symm hb, join_symm hb, rd_join_inl hc, rd_join_inl hc] at h
    exact h
  · have h := ha.rd_own (b.m0.symm (m0, y0)) (b.m0.symm (m0', y0)) (b.mj.symm (mj, yj))
      (c.pos (.inl p)) ((hb.ownA p).symm.trans hp)
    rw [join_symm hb, join_symm hb, rd_join_inl hc, rd_join_inl hc] at h
    exact h
  · have h := ha.rd_shared (b.m0.symm (x0, m0)) (b.mj.symm (xj, mj)) (b.mj.symm (xj, mj'))
      (c.pos (.inr p)) ((hb.ownB p).symm.trans hp)
    rw [join_symm hb, join_symm hb, rd_join_inr hc, rd_join_inr hc] at h
    exact h
  · have h := ha.rd_own (b.m0.symm (x0, m0)) (b.m0.symm (x0, m0')) (b.mj.symm (xj, mj))
      (c.pos (.inr p)) ((hb.ownB p).symm.trans hp)
    rw [join_symm hb, join_symm hb, rd_join_inr hc, rd_join_inr hc] at h
    exact h

theorem subsingleton_parts {α β γ : Type} (e : α ≃ β × γ) [Subsingleton α]
    [Nonempty β] [Nonempty γ] :
    Subsingleton β ∧ Subsingleton γ := by
  haveI : Subsingleton (β × γ) := e.symm.subsingleton
  obtain ⟨y⟩ := ‹Nonempty β›
  obtain ⟨z⟩ := ‹Nonempty γ›
  exact ⟨⟨fun u v => congrArg Prod.fst (Subsingleton.elim (u, z) (v, z))⟩,
    ⟨fun u v => congrArg Prod.snd (Subsingleton.elim (y, u) (y, v))⟩⟩

/-- Under `b.OK`: if the old round has no shared component, neither part has one. -/
theorem noShared_cut (hb : b.OK) (h : a.NoShared) : b.ann1.NoShared ∧ b.ann2.NoShared := by
  obtain ⟨h1, h2, -, -⟩ := nonempty_parts b
  haveI := h.2
  obtain ⟨s1, s2⟩ := subsingleton_parts b.m0
  exact ⟨⟨fun p => (hb.ownA p).trans (h.1 _), s1⟩, ⟨fun p => (hb.ownB p).trans (h.1 _), s2⟩⟩

/-- Under `b.OK`: if the old round has no slot's component, neither part has one. -/
theorem noSlot_cut (hb : b.OK) (h : a.NoSlot) : b.ann1.NoSlot ∧ b.ann2.NoSlot := by
  obtain ⟨-, -, h1, h2⟩ := nonempty_parts b
  haveI := h.2
  obtain ⟨s1, s2⟩ := subsingleton_parts b.mj
  exact ⟨⟨fun p => (hb.ownA p).trans (h.1 _), s1⟩, ⟨fun p => (hb.ownB p).trans (h.1 _), s2⟩⟩

variable (b) {s : Shape} (A : RoundSplits s)

/-! The remainder of a split round has the challenges and the kind of the old round. So what is
defined on the challenges of a list of rounds that begins with the old round and what is defined on
those of a list that begins with the remainder agree; for a variable this is seen after it is
destructured. -/

theorem slot_snd {N : ℕ} (j : Fin N) :
    ∀ x : BRho N (c.snd :: s) (b.ann2, A), BRho.slot j (s := r :: s) (A := (a, A)) x =
      BRho.slot j (s := c.snd :: s) (A := (b.ann2, A)) x := by
  rintro ⟨_, _⟩
  rfl

theorem lo_snd :
    ∀ x : Rho (c.snd :: s),
      Rho.lo (s := r :: s) (a, A) x = Rho.lo (s := c.snd :: s) (b.ann2, A) x := by
  rintro ⟨_, _⟩
  rfl

theorem sh_snd :
    ∀ x : Rho (c.snd :: s),
      Rho.sh (s := r :: s) (a, A) x = Rho.sh (s := c.snd :: s) (b.ann2, A) x := by
  rintro ⟨_, _⟩
  rfl

end OneCut

/-! ## 2. Challenges -/

theorem slot_merge {N : ℕ} (j : Fin N) {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A) (ρ : BRho N P.shape (A.split P Z)),
      (BRho.merge P A Z ρ).slot j = Rho.merge P (ρ.slot j) := by
  induction P with
  | nil => intro _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ⟨v, ρ⟩
      exact (slot_snd b A j _).trans (ih (b.ann2, A) Z ρ)

theorem lo_merge {s : Shape} (P : SPlan s) : ∀ (A : RoundSplits s) (Z : APlan P A) (ρ : Rho P.shape),
    RhoLo.merge P A Z (Rho.lo (A.split P Z) ρ) = Rho.lo A (Rho.merge P ρ) := by
  induction P with
  | nil => intro _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ⟨v, ρ⟩
      exact (ih (b.ann2, A) Z ρ).trans (lo_snd b A _).symm

theorem sh_merge {s : Shape} (P : SPlan s) : ∀ (A : RoundSplits s) (Z : APlan P A) (ρ : Rho P.shape),
    RhoSh.merge P A Z (Rho.sh (A.split P Z) ρ) = Rho.sh A (Rho.merge P ρ) := by
  induction P with
  | nil => intro _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ⟨v, ρ⟩
      exact (ih (b.ann2, A) Z ρ).trans (sh_snd b A _).symm

/-! ## 3. Annotations -/

theorem coherent_split {s : Shape} (P : SPlan s) (hP : P.OK) :
    ∀ (A : RoundSplits s) (Z : APlan P A), APlan.OK P A Z → A.Coherent → (A.split P Z).Coherent := by
  induction P with
  | nil => intro _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨a, A⟩ Z hZ h
      exact ⟨h.1, ih hP A Z hZ h.2⟩
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ h
      obtain ⟨h1, h2⟩ := coherent_cut hP.1 hZ.1 h.1
      exact ⟨h1, ih hP.2 (b.ann2, A) Z hZ.2 ⟨h2, h.2⟩⟩

/-! ## 4. Prefixes -/

/-- A prefix of a transcript whose rounds begin with the remainder of a split round, with the first
part put back. -/
def glueP {r : Round} (c : RCut r) {s : Shape} (x : c.fst.Msg) : PTr (c.snd :: s) → PTr (r :: s)
  | .atP (.inl _) => .atP (.inl ())
  | .atP (.inr z) => .atP (.inr (c.join x z.1, z.2.1, z.2.2))
  | .atV (.inl y) => .atV (.inl (c.join x y))
  | .atV (.inr z) => .atV (.inr (c.join x z.1, z.2.1, z.2.2))
  | .full z => .full (c.glue x z)

/-- The old prefix that belongs to a new one. The parts of complete prover messages are put
together. If the prefix ends inside a prover message of the old protocol, the parts of that message
are dropped: the result is the old prefix before the message. -/
def merge : {s : Shape} → (P : SPlan s) → PTr P.shape → PTr s
  | _, .nil => fun t => t
  | _, .keep r P => fun (t : PTr (r :: P.shape)) => match t with
      | .atP (.inl _) => .atP (.inl ())
      | .atP (.inr z) => PTr.cons z.1 z.2.1 (merge P (.atP z.2.2))
      | .atV (.inl m) => .atV (.inl m)
      | .atV (.inr z) => PTr.cons z.1 z.2.1 (merge P (.atV z.2.2))
      | .full z => PTr.cons z.1 z.2.1 (merge P (.full z.2.2))
  | _, .cut c P => fun (t : PTr (c.fst :: P.shape)) => match t with
      | .atP (.inl _) => .atP (.inl ())
      | .atP (.inr z) => glueP c z.1 (merge P (.atP z.2.2))
      | .atV (.inl _) => .atP (.inl ())
      | .atV (.inr z) => glueP c z.1 (merge P (.atV z.2.2))
      | .full z => glueP c z.1 (merge P (.full z.2.2))

theorem glueP_cons {r : Round} (c : RCut r) {s : Shape} (x : c.fst.Msg)
    (y : c.snd.Msg) (ch : r.Chal) :
    ∀ t : PTr s, glueP c x (PTr.cons (r := c.snd) y ch t) = PTr.cons (c.join x y) ch t
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem merge_cons_keep (r : Round) {s : Shape} (P : SPlan s) (m : r.Msg) (ch : r.Chal) :
    ∀ t : PTr P.shape, merge (.keep r P) (PTr.cons m ch t) = PTr.cons m ch (merge P t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem merge_cons_cut {r : Round} {s : Shape} (c : RCut r) (P : SPlan (c.snd :: s))
    (x : c.fst.Msg) (u : Unit) :
    ∀ t : PTr P.shape, merge (.cut c P) (PTr.cons (r := c.fst) x u t) = glueP c x (merge P t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem merge_empty : ∀ {s : Shape} (P : SPlan s), merge P (PTr.empty P.shape) = PTr.empty s
  | _, .nil => rfl
  | _, .keep _ _ => rfl
  | _, .cut _ _ => rfl

theorem merge_full {s : Shape} (P : SPlan s) :
    ∀ τ : Tr P.shape, merge P (.full τ) = .full (Tr.merge P τ) := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, ch, τ⟩
      show PTr.cons m ch (merge P (.full τ)) = _
      rw [ih]
      rfl
  | cut c P ih =>
      rintro ⟨x, u, τ⟩
      show glueP c x (merge P (.full τ)) = _
      rw [ih]
      rfl

open BatchH4 in
theorem proverLaw_glue {r : Round} (c : RCut r) {s : Shape} (x : c.fst.Msg)
    (S : PTr (r :: s) → Bool) (h : ProverLaw (r :: s) S) :
    ProverLaw (c.snd :: s) (fun t => S (glueP c x t))
  | .inl _, m, h0 => h (.inl ()) (c.join x m) h0
  | .inr (y, ch, τ), m, h0 => h (.inr (c.join x y, ch, τ)) m h0

open BatchH4 in
theorem proverLaw_split {s : Shape} (P : SPlan s) :
    ∀ S : PTr s → Bool, ProverLaw s S → ProverLaw P.shape (fun t => S (merge P t)) := by
  induction P with
  | nil => intro _ _ τ; exact Empty.elim τ
  | keep r P ih =>
      rintro S h (_ | ⟨m', c', τ⟩) m h0
      · exact h (.inl ()) m h0
      · exact ih (fun t => S (PTr.cons m' c' t)) (h.tail m' c') τ m h0
  | cut c P ih =>
      rintro S h (_ | ⟨x, u, τ⟩) m h0
      · exact h0
      · exact ih (fun t => S (glueP c x t)) (proverLaw_glue c x S h) τ m h0

/-! ## 5. The soundness property `SndB` (Snd-B) -/

/-- The condition of one round in `JointLaw` (Iop/Batch.lean), for state functions on any type T:
`x0 j` is the prefix of slot j before the challenge, `x1 j c` the one after the challenge c. -/
def RoundLaw {N : ℕ} {T C : Type} [Finite C] (k : Kind) (e : ℕ) (St : Fin N → Option (T → Bool))
    (x0 : Fin N → T) (x1 : Fin N → C → T) : Prop :=
  match k with
  | .lo => ∀ j S, St j = some S → S (x0 j) = false → cnt (fun c : C => S (x1 j c) = true) ≤ e
  | .sh => cnt (fun c : C => ∃ j S, St j = some S ∧ S (x0 j) = false ∧ S (x1 j c) = true) ≤ e

theorem RoundLaw.comap {N : ℕ} {T T' C : Type} [Finite C] (f : Fin N → T' → T) (k : Kind)
    (e : ℕ) (St : Fin N → Option (T → Bool)) (x0 : Fin N → T) (x1 : Fin N → C → T)
    (x0' : Fin N → T') (x1' : Fin N → C → T') (h0 : ∀ j, f j (x0' j) = x0 j)
    (h1 : ∀ j c, f j (x1' j c) = x1 j c) (h : RoundLaw k e St x0 x1) :
    RoundLaw k e (fun j => (St j).map fun S t => S (f j t)) x0' x1' := by
  cases k with
  | lo =>
      intro j S' hS' h0'
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      refine le_trans (le_of_eq (cnt_congr fun c => ?_)) (h j S hS (by rw [← h0 j]; exact h0'))
      show S (f j (x1' j c)) = true ↔ _
      rw [h1]
  | sh =>
      refine le_trans (cnt_mono ?_) h
      rintro c ⟨j, S', hS', h0', h1'⟩
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      exact ⟨j, S, hS, by rw [← h0 j]; exact h0', by rw [← h1 j c]; exact h1'⟩

/-- A challenge that does not change the old prefix has the error 0. -/
theorem RoundLaw.zero {N : ℕ} {T T' C : Type} [Finite C] (f : Fin N → T' → T) (k : Kind)
    (St : Fin N → Option (T → Bool)) (x0' : Fin N → T') (x1' : Fin N → C → T')
    (h : ∀ j c, f j (x1' j c) = f j (x0' j)) :
    RoundLaw k 0 (fun j => (St j).map fun S t => S (f j t)) x0' x1' := by
  cases k with
  | lo =>
      intro j S' hS' h0'
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      refine le_of_eq (cnt_false fun c hc => ?_)
      have hc' : S (f j (x1' j c)) = true := hc
      have h0'' : S (f j (x0' j)) = false := h0'
      rw [h, h0''] at hc'
      cases hc'
  | sh =>
      refine le_of_eq (cnt_false ?_)
      rintro c ⟨j, S', hS', h0', h1'⟩
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      have hc' : S (f j (x1' j c)) = true := h1'
      have h0'' : S (f j (x0' j)) = false := h0'
      rw [h, h0''] at hc'
      cases hc'

theorem jointLaw_split {N : ℕ} {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A), APlan.OK P A Z →
      ∀ (ε : Err s) (St : Fin N → Option (PTr s → Bool)), JointLaw N s A ε St →
        JointLaw N P.shape (A.split P Z) (Err.split P ε)
          (fun j => (St j).map fun S t => S (merge P t)) := by
  induction P with
  | nil => intro _ _ _ _ _ _; trivial
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hZ ⟨e, ε⟩ St h
      intro (m0 : a.M0) (m : Fin N → a.Mj)
      obtain ⟨hround, hrest⟩ := h m0 m
      refine ⟨?_, fun v => ?_⟩
      · exact RoundLaw.comap (fun _ => merge (.keep r P)) a.kind e St
          (fun j => .atV (Sum.inl (a.join m0 (m j))))
          (fun j ch => PTr.cons (a.join m0 (m j)) ch (PTr.empty s))
          (fun j => .atV (Sum.inl (a.join m0 (m j))))
          (fun j ch => PTr.cons (a.join m0 (m j)) ch (PTr.empty P.shape)) (fun _ => rfl)
          (fun j ch => by beta_reduce; rw [merge_cons_keep, merge_empty]) hround
      · refine cast (congrArg (JointLaw N P.shape (A.split P Z) (Err.split P ε)) ?_)
          (ih A Z hZ ε _ (hrest v))
        funext j
        beta_reduce
        refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
        congr 1
        funext S t
        show S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) (merge P t)) =
          S (merge (.keep r P) (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) t))
        rw [merge_cons_keep]
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ ε St h
      intro (x0 : b.A.M0) (x : Fin N → b.A.Mj)
      refine ⟨?_, fun v => ?_⟩
      · exact RoundLaw.zero (fun _ => merge (.cut c P)) b.kind St
          (fun j => .atV (Sum.inl (b.ann1.join x0 (x j))))
          (fun j u => PTr.cons (r := c.fst) (b.ann1.join x0 (x j)) u (PTr.empty P.shape))
          (fun j u => by beta_reduce; rw [merge_cons_cut, merge_empty]; rfl)
      · have h2 : JointLaw N (c.snd :: s) (b.ann2, A) ε
            (fun j => (St j).map fun S t => S (glueP c (b.ann1.join x0 (x j)) t)) := by
          obtain ⟨e, ε⟩ := ε
          intro (y0 : b.B.M0) (y : Fin N → b.B.Mj)
          obtain ⟨hround, hrest⟩ := h (b.m0.symm (x0, y0)) (fun j => b.mj.symm (x j, y j))
          have hj : ∀ j, a.join (b.m0.symm (x0, y0)) (b.mj.symm (x j, y j)) =
              c.join (b.ann1.join x0 (x j)) (b.ann2.join y0 (y j)) :=
            fun j => join_symm hZ.1 x0 y0 (x j) (y j)
          refine ⟨?_, fun w => ?_⟩
          · exact RoundLaw.comap (fun j => glueP c (b.ann1.join x0 (x j))) a.kind e St
              (fun j => .atV (Sum.inl (a.join (b.m0.symm (x0, y0)) (b.mj.symm (x j, y j)))))
              (fun j ch =>
                PTr.cons (a.join (b.m0.symm (x0, y0)) (b.mj.symm (x j, y j))) ch (PTr.empty s))
              (fun j => .atV (Sum.inl (b.ann2.join y0 (y j))))
              (fun j ch => PTr.cons (r := c.snd) (b.ann2.join y0 (y j)) ch (PTr.empty s))
              (fun j => by beta_reduce; rw [hj]; rfl)
              (fun j ch => by beta_reduce; rw [glueP_cons, hj]) hround
          · refine cast (congrArg (JointLaw N s A ε) ?_) (hrest w)
            funext j
            beta_reduce
            refine Eq.trans ?_ (Option.map_map _ _ _).symm
            congr 1
            funext S t
            show S (PTr.cons (a.join (b.m0.symm (x0, y0)) (b.mj.symm (x j, y j))) (a.kind.slot w j)
                  t) =
              S (glueP c (b.ann1.join x0 (x j))
                  (PTr.cons (r := c.snd) (b.ann2.join y0 (y j)) (a.kind.slot w j) t))
            rw [glueP_cons, hj]
        refine cast (congrArg (JointLaw N P.shape (RoundSplits.split P (b.ann2, A) Z) (Err.split P ε)) ?_)
          (ih (b.ann2, A) Z hZ.2 ε _ h2)
        funext j
        beta_reduce
        refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
        congr 1
        funext S t
        show S (glueP c (b.ann1.join x0 (x j)) (merge P t)) =
          S (merge (.cut c P) (PTr.cons (r := c.fst) (b.ann1.join x0 (x j)) (b.kind.slot v j) t))
        rw [merge_cons_cut]

variable {X : Type} {E : ExtSpec}

theorem sndB_split {Q : BatchInteractiveOracleProof X E} {P : SPlan Q.loc.shape}
    {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) {N : ℕ} {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (h : Q.SndB N L ε) :
    (Q.split P Z).SndB N L (Err.split P ε) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  refine ⟨fun y x t => State y x (merge P t), fun y x => ?_,
    fun y x => proverLaw_split P (State y x) (h2 y x), fun y x τ hτ => ?_, fun y x => ?_⟩
  · show State y x (merge P (PTr.empty P.shape)) = true ↔ _
    rw [merge_empty]
    exact h1 y x
  · have hτ' : State y x (merge P (.full τ)) = false := hτ
    rw [merge_full] at hτ'
    exact h3 y x (Tr.merge P τ) hτ'
  · refine cast (congrArg (JointLaw N P.shape (Q.ann.split P Z) (Err.split P ε)) ?_)
      (jointLaw_split P Q.ann Z hZ ε _ (h4 y x))
    funext j
    cases x j <;> rfl

/-! ## 5a. The late form `SndBL` of (Snd-B) (Iop/Batch.lean) -/

theorem le_idx {s : Shape} (P : SPlan s) : ∀ n, n ≤ P.idx n := by
  induction P with
  | nil => exact fun n => Nat.le_refl n
  | keep r P ih =>
      rintro (_ | n)
      · exact Nat.le_refl 0
      · exact Nat.succ_le_succ (ih n)
  | cut c P ih =>
      rintro (_ | n)
      · exact Nat.le_refl 0
      · exact Nat.le_succ_of_le (ih (n + 1))

theorem localTo_snd {r : Round} {c : RCut r} {a : RAnn r} (b : ACut c a) {s : Shape} (A : RoundSplits s) :
    ∀ n, RoundSplits.LocalTo n (r :: s) (a, A) → RoundSplits.LocalTo n (c.snd :: s) (b.ann2, A)
  | 0, h => h
  | _ + 1, h => h

/-- Under `APlan.LoTo`: if the old rounds up to n are local, so are the new ones up to the first
part of round n. -/
theorem localTo_split {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A) (n : ℕ),
      RoundSplits.LocalTo n s A → APlan.LoTo P A Z n → RoundSplits.LocalTo (P.idx n) P.shape (A.split P Z) := by
  induction P with
  | nil => intro _ _ _ h _; exact h
  | keep r P ih =>
      rintro ⟨a, A⟩ Z (_ | n) h hZ
      · exact h
      · exact ⟨h.1, ih A Z n h.2 hZ⟩
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ (_ | n) h hZ
      · exact hZ.1
      · exact ⟨hZ.1, ih (b.ann2, A) Z (n + 1) (localTo_snd b A (n + 1) h) hZ.2⟩

/-- "If the state S0 is 0 before the prover message of round n, so is the state S1." -/
def SwitchLaw (n : ℕ) (s : Shape) (S0 S1 : PTr s → Bool) : Prop :=
  ∀ τ : AtP s, τ.idx = n → S0 (.atP τ) = false → S1 (.atP τ) = false

theorem switchLaw_glue {r : Round} (c : RCut r) {s : Shape} (x : c.fst.Msg) (n : ℕ)
    (S0 S1 : PTr (r :: s) → Bool) (h : SwitchLaw n (r :: s) S0 S1) :
    SwitchLaw n (c.snd :: s) (fun t => S0 (glueP c x t)) (fun t => S1 (glueP c x t))
  | .inl _, hn, h0 => h (.inl ()) hn h0
  | .inr (y, ch, τ), hn, h0 => h (.inr (c.join x y, ch, τ)) hn h0

/-- `SwitchLaw` before the old round n gives `SwitchLaw` before its first part. -/
theorem switchLaw_split {s : Shape} (P : SPlan s) :
    ∀ (n : ℕ) (S0 S1 : PTr s → Bool), SwitchLaw n s S0 S1 →
      SwitchLaw (P.idx n) P.shape (fun t => S0 (merge P t)) (fun t => S1 (merge P t)) := by
  induction P with
  | nil => intro _ _ _ _ τ; exact Empty.elim τ
  | keep r P ih =>
      rintro n S0 S1 h (_ | ⟨m', c', τ⟩) hn h0
      · cases n with
        | zero => exact h (.inl ()) rfl h0
        | succ n => exact absurd hn (Nat.succ_ne_zero _).symm
      · cases n with
        | zero => exact absurd hn (Nat.succ_ne_zero _)
        | succ n =>
            exact ih n (fun t => S0 (PTr.cons m' c' t)) (fun t => S1 (PTr.cons m' c' t))
              (fun τ₁ h₁ => h (.inr (m', c', τ₁)) (congrArg (· + 1) h₁)) τ (Nat.succ.inj hn) h0
  | cut c P ih =>
      rintro n S0 S1 h (_ | ⟨x, u, τ⟩) hn h0
      · cases n with
        | zero => exact h (.inl ()) rfl h0
        | succ n => exact absurd hn (Nat.succ_ne_zero _).symm
      · cases n with
        | zero => exact absurd hn (Nat.succ_ne_zero _)
        | succ n =>
            exact ih (n + 1) (fun t => S0 (glueP c x t)) (fun t => S1 (glueP c x t))
              (switchLaw_glue c x (n + 1) S0 S1 h) τ (Nat.succ.inj hn) h0

theorem sndBL_split {Q : BatchInteractiveOracleProof X E} {P : SPlan Q.loc.shape} {Z : APlan P Q.ann}
    (hZ : APlan.OK P Q.ann Z) {N : ℕ} {early : X → X} {late : Option ℕ}
    (hlo : ∀ n, late = some n → APlan.LoTo P Q.ann Z n) {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (h : Q.SndBL N early late L ε) :
    (Q.split P Z).SndBL N early (late.map P.idx) L (Err.split P ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  refine ⟨fun n' hn' => ?_, fun y x t => State y x (merge P t), fun y x hL => ?_,
    fun y x => proverLaw_split P (State y x) (h2 y x), fun y x τ hL hn' => ?_,
    fun y x τ hL hτ => ?_, fun y x => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hn'
    exact ⟨lt_of_lt_of_le (h0 n hn).1 (le_idx P n),
      localTo_split P Q.ann Z n (h0 n hn).2 (hlo n hn)⟩
  · show State y (early x) (merge P (PTr.empty P.shape)) = false
    rw [merge_empty]
    exact h1 y x hL
  · obtain ⟨n, hn, hi⟩ := Option.map_eq_some_iff.1 hn'
    exact switchLaw_split P n (State y (early x)) (State y x)
      (fun τ₁ h₁ => hsw y x τ₁ hL (by rw [hn, h₁])) τ hi.symm
  · have hτ' : State y (if late.isSome then x else early x) (merge P (.full τ)) = false := by
      have e : (late.map P.idx).isSome = late.isSome := by cases late <;> rfl
      rw [← e]
      exact hτ
    rw [merge_full] at hτ'
    exact h3 y x (Tr.merge P τ) hL hτ'
  · refine cast (congrArg (JointLaw N P.shape (Q.ann.split P Z) (Err.split P ε)) ?_)
      (jointLaw_split P Q.ann Z hZ ε _ (h4 y x))
    funext j
    cases x j <;> rfl

/-! ## 6. Positions read in the external string -/

theorem allReads_split (Q : BatchInteractiveOracleProof X E) (P : SPlan Q.loc.shape) (Z : APlan P Q.ann) {N : ℕ}
    (x : Fin N → Option X) (ρ : BRho N P.shape (Q.ann.split P Z)) :
    (Q.split P Z).allReads x ρ = Q.allReads x (BRho.merge P Q.ann Z ρ) := by
  classical
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.biUnion_congr rfl fun j _ => ?_
  cases x j with
  | none => rfl
  | some xj =>
    show Q.loc.extReads xj (Rho.merge P (ρ.slot j)) =
      Q.loc.extReads xj ((BRho.merge P Q.ann Z ρ).slot j)
    rw [slot_merge]

theorem readsAtMost_split {Q : BatchInteractiveOracleProof X E} (P : SPlan Q.loc.shape) (Z : APlan P Q.ann)
    {N q : ℕ} (h : Q.ReadsAtMost N q) : (Q.split P Z).ReadsAtMost N q :=
  fun x ρ => by rw [allReads_split]; exact h x _

theorem extShared_split {Q : BatchInteractiveOracleProof X E} (P : SPlan Q.loc.shape)
    (Z : APlan P Q.ann) (h : Q.ExtShared) : (Q.split P Z).ExtShared :=
  fun x x' ρ ρ' hρ =>
    h x x' (Rho.merge P ρ) (Rho.merge P ρ')
      (by
        rw [← sh_merge P Q.ann Z, ← sh_merge P Q.ann Z]; exact congrArg (RhoSh.merge P Q.ann Z) hρ)

/-! ## 7. One slot of the honest prover -/

theorem zip_split {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A), APlan.OK P A Z →
      ∀ (σ0 : SStrat s A) (σj : LStrat s A),
        (SStrat.split P A Z σ0).zip (LStrat.split P A Z σj) = Strat.split P (σ0.zip σj) := by
  induction P with
  | nil => intro _ _ _ _ _; rfl
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hZ ⟨m0, k0⟩ ⟨mj, kj⟩
      show (a.join m0 mj,
          fun ch : r.Chal =>
            (SStrat.split P A Z (k0 (a.kind.shOf ch))).zip (LStrat.split P A Z (kj ch))) =
        ((a.join m0 mj,
          fun ch : r.Chal =>
            Strat.split P
              ((k0 (a.kind.shOf ch)).zip (kj ch))) : r.Msg × (r.Chal → Strat P.shape Unit))
      congr 1
      funext ch
      rw [ih A Z hZ]
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨m0, k0⟩ ⟨mj, kj⟩
      show (b.ann1.join (b.m0 m0).1 (b.mj mj).1,
          fun _ : Unit =>
            (SStrat.split P (b.ann2, A) Z ((b.m0 m0).2, k0)).zip
              (LStrat.split P (b.ann2, A) Z ((b.mj mj).2, kj))) =
        ((c.left (a.join m0 mj),
          fun _ : Unit =>
            Strat.split P
              (c.right (a.join m0 mj),
                fun ch : r.Chal =>
                  (k0 (a.kind.shOf ch)).zip (kj ch))) : c.fst.Msg × (Unit → Strat P.shape Unit))
      rw [hZ.1.join, RCut.left_join, RCut.right_join]
      congr 1
      funext _
      rw [ih (b.ann2, A) Z hZ.2]
      rfl

variable {Wt : Type}

theorem one_strat_split {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : SPlan Q.loc.shape}
    {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) (w : Wt) (x : X) (c : H.Coin0 × H.Coin) :
    (H.split P Z).one.strat w x c = Strat.split P (H.one.strat w x c) :=
  zip_split P Q.ann Z hZ _ _

theorem mem_one_withheld_split {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (P : SPlan Q.loc.shape)
    (Z : APlan P Q.ann) (w : Wt) (x : X) (ρ : Rho P.shape) :
    ρ ∈ (H.split P Z).one.withheld w x ↔ Rho.merge P ρ ∈ H.one.withheld w x := by
  show ((RhoLo.merge P Q.ann Z (Rho.lo (Q.ann.split P Z) ρ) ∈ H.Bad ∨
        H.stop0 (RhoSh.merge P Q.ann Z (Rho.sh (Q.ann.split P Z) ρ)) = true) ∨
      RhoLo.merge P Q.ann Z (Rho.lo (Q.ann.split P Z) ρ) ∈ H.Hid w x) ↔
    ((Rho.lo Q.ann (Rho.merge P ρ) ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann (Rho.merge P ρ)) = true) ∨
      Rho.lo Q.ann (Rho.merge P ρ) ∈ H.Hid w x)
  rw [lo_merge, sh_merge]

theorem acc_split {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid)
    {P : SPlan Q.loc.shape} {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) :
    (H.split P Z).Acc valid := by
  intro w x c ρ hv hρ
  show Q.loc.accept x (H.ext w) (Tr.merge P (((H.split P Z).one.strat w x c).run ρ).1) = true
  rw [one_strat_split H hZ]
  exact (congrArg (Q.loc.accept x (H.ext w)) (Strat.run_split P (H.one.strat w x c) ρ)).trans
    (h w x c (Rho.merge P ρ) hv fun hm => hρ ((mem_one_withheld_split H P Z w x ρ).2 hm))

theorem prRho_one_withheld_split {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (P : SPlan Q.loc.shape)
    (Z : APlan P Q.ann) (w : Wt) (x : X) :
    prRho ((H.split P Z).one.withheld w x) = prRho (H.one.withheld w x) := by
  have e : (H.split P Z).one.withheld w x = {ρ | Rho.merge P ρ ∈ H.one.withheld w x} :=
    Set.ext fun ρ => mem_one_withheld_split H P Z w x ρ
  rw [e]
  exact prRho_merge P (H.one.withheld w x)

/-! ## 8. The whole verifier randomness of a batch: a bijection -/

theorem unitAll_eq {N : ℕ} : ∀ (k : Kind) (v : k.All N Unit), Kind.unitAll N k = v
  | .sh, _ => rfl
  | .lo, _ => rfl

theorem split_merge {N : ℕ} {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A) (ρ : BRho N P.shape (A.split P Z)),
      BRho.split P A Z (BRho.merge P A Z ρ) = ρ := by
  induction P with
  | nil => intro _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ⟨v, ρ⟩
      exact Prod.ext (unitAll_eq b.kind v) (ih (b.ann2, A) Z ρ)

theorem merge_split {N : ℕ} {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A) (ρ : BRho N s A), BRho.merge P A Z (BRho.split P A Z ρ) = ρ := by
  induction P with
  | nil => intro _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ρ
      exact ih (b.ann2, A) Z ρ

def mergeEquiv (N : ℕ) {s : Shape} (P : SPlan s) (A : RoundSplits s) (Z : APlan P A) :
    BRho N P.shape (A.split P Z) ≃ BRho N s A :=
  ⟨BRho.merge P A Z, BRho.split P A Z, split_merge P A Z, merge_split P A Z⟩

/-- The preimage of a set of values of the whole verifier randomness of a batch has the same
probability. -/
theorem prBRho_merge {N : ℕ} {s : Shape} (P : SPlan s) (A : RoundSplits s)
    (Z : APlan P A) (S : Set (BRho N s A)) :
    prBRho {ρ : BRho N P.shape (A.split P Z) | BRho.merge P A Z ρ ∈ S} = prBRho S := by
  unfold prBRho
  rw [← map_unif_equiv (mergeEquiv N P A Z), pr_map]
  rfl

/-! ## 9. Honest-verifier zero knowledge for sets of slots (`BatchHonestProver.HVZK`) -/

open BatchPull (slotOut output_eq)

theorem slotOut_split {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : SPlan Q.loc.shape}
    (hP : P.OK) {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) (w : Wt) (ox : Option X)
    (ρ : Rho P.shape) (c : H.Coin0 × H.Coin) :
    slotOut (H.split P Z) w ox ρ c = (slotOut H w ox (Rho.merge P ρ) c).map (DView.split P) := by
  classical
  cases ox with
  | none => rfl
  | some xj =>
    by_cases h : Rho.merge P ρ ∈ H.one.withheld w xj
    · have e1 : slotOut (H.split P Z) w (some xj) ρ c = none :=
        if_pos ((mem_one_withheld_split H P Z w xj ρ).2 h)
      have e2 : slotOut H w (some xj) (Rho.merge P ρ) c = none := if_pos h
      rw [e1, e2]
      rfl
    · have e1 : slotOut (H.split P Z) w (some xj) ρ c
          = some ((Q.loc.split P).dview xj (H.ext w) (((H.split P Z).one.strat w xj c).run ρ).1) :=
        if_neg fun hm => h ((mem_one_withheld_split H P Z w xj ρ).1 hm)
      have e2 : slotOut H w (some xj) (Rho.merge P ρ) c =
          some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj c).run (Rho.merge P ρ)).1) := if_neg h
      rw [e1, e2, one_strat_split H hZ, InteractiveOracleProof.dview_split hP]
      exact congrArg (fun t => some (DView.split P (Q.loc.dview xj (H.ext w) t)))
        (Strat.run_split P (H.one.strat w xj c) ρ)

/-- Under `P.OK`, `APlan.OK`: the output for J at ρ is the image of the output for J at the old
challenges (`BRho.merge`). -/
theorem output_split {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : SPlan Q.loc.shape} (hP : P.OK)
    {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N P.shape (Q.ann.split P Z)) (J : Finset (Fin N)) :
    (H.split P Z).output w x ρ J =
      (H.output w x (BRho.merge P Q.ann Z ρ) J).map fun f j => (f j).map (DView.split P) := by
  rw [output_eq, output_eq, PMF.map_comp]
  refine congrArg (fun g => PMF.map g (unif (H.Coin0 × (Fin N → H.Coin)))) ?_
  funext c j
  show slotOut (H.split P Z) w (x j) (ρ.slot j.1) (c.1, c.2 j) =
    (slotOut H w (x j) ((BRho.merge P Q.ann Z ρ).slot j.1) (c.1, c.2 j)).map (DView.split P)
  rw [slotOut_split H hP hZ, slot_merge]
  rfl

/-- Under `P.OK` and `APlan.OK`, HVZK for sets of slots in the exact form (`BatchHonestProver.HVZK`) is
preserved, with the same number. -/
theorem hvzk_split {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop}
    {z : ℝ≥0∞} (h : H.HVZK N valid z) {P : SPlan Q.loc.shape} (hP : P.OK)
    {Z : APlan P Q.ann} (hZ : APlan.OK P Q.ann Z) :
    (H.split P Z).HVZK N valid z := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun J xs ρs a =>
      (Sim J xs (fun j => Rho.merge P (ρs j)) a).map fun f j => (f j).map (DView.split P),
    fun w x hv J xs hxs => ?_⟩
  refine le_trans (le_trans (pr_mono _ ?_) (le_of_eq (prBRho_merge P Q.ann Z _)))
    (hS w x hv J xs hxs)
  intro ρ hρ heq
  apply hρ
  rw [output_split H hP hZ, heq]
  have e : (fun j : J => (BRho.merge P Q.ann Z ρ).slot j.1) =
      fun j : J => Rho.merge P (ρ.slot j.1) :=
    funext fun j => slot_merge j.1 P Q.ann Z ρ
  rw [e]
  rfl

/-! ## 10. The pattern `RoundSplits.Fmt` -/

/-- what `RoundSplits.Fmt` asks of one round of the kind k in the phase ph -/
def fmtAt (k : Kind) (ph : FPhase) (noShared noSlot : Prop) : Prop :=
  match k, ph with
  | .lo, _ => noShared
  | .sh, .loc => True
  | .sh, .shr => noSlot
  | .sh, _ => False

theorem fmtFrom_cons {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (ph : FPhase) :
    RoundSplits.FmtFrom (r :: s) (a, A) ph ↔
    fmtAt a.kind ph a.NoShared a.NoSlot ∧ RoundSplits.FmtFrom s A (FPhase.after a.kind ph) := by
  obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
  cases k
  · cases ph
    · exact ⟨fun h => h.elim, fun h => h.1.elim⟩
    · exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    · exact Iff.rfl
    · exact ⟨fun h => h.elim, fun h => h.1.elim⟩
  · exact Iff.rfl

/-- The table of `FPhase.fit` is right (format, phase: Iop/BatchFmt.lean): if the old round has a
format in the phase ph and the split fits, and a component that the old round lacks both parts lack
(hS, hL), the first part has a format in ph, the remainder has one in the phase after it, and the
phase after both is the phase after the old round. (S, L: the old round has no shared, no slot's
component; S1, L1, S2, L2: the same for the two parts.) -/
theorem fit_table (k1 k : Kind) (ph : FPhase) {S L S1 L1 S2 L2 : Prop} (hS : S → S1 ∧ S2)
    (hL : L → L1 ∧ L2) (h : fmtAt k ph S L) (hF : FPhase.fit k1 k ph L2 S1) :
    fmtAt k1 ph S1 L1 ∧
    fmtAt k (FPhase.after k1 ph) S2 L2 ∧
    FPhase.after k (FPhase.after k1 ph) = FPhase.after k ph := by
  cases k1 <;> cases k <;> cases ph <;> simp_all [fmtAt, FPhase.fit, FPhase.after, FPhase.afterLo]

theorem fmtFrom_split {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A), APlan.OK P A Z →
      ∀ ph : FPhase,
        RoundSplits.FmtFrom s A ph → APlan.Fit P A Z ph → RoundSplits.FmtFrom P.shape (A.split P Z) ph := by
  induction P with
  | nil => intro _ _ _ _ _ _; trivial
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hZ ph h hF
      obtain ⟨h1, h2⟩ := (fmtFrom_cons a A ph).1 h
      exact (fmtFrom_cons a (RoundSplits.split P A Z) ph).2 ⟨h1, ih A Z hZ _ h2 hF⟩
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ ph h hF
      obtain ⟨h1, h2⟩ := (fmtFrom_cons a A ph).1 h
      obtain ⟨t1, t2, t3⟩ :=
        fit_table b.kind a.kind ph (noShared_cut hZ.1) (noSlot_cut hZ.1) h1 hF.1
      refine (fmtFrom_cons b.ann1 (RoundSplits.split P (b.ann2, A) Z) ph).2
        ⟨t1, ih (b.ann2, A) Z hZ.2 _ ?_ hF.2⟩
      exact (fmtFrom_cons b.ann2 A _).2
        ⟨t2, by rw [show FPhase.after b.ann2.kind _ = FPhase.after a.kind ph from t3]; exact h2⟩

theorem fit_lo {k1 : Kind} {ph : FPhase} {p q : Prop} (h : FPhase.fit k1 .lo ph p q) :
    k1 = .lo := by
  cases k1
  · cases ph <;> exact h.elim
  · rfl

theorem loTo_of_fit {s : Shape} (P : SPlan s) :
    ∀ (A : RoundSplits s) (Z : APlan P A) (n : ℕ) (ph : FPhase),
      RoundSplits.LocalTo n s A → APlan.Fit P A Z ph → APlan.LoTo P A Z n := by
  induction P with
  | nil => intro _ _ _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨a, A⟩ Z (_ | n) ph h hF
      · trivial
      · exact ih A Z n _ h.2 hF
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ n ph h hF
      have hk : a.kind = .lo := by
        cases n with
        | zero => exact h
        | succ n => exact h.1
      have hF1 : FPhase.fit b.kind a.kind ph b.ann2.NoSlot b.ann1.NoShared := hF.1
      rw [hk] at hF1
      exact ⟨fit_lo hF1, ih (b.ann2, A) Z n _ (localTo_snd b A n h) hF.2⟩

end BatchSplit


theorem splitLoTo : Spec.splitLoTo := fun _ P A Z n ph h hF =>
  BatchSplit.loTo_of_fit P A Z n ph h hF

open BatchSplit in
/-- `RoundSplits.Fmt` is preserved by a plan that fits and satisfies `APlan.OK`, and `ExtShared` by every
plan. -/
theorem splitFmtB : Spec.splitFmtB := fun _ _ Q P Z =>
  ⟨fun hZ h hF => fmtFrom_split P Q.ann Z hZ .first h hF, extShared_split P Z⟩

/-! ## 11. The record `BatchProtocol` -/

open BatchSplit in
/-- `BatchProtocol.Props` is preserved, with the same numbers, under the hypotheses of `Spec.splitPropsB`. -/
theorem splitPropsB : Spec.splitPropsB := by
  intro I X L Ryes Rno M PT PL PB ZB hT hL hB hZ hlo h
  exact
    { sub := h.sub
      wired := ⟨h.wired.dec_enc, h.wired.extT, h.wired.extL, h.wired.extB⟩
      sound :=
        ⟨let ⟨ε, hb, hs⟩ := h.sound.sndT; ⟨Err.split PT ε, hb.split PT, hs.split PT⟩,
         let ⟨ε, hb, hs⟩ := h.sound.sndL; ⟨Err.split PL ε, hb.split PL, hs.split PL⟩,
         let ⟨ε, hb, hs⟩ := h.sound.sndB; ⟨Err.split PB ε, hb.split PB, sndBL_split hZ hlo hs⟩⟩
      reads :=
        ⟨fun x ρ => h.reads.cntT x (Rho.merge PT ρ),
          fun x ρ => h.reads.cntLp x (Rho.merge PL ρ),
          fun x ρ => h.reads.cntLc x (Rho.merge PL ρ),
          readsAtMost_split PB ZB h.reads.cntB,
          h.reads.hidE⟩
      hidden := ⟨h.hidden.hidT.split hT, h.hidden.hidL.split hL, hvzk_split h.hidden.hidB hB hZ⟩
      complete :=
        ⟨h.complete.accT.split PT,
          h.complete.accL.split PL,
          acc_split h.complete.accB hZ,
          fun w x => (le_of_eq (L.honestOfflineProver.prRho_withheld_split PT w x)).trans (h.complete.prT w x),
          fun w x => (le_of_eq (L.honestLinkProver.prRho_withheld_split PL w x)).trans (h.complete.prL w x),
          fun w x hv =>
            (le_of_eq (prRho_one_withheld_split L.honestOnlineBatchProver PB ZB w x)).trans (h.complete.prB w x hv)⟩
      localT := h.localT.split hT
      localL := h.localL.split hL
      localB := h.localB.split hB
      cohB := coherent_split PB hB L.onlineBatch.ann ZB hZ h.cohB
      pointT := h.pointT.map (Shape.IsPoint.split PT hT)
      pointL := h.pointL.map (Shape.IsPoint.split PL hL)
      pointB := h.pointB.map (Shape.IsPoint.split PB hB) }

end Iop
