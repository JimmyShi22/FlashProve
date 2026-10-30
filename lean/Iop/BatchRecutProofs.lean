-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchRecutProofs.lean: the proofs of the statements of Iop/BatchRecut.lean.
  `recutPropsB`: `BatchProtocol.Props` except soundness after a plan of splits and merges (statement and
    hypotheses: Iop/BatchRecut.lean).
  `recutFmtB`: `RoundSplits.Fmt` and `ExtShared` after such a plan (statement and hypotheses:
    Iop/BatchRecut.lean).
Soundness is preserved for three explicit lists of errors, which grow at a merge, under the
hypotheses of `BatchProtocol.SoundAt.recut`. This file also has the simulator for sets of slots as a term
(`simRecutB`, `simRecutB_good`). Helpers: namespace `Iop.BatchRecut`. (Words of this library:
lean/GLOSSARY.md.)
The main lemmas are inductions on the plan; the cases are those of Iop/BatchSplitProofs.lean and
Iop/BatchJoinProofs.lean. Because of the merges by (J1) (header of Iop/BatchJoinProofs.lean), the
condition on prover messages is carried through the induction together with the condition on
challenges.

Notation: `St : Fin N → Option (PTr s → Bool)` in `JointLaw` (Iop/Batch.lean): St j is the state
function of slot j on what is left of the protocol (none: the slot is empty);
`State : E.Str → X → PTr Q.loc.shape → Bool` in `SndB` (Iop/Batch.lean): a function State(Π, τ) ∈
{0,1} of the external oracle and a partial local transcript of a non-empty slot; `PTr s : Type`
(Iop/State.lean): partial transcripts: at the prover (`atP`), at the verifier (`atV`), or full
(`full`); `SwitchLaw n s S0 S1 : Prop` (Iop/BatchSplitProofs.lean): if the state S0 is 0 before the
prover message of round n, so is the state S1; `RoundSplits.LocalTo n s A : Prop` (Iop/Batch.lean): the
rounds 0, .., n exist and are local; `early : X → X` (a field of `BatchProtocol`, Iop/Batch.lean): what of an
instance layer 1 (the compiler) writes into the first query of the chain of a slot of Batch;
`late : Option ℕ` (there): the round of Batch (counted from 0) into whose query layer 1 writes the
whole instance; none: there is no such round; `u : r1.Chal` in `XPlan.msg r1 r2 u X`
(Iop/Recut.lean): (J1): u is a value of the challenge of r1; `XPlan.OK` asks that it is the only
one.
-/
import Iop.BatchRecut
import Iop.RecutProofs
import Iop.BatchSplitProofs
import Iop.BatchJoinProofs
import Iop.SoundAt
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

namespace BatchRecut
open BatchSplit
  (slot_snd lo_snd sh_snd coherent_cut glueP glueP_cons proverLaw_glue RoundLaw join_symm
    localTo_snd SwitchLaw switchLaw_glue unitAll_eq fmtAt fmtFrom_cons fit_table
    noShared_cut noSlot_cut)
open BatchJoin
  (slot_constAll slot_msg lo_msg sh_msg slot_chal lo_chal sh_chal coherent_msg unMsgP unChalP
    unMsgP_cons unChalP_cons roundLaw_map roundLaw_mono roundLaw_noFlip roundLaw_two
    join_split proverLaw_chal proverLaw_msg switch_msg switch_chal eq_constAll pairAll_fst_snd
    fst_pairAll snd_pairAll sndSh_shOf slot_sndAll fitMsg_table after_after noShared_msg
    noSlot_msg unitZero_of_below)
open BatchH4 (ProverLaw)

/-! ## 1. Challenges -/

theorem slot_old {N : ℕ} (j : Fin N) {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (h : AXPlan.Kinds P A Z) (ρ : BRho N P.shape (A.recut P Z)),
      (BRho.old P A Z h ρ).slot j = Rho.old P (ρ.slot j) := by
  induction P with
  | nil => intro _ _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z h ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z h ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ h ⟨v, ρ⟩
      exact (slot_snd b A j _).trans (ih (b.ann2, A) Z h ρ)
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      exact Prod.ext (slot_constAll j a1.kind u)
        ((slot_msg a1 a2 A j _).trans (ih (a1.joinMsg a2, A) Z h ρ))
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      refine (slot_chal A h.1 j (BRho.old P (a1.joinChal r2, A) Z h.2 ρ)).trans ?_
      rw [ih (a1.joinChal r2, A) Z h.2 ρ]
      rfl

theorem lo_old {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (h : AXPlan.Kinds P A Z) (ρ : Rho P.shape),
      RhoLo.old P A Z h (Rho.lo (A.recut P Z) ρ) = Rho.lo A (Rho.old P ρ) := by
  induction P with
  | nil => intro _ _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z h ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z h ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ h ⟨v, ρ⟩
      exact (ih (b.ann2, A) Z h ρ).trans (lo_snd b A _).symm
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      exact Prod.ext rfl ((ih (a1.joinMsg a2, A) Z h ρ).trans (lo_msg a1 a2 A _).symm)
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      have e := ih (a1.joinChal r2, A) Z h.2 ρ
      show (a1.kind.mapLo Prod.fst (RhoLo.old P (a1.joinChal r2, A) Z h.2 (Rho.lo _ ρ)).1,
          Kind.sndLo a1.kind a2.kind h.1 (RhoLo.old P (a1.joinChal r2, A) Z h.2 (Rho.lo _ ρ)).1,
          (RhoLo.old P (a1.joinChal r2, A) Z h.2 (Rho.lo _ ρ)).2) = _
      rw [e]
      exact lo_chal A h.1 (Rho.old P ρ)

theorem sh_old {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (h : AXPlan.Kinds P A Z) (ρ : Rho P.shape),
      RhoSh.old P A Z h (Rho.sh (A.recut P Z) ρ) = Rho.sh A (Rho.old P ρ) := by
  induction P with
  | nil => intro _ _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z h ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z h ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ h ⟨v, ρ⟩
      exact (ih (b.ann2, A) Z h ρ).trans (sh_snd b A _).symm
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      exact Prod.ext rfl ((ih (a1.joinMsg a2, A) Z h ρ).trans (sh_msg a1 a2 A _).symm)
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z h ρ
      have e := ih (a1.joinChal r2, A) Z h.2 ρ
      show (a1.kind.mapSh Prod.fst (RhoSh.old P (a1.joinChal r2, A) Z h.2 (Rho.sh _ ρ)).1,
          Kind.sndSh a1.kind a2.kind h.1 (RhoSh.old P (a1.joinChal r2, A) Z h.2 (Rho.sh _ ρ)).1,
          (RhoSh.old P (a1.joinChal r2, A) Z h.2 (Rho.sh _ ρ)).2) = _
      rw [e]
      exact sh_chal A h.1 (Rho.old P ρ)

/-! ## 2. Annotations -/

theorem coherent_recut {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z → A.Coherent → (A.recut P Z).Coherent := by
  induction P with
  | nil => intro _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨a, A⟩ Z hZ h
      exact ⟨h.1, ih hP A Z hZ h.2⟩
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ h
      obtain ⟨h1, h2⟩ := coherent_cut hP.1 hZ.1 h.1
      exact ⟨h1, ih hP.2 (b.ann2, A) Z hZ.2 ⟨h2, h.2⟩⟩
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ h
      exact ih hP.2 (a1.joinMsg a2, A) Z hZ ⟨coherent_msg h.1 h.2.1, h.2.2⟩
  | chal r1 r2 np P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ h
      exact ih hP.2 (a1.joinChal r2, A) Z hZ ⟨⟨h.1.plain_join, h.1.rd_shared, h.1.rd_own⟩, h.2.2⟩

/-! ## 3. Prefixes of transcripts -/

/-- The old prefix of a new one. If the new one ends inside a prover message that is sent in parts,
these parts are dropped (where a merged round is split: those of the whole merged message). -/
def oldP : {s : Shape} → (P : XPlan s) → PTr P.shape → PTr s
  | _, .nil => fun t => t
  | _, .keep r P => fun (t : PTr (r :: P.shape)) => match t with
      | .atP (.inl _) => .atP (.inl ())
      | .atP (.inr z) => PTr.cons z.1 z.2.1 (oldP P (.atP z.2.2))
      | .atV (.inl m) => .atV (.inl m)
      | .atV (.inr z) => PTr.cons z.1 z.2.1 (oldP P (.atV z.2.2))
      | .full z => PTr.cons z.1 z.2.1 (oldP P (.full z.2.2))
  | _, .cut c P => fun (t : PTr (c.fst :: P.shape)) => match t with
      | .atP (.inl _) => .atP (.inl ())
      | .atP (.inr z) => glueP c z.1 (oldP P (.atP z.2.2))
      | .atV (.inl _) => .atP (.inl ())
      | .atV (.inr z) => glueP c z.1 (oldP P (.atV z.2.2))
      | .full z => glueP c z.1 (oldP P (.full z.2.2))
  | _, .msg _ _ u P => fun t => unMsgP u (oldP P t)
  | _, .chal _ _ _ P => fun t => unChalP (oldP P t)

theorem oldP_cons_keep (r : Round) {s : Shape} (P : XPlan s) (m : r.Msg) (ch : r.Chal) :
    ∀ t : PTr P.shape, oldP (.keep r P) (PTr.cons m ch t) = PTr.cons m ch (oldP P t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem oldP_cons_cut {r : Round} {s : Shape} (c : RCut r) (P : XPlan (c.snd :: s))
    (x : c.fst.Msg) (u : Unit) :
    ∀ t : PTr P.shape, oldP (.cut c P) (PTr.cons (r := c.fst) x u t) = glueP c x (oldP P t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem oldP_empty {s : Shape} (P : XPlan s) : oldP P (PTr.empty P.shape) = PTr.empty s := by
  induction P with
  | nil => rfl
  | keep r P ih => rfl
  | cut c P ih => rfl
  | msg r1 r2 u P ih =>
      show unMsgP u (oldP P (PTr.empty P.shape)) = _
      rw [ih]
      rfl
  | chal r1 r2 np P ih =>
      show unChalP (oldP P (PTr.empty P.shape)) = _
      rw [ih]
      rfl

theorem oldP_full {s : Shape} (P : XPlan s) :
    ∀ τ : Tr P.shape, oldP P (.full τ) = .full (Tr.old P τ) := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, ch, τ⟩
      show PTr.cons m ch (oldP P (.full τ)) = _
      rw [ih]
      rfl
  | cut c P ih =>
      rintro ⟨x, u, τ⟩
      show glueP c x (oldP P (.full τ)) = _
      rw [ih]
      rfl
  | msg r1 r2 u P ih =>
      intro τ
      show unMsgP u (oldP P (.full τ)) = _
      rw [ih]
      rfl
  | chal r1 r2 np P ih =>
      intro τ
      show unChalP (oldP P (.full τ)) = _
      rw [ih]
      rfl

/-! ## 4. The soundness property `SndB` (Snd-B) -/

/-- At every merge by (J1) the error of the first of the two rounds is 0. -/
def MsgZero : {s : Shape} → (P : XPlan s) → Err s → Prop
  | _, .nil => fun _ => True
  | _, .keep _ P => fun (ε : ℕ × Err _) => MsgZero P ε.2
  | _, .cut _ P => fun ε => MsgZero P ε
  | _, .msg r1 r2 (s := s) _ P => fun (ε : ℕ × ℕ × Err s) =>
      ε.1 = 0 ∧
      MsgZero P (show Err (r1.joinMsg r2 :: s)
          from (ε.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * ε.2.1, ε.2.2))
  | _, .chal r1 r2 (s := s) _ P => fun (ε : ℕ × ℕ × Err s) =>
      MsgZero P (show Err (r1.joinChal r2 :: s)
          from (ε.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * ε.2.1, ε.2.2))

theorem msgZero_of_unitZero {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ ε : Err s, ε.UnitZero → MsgZero P ε := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih =>
      rintro ⟨e, ε⟩ h
      exact ih hP ε h.2
  | cut c P ih =>
      rintro ⟨e, ε⟩ h
      exact ih hP.2 (e, ε) h
  | @msg r1 r2 s u P ih =>
      rintro ⟨e1, e2, ε⟩ h
      have h1 : e1 = 0 := h.1 (card_eq_one_of_forall hP.1)
      refine ⟨h1, ih hP.2 _ ⟨fun hc => ?_, h.2.2⟩⟩
      rw [h1, h.2.1 hc, Nat.zero_mul, Nat.mul_zero]
  | @chal r1 r2 s np P ih =>
      rintro ⟨e1, e2, ε⟩ h
      refine ih hP.2 _ ⟨fun hc => ?_, h.2.2⟩
      have hc' : Fintype.card r1.Chal * Fintype.card r2.Chal = 1 := by
        rw [← Fintype.card_prod]; exact hc
      rw [h.1 (Nat.eq_one_of_mul_eq_one_right hc'), h.2.1 (Nat.eq_one_of_mul_eq_one_left hc'),
        Nat.zero_mul, Nat.mul_zero]

/-- `JointLaw` and `ProverLaw` are preserved together, with the errors `Err.recut P ε`, under
`P.OK`, `AXPlan.OK`, `AXPlan.Kinds`, `MsgZero`. -/
theorem joint_recut {N : ℕ} {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z → AXPlan.Kinds P A Z →
      ∀ (ε : Err s) (St : Fin N → Option (PTr s → Bool)), MsgZero P ε → JointLaw N s A ε St →
        (∀ j S, St j = some S → ProverLaw s S) →
        JointLaw N P.shape (A.recut P Z) (Err.recut P ε)
          (fun j => (St j).map fun S t => S (oldP P t)) ∧
        ∀ j S, St j = some S → ProverLaw P.shape (fun t => S (oldP P t)) := by
  induction P with
  | nil => exact fun _ _ _ _ _ _ _ _ _ => ⟨trivial, fun _ _ _ τ => Empty.elim τ⟩
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hZ hK ⟨e, ε⟩ St hz h hp
      have step : ∀ (m0 : a.M0) (m : Fin N → a.Mj) (v : a.kind.All N r.Chal), _ := fun m0 m v =>
        ih hP A Z hZ hK ε
            (fun j => (St j).map fun S τ => S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) τ)) hz
            ((h m0 m).2 v) fun j S' hS' => by
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          exact (hp j S hS).tail _ _
      refine ⟨fun (m0 : a.M0) (m : Fin N → a.Mj) => ⟨?_, fun v => ?_⟩, ?_⟩
      · refine (roundLaw_map (fun _ => oldP (.keep r P)) a.kind e St
          (fun j => .atV (Sum.inl (a.join m0 (m j))))
          (fun j ch => PTr.cons (a.join m0 (m j)) ch (PTr.empty P.shape))).2 ?_
        have e1 : (fun (j : Fin N) (ch : r.Chal) =>
              oldP (.keep r P) (PTr.cons (a.join m0 (m j)) ch (PTr.empty P.shape))) =
            fun j ch => PTr.cons (a.join m0 (m j)) ch (PTr.empty s) := by
          funext j ch
          rw [oldP_cons_keep, oldP_empty]
        rw [e1]
        exact (h m0 m).1
      · refine cast (congrArg (JointLaw N P.shape (A.recut P Z) (Err.recut P ε)) ?_) (step m0 m v).1
        funext j
        beta_reduce
        refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
        congr 1
        funext S t
        show S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) (oldP P t)) =
          S (oldP (.keep r P) (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) t))
        rw [oldP_cons_keep]
      · rintro j S hS (_ | ⟨m', c', τ⟩) m h0
        · exact hp j S hS (.inl ()) m h0
        · have := (step (a.split m').1 (fun _ => (a.split m').2) (Kind.constAll N a.kind c')).2 j
            (fun τ =>
                S (PTr.cons (a.join (a.split m').1 (a.split m').2)
                    (a.kind.slot (Kind.constAll N a.kind c') j) τ))
              (by show (St j).map _ = _; rw [hS]; rfl) τ m
          rw [join_split, slot_constAll] at this
          exact this h0
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ hK ε St hz h hp
      -- the conditions for the remainder of the round, with the first part x0, x fixed
      have h2 : ∀ (x0 : b.A.M0) (x : Fin N → b.A.Mj), JointLaw N (c.snd :: s) (b.ann2, A) ε
          (fun j => (St j).map fun S t => S (glueP c (b.ann1.join x0 (x j)) t)) := by
        intro x0 x
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
          show S
              (PTr.cons (a.join (b.m0.symm (x0, y0)) (b.mj.symm (x j, y j))) (a.kind.slot w j) t) =
            S (glueP c (b.ann1.join x0 (x j))
                (PTr.cons (r := c.snd) (b.ann2.join y0 (y j)) (a.kind.slot w j) t))
          rw [glueP_cons, hj]
      have step : ∀ (x0 : b.A.M0) (x : Fin N → b.A.Mj), _ := fun x0 x =>
        ih hP.2 (b.ann2, A) Z hZ.2 hK ε
            (fun j => (St j).map fun S t => S (glueP c (b.ann1.join x0 (x j)) t)) hz
            (h2 x0 x) fun j S' hS' => by
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          exact proverLaw_glue c _ S (hp j S hS)
      refine ⟨fun (x0 : b.A.M0) (x : Fin N → b.A.Mj) => ⟨?_, fun v => ?_⟩, ?_⟩
      · exact RoundLaw.zero (fun _ => oldP (.cut c P)) b.kind St
          (fun j => .atV (Sum.inl (b.ann1.join x0 (x j))))
          (fun j u => PTr.cons (r := c.fst) (b.ann1.join x0 (x j)) u (PTr.empty P.shape))
          (fun j u => by beta_reduce; rw [oldP_cons_cut, oldP_empty]; rfl)
      · refine cast (congrArg (JointLaw N P.shape (RoundSplits.recut P (b.ann2, A) Z) (Err.recut P ε)) ?_)
          (step x0 x).1
        funext j
        beta_reduce
        refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
        congr 1
        funext S t
        show S (glueP c (b.ann1.join x0 (x j)) (oldP P t)) =
          S (oldP (.cut c P) (PTr.cons (r := c.fst) (b.ann1.join x0 (x j)) (b.kind.slot v j) t))
        rw [oldP_cons_cut]
      · rintro j S hS (_ | ⟨x, u, τ⟩) m h0
        · exact h0
        · have := (step (b.ann1.split x).1 (fun _ => (b.ann1.split x).2)).2
            j (fun t => S (glueP c (b.ann1.join (b.ann1.split x).1 (b.ann1.split x).2) t))
            (by show (St j).map _ = _; rw [hS]; rfl) τ m
          rw [join_split] at this
          exact this h0
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ⟨e1, e2, ε⟩ St hz h hp
      obtain rfl : e1 = 0 := hz.1
      have hflip : ∀ j S, St j = some S →
          ∀ m1 : r1.Msg,
            S (.atV (.inl m1)) = false → S (PTr.cons m1 u (PTr.empty (r2 :: s))) = false := by
        intro j S hS m1 h0
        have hr := (h (a1.split m1).1 (fun _ => (a1.split m1).2)).1
        have := roundLaw_noFlip (k := a1.kind)
          (x0 := fun _ : Fin N =>
              (PTr.atV (Sum.inl (a1.join (a1.split m1).1 (a1.split m1).2)) : PTr (r1 :: r2 :: s)))
          (x1 := fun (_ : Fin N) (c : r1.Chal) =>
              PTr.cons (a1.join (a1.split m1).1 (a1.split m1).2) c (PTr.empty (r2 :: s)))
          hr hS (by rw [join_split]; exact h0) u
        rwa [join_split] at this
      have hA : JointLaw N (r1.joinMsg r2 :: s) (a1.joinMsg a2, A)
          (0 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε)
          (fun j => (St j).map fun S t => S (unMsgP u t)) := by
        intro (m0 : a1.M0 × a2.M0) (m : Fin N → a1.Mj × a2.Mj)
        obtain ⟨hr2, hrest2⟩ :=
          (h m0.1 fun j => (m j).1).2 (Kind.constAll N a1.kind u) m0.2 fun j => (m j).2
        refine ⟨?_, fun v => ?_⟩
        · refine (roundLaw_map (fun _ => unMsgP u) a2.kind _ St
            (fun j => .atV (Sum.inl ((a1.joinMsg a2).join m0 (m j)))) (fun j ch =>
              PTr.cons (r := r1.joinMsg r2) ((a1.joinMsg a2).join m0 (m j)) ch (PTr.empty s))).2 ?_
          have hr2' := (roundLaw_map
            (fun j τ =>
              PTr.cons (a1.join m0.1 (m j).1) (a1.kind.slot (Kind.constAll N a1.kind u) j) τ)
            a2.kind e2 St (fun j => .atV (Sum.inl (a2.join m0.2 (m j).2)))
            (fun j ch => PTr.cons (a2.join m0.2 (m j).2) ch (PTr.empty s))).1 hr2
          refine roundLaw_mono
            (Nat.le_trans (Nat.le_mul_of_pos_left e2 Fintype.card_pos) (Nat.le_add_left _ _)) ?_
          refine cast ?_ hr2'
          congr 1
          · funext j
            rw [slot_constAll]
            rfl
          · funext j ch
            rw [slot_constAll, unMsgP_cons]
            rfl
        · refine cast (congrArg (JointLaw N s A ε) ?_) (hrest2 v)
          funext j
          beta_reduce
          refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
          congr 1
          funext S t
          show S (PTr.cons (a1.join m0.1 (m j).1) (a1.kind.slot (Kind.constAll N a1.kind u) j)
                (PTr.cons (a2.join m0.2 (m j).2) (a2.kind.slot v j) t)) =
            S (unMsgP u (PTr.cons (r := r1.joinMsg r2)
                  ((a1.joinMsg a2).join m0 (m j)) (a2.kind.slot v j) t))
          rw [slot_constAll, unMsgP_cons]
          rfl
      obtain ⟨g1, g2⟩ := ih hP.2 (a1.joinMsg a2, A) Z hZ hK _ _ hz.2 hA fun j S' hS' => by
        obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
        exact proverLaw_msg u S (hp j S hS) (hflip j S hS)
      refine ⟨cast (congrArg (JointLaw N P.shape _ _) ?_) g1,
        fun j S hS => g2 j (fun t => S (unMsgP u t)) (by show (St j).map _ = _; rw [hS]; rfl)⟩
      funext j
      exact Option.map_map _ _ _
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ⟨e1, e2, ε⟩ St hz h hp
      have hd : a2.join (a2.split r2.dMsg).1 (a2.split r2.dMsg).2 = r2.dMsg := join_split a2 _
      have hA : JointLaw N (r1.joinChal r2 :: s) (a1.joinChal r2, A)
          (e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε)
          (fun j => (St j).map fun S t => S (unChalP t)) := by
        intro (m0 : a1.M0) (m : Fin N → a1.Mj)
        obtain ⟨hr1, hrest1⟩ := h m0 m
        refine ⟨?_, fun v => ?_⟩
        · refine (roundLaw_map (fun _ => unChalP) a1.kind _ St
            (fun j => .atV (Sum.inl (a1.join m0 (m j)))) (fun j (ch : r1.Chal × r2.Chal) =>
              PTr.cons (r := r1.joinChal r2) (a1.join m0 (m j)) ch (PTr.empty s))).2 ?_
          have key := roundLaw_two a1.kind a2.kind hK.1 e1 e2 St
            (fun j => .atV (Sum.inl (a1.join m0 (m j))))
            (fun j c1 => PTr.cons (a1.join m0 (m j)) c1 (PTr.empty (r2 :: s)))
            (fun j c1 => PTr.cons (a1.join m0 (m j)) c1 (.atV (Sum.inl r2.dMsg)))
            (fun j c1 c2 => PTr.cons (a1.join m0 (m j)) c1 (PTr.cons r2.dMsg c2 (PTr.empty s))) hr1
            (fun j S c1 hS h0 => hp j S hS (.inr (a1.join m0 (m j), c1, .inl ())) r2.dMsg h0)
            (fun v1 => by
              have := (roundLaw_map (fun j τ => PTr.cons (a1.join m0 (m j)) (a1.kind.slot v1 j) τ)
                  a2.kind e2 St
                  (fun _ => .atV (Sum.inl (a2.join (a2.split r2.dMsg).1 (a2.split r2.dMsg).2)))
                  (fun _ ch =>
                    PTr.cons (a2.join (a2.split r2.dMsg).1 (a2.split r2.dMsg).2) ch
                      (PTr.empty s))).1
                ((hrest1 v1 (a2.split r2.dMsg).1 fun _ => (a2.split r2.dMsg).2).1)
              rw [hd] at this
              exact this)
          refine cast ?_ key
          congr 1
          funext j ch
          rw [unChalP_cons]
        · refine cast (congrArg (JointLaw N s A ε) ?_)
            ((hrest1 (a1.kind.mapAll Prod.fst v) (a2.split r2.dMsg).1 fun _ =>
                (a2.split r2.dMsg).2).2
              (Kind.sndAll a1.kind a2.kind hK.1 v))
          funext j
          beta_reduce
          refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
          congr 1
          funext S t
          show S (PTr.cons (a1.join m0 (m j)) (a1.kind.slot (a1.kind.mapAll Prod.fst v) j)
                (PTr.cons (a2.join (a2.split r2.dMsg).1 (a2.split r2.dMsg).2)
                  (a2.kind.slot (Kind.sndAll a1.kind a2.kind hK.1 v) j) t)) =
            S (unChalP (PTr.cons (r := r1.joinChal r2) (a1.join m0 (m j)) (a1.kind.slot v j) t))
          rw [hd, BatchPull.slot_mapAll, slot_sndAll, unChalP_cons]
      obtain ⟨g1, g2⟩ := ih hP.2 (a1.joinChal r2, A) Z hZ hK.2 _ _ hz hA fun j S' hS' => by
        obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
        exact proverLaw_chal S (hp j S hS)
      refine ⟨cast (congrArg (JointLaw N P.shape _ _) ?_) g1,
        fun j S hS => g2 j (fun t => S (unChalP t)) (by show (St j).map _ = _; rw [hS]; rfl)⟩
      funext j
      exact Option.map_map _ _ _

variable {X : Type} {E : ExtSpec}

theorem sndB_recut {Q : BatchInteractiveOracleProof X E} {P : XPlan Q.loc.shape} {Z : AXPlan P Q.ann} (hP : P.OK)
    (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) {N : ℕ} (hN : 0 < N)
    {L : X → E.Str → Prop} {ε : Err Q.loc.shape} (hε : ε.UnitZero) (h : Q.SndB N L ε) :
    (Q.recut P Z).SndB N L (Err.recut P ε) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  have hz := msgZero_of_unitZero P hP ε hε
  refine ⟨fun y x t => State y x (oldP P t), fun y x => ?_, fun y x => ?_,
    fun y x τ hτ => ?_, fun y x => ?_⟩
  · show State y x (oldP P (PTr.empty P.shape)) = true ↔ _
    rw [oldP_empty]
    exact h1 y x
  · exact (joint_recut P hP Q.ann Z hZ hK ε (fun _ : Fin N => some (State y x)) hz (h4 y fun _ => some x) fun _ S hS => by
      obtain rfl := Option.some.inj hS
      exact h2 y x).2 ⟨0, hN⟩ (State y x) rfl
  · have hτ' : State y x (oldP P (.full τ)) = false := hτ
    rw [oldP_full] at hτ'
    exact h3 y x (Tr.old P τ) hτ'
  · refine cast (congrArg (JointLaw N P.shape (Q.ann.recut P Z) (Err.recut P ε)) ?_)
      (joint_recut P hP Q.ann Z hZ hK ε _ hz (h4 y x) fun j S hS => ?_).1
    · funext j
      cases x j <;> rfl
    · obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
      exact h2 y xj

/-! ## 4a. The late form `SndBL` of (Snd-B) (Iop/Batch.lean) -/

theorem late_msg {r1 r2 : Round} {s : Shape} {u : r1.Chal} {P : XPlan (r1.joinMsg r2 :: s)}
    {A : RoundSplits (r1 :: r2 :: s)}
    {Z : AXPlan P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))} :
    ∀ {n : ℕ}, AXPlan.Late (.msg r1 r2 u P) A Z n →
      n ≠ 1 ∧ AXPlan.Late P
        (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z (n - 1)
  | 0, h => ⟨Nat.zero_ne_one, h.2⟩
  | 1, h => h.elim
  | _ + 2, h => ⟨by omega, h⟩

theorem late_chal {r1 r2 : Round} {s : Shape} {np : r2.Pos → Empty}
    {P : XPlan (r1.joinChal r2 :: s)} {A : RoundSplits (r1 :: r2 :: s)}
    {Z : AXPlan P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))} :
    ∀ {n : ℕ}, AXPlan.Late (.chal r1 r2 np P) A Z n →
      n ≠ 1 ∧ AXPlan.Late P
        (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z (n - 1)
  | 0, h => ⟨Nat.zero_ne_one, h⟩
  | 1, h => h.elim
  | _ + 2, h => ⟨by omega, h⟩

/-- Under `AXPlan.Late`, `SwitchLaw` before the old round n gives `SwitchLaw` before the new round
`P.idx n`. -/
theorem switch_recut {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (n : ℕ), AXPlan.Late P A Z n →
      ∀ S0 S1 : PTr s → Bool, SwitchLaw n s S0 S1 →
        SwitchLaw (P.idx n) P.shape (fun t => S0 (oldP P t)) (fun t => S1 (oldP P t)) := by
  induction P with
  | nil => intro _ _ _ _ _ _ _ τ; exact Empty.elim τ
  | keep r P ih =>
      rintro ⟨a, A⟩ Z n hl S0 S1 h (_ | ⟨m', c', τ⟩) hn h0
      · cases n with
        | zero => exact h (.inl ()) rfl h0
        | succ n => exact absurd hn (Nat.succ_ne_zero _).symm
      · cases n with
        | zero => exact absurd hn (Nat.succ_ne_zero _)
        | succ n =>
            exact ih A Z n hl (fun t => S0 (PTr.cons m' c' t)) (fun t => S1 (PTr.cons m' c' t))
              (fun τ₁ h₁ => h (.inr (m', c', τ₁)) (congrArg (· + 1) h₁)) τ (Nat.succ.inj hn) h0
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ n hl S0 S1 h (_ | ⟨x, u, τ⟩) hn h0
      · cases n with
        | zero => exact h (.inl ()) rfl h0
        | succ n => exact absurd hn (Nat.succ_ne_zero _).symm
      · cases n with
        | zero => exact absurd hn (Nat.succ_ne_zero _)
        | succ n =>
            exact ih (b.ann2, A) Z (n + 1) hl.2 (fun t => S0 (glueP c x t))
              (fun t => S1 (glueP c x t))
              (switchLaw_glue c x (n + 1) S0 S1 h) τ (Nat.succ.inj hn) h0
  | msg r1 r2 u P ih =>
      rintro A Z n hl S0 S1 h
      obtain ⟨hn, hl'⟩ := late_msg hl
      exact ih _ Z (n - 1) hl' _ _ (switch_msg u n hn S0 S1 h)
  | chal r1 r2 np P ih =>
      rintro A Z n hl S0 S1 h
      obtain ⟨hn, hl'⟩ := late_chal hl
      exact ih _ Z (n - 1) hl' _ _ (switch_chal n hn S0 S1 h)

theorem localTo_recut {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (n : ℕ),
      AXPlan.Late P A Z n → RoundSplits.LocalTo n s A → RoundSplits.LocalTo (P.idx n) P.shape (A.recut P Z) := by
  induction P with
  | nil => intro _ _ _ _ h; exact h
  | keep r P ih =>
      rintro ⟨a, A⟩ Z (_ | n) hl h
      · exact h
      · exact ⟨h.1, ih A Z n hl h.2⟩
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ (_ | n) hl h
      · exact hl
      · exact ⟨hl.1, ih (b.ann2, A) Z (n + 1) hl.2 (localTo_snd b A (n + 1) h)⟩
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) hl h
      · exact ih (a1.joinMsg a2, A) Z 0 hl.2 hl.1
      · exact hl.elim
      · exact ih (a1.joinMsg a2, A) Z (n + 1) hl ⟨h.2.1, h.2.2⟩
  | chal r1 r2 np P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) hl h
      · exact ih (a1.joinChal r2, A) Z 0 hl h
      · exact hl.elim
      · exact ih (a1.joinChal r2, A) Z (n + 1) hl ⟨h.1, h.2.2⟩

theorem idx_pos {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (n : ℕ), AXPlan.Late P A Z n → 0 < n → 0 < P.idx n := by
  induction P with
  | nil => intro _ _ _ _ h; exact h
  | keep r P ih =>
      rintro ⟨a, A⟩ Z (_ | n) _ h
      · exact absurd h (Nat.lt_irrefl 0)
      · exact Nat.succ_pos _
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ (_ | n) _ h
      · exact absurd h (Nat.lt_irrefl 0)
      · exact Nat.succ_pos _
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) hl h
      · exact absurd h (Nat.lt_irrefl 0)
      · exact hl.elim
      · exact ih (a1.joinMsg a2, A) Z (n + 1) hl (Nat.succ_pos n)
  | chal r1 r2 np P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) hl h
      · exact absurd h (Nat.lt_irrefl 0)
      · exact hl.elim
      · exact ih (a1.joinChal r2, A) Z (n + 1) hl (Nat.succ_pos n)

theorem sndBL_recut {Q : BatchInteractiveOracleProof X E} {P : XPlan Q.loc.shape} {Z : AXPlan P Q.ann} (hP : P.OK)
    (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) {N : ℕ} (hN : 0 < N) {early : X → X}
    {late : Option ℕ} (hl : ∀ n, late = some n → AXPlan.Late P Q.ann Z n) {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (hε : ε.UnitZero) (h : Q.SndBL N early late L ε) :
    (Q.recut P Z).SndBL N early (late.map P.idx) L (Err.recut P ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  have hz := msgZero_of_unitZero P hP ε hε
  refine ⟨fun n' hn' => ?_, fun y x t => State y x (oldP P t), fun y x hL => ?_, fun y x => ?_,
    fun y x τ hL hn' => ?_, fun y x τ hL hτ => ?_, fun y x => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hn'
    exact ⟨idx_pos P Q.ann Z n (hl n hn) (h0 n hn).1,
      localTo_recut P Q.ann Z n (hl n hn) (h0 n hn).2⟩
  · show State y (early x) (oldP P (PTr.empty P.shape)) = false
    rw [oldP_empty]
    exact h1 y x hL
  · exact (joint_recut P hP Q.ann Z hZ hK ε (fun _ : Fin N => some (State y x)) hz (h4 y fun _ => some x) fun _ S hS => by
      obtain rfl := Option.some.inj hS
      exact h2 y x).2 ⟨0, hN⟩ (State y x) rfl
  · obtain ⟨n, hn, hi⟩ := Option.map_eq_some_iff.1 hn'
    exact switch_recut P Q.ann Z n (hl n hn) (State y (early x)) (State y x)
      (fun τ₁ h₁ => hsw y x τ₁ hL (by rw [hn, h₁])) τ hi.symm
  · have hτ' : State y (if late.isSome then x else early x) (oldP P (.full τ)) = false := by
      have e : (late.map P.idx).isSome = late.isSome := by cases late <;> rfl
      rw [← e]
      exact hτ
    rw [oldP_full] at hτ'
    exact h3 y x (Tr.old P τ) hL hτ'
  · refine cast (congrArg (JointLaw N P.shape (Q.ann.recut P Z) (Err.recut P ε)) ?_)
      (joint_recut P hP Q.ann Z hZ hK ε _ hz (h4 y x) fun j S hS => ?_).1
    · funext j
      cases x j <;> rfl
    · obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
      exact h2 y xj

/-! ## 5. Positions read in the external string -/

theorem allReads_recut (Q : BatchInteractiveOracleProof X E) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann)
    (hK : AXPlan.Kinds P Q.ann Z) {N : ℕ} (x : Fin N → Option X)
    (ρ : BRho N P.shape (Q.ann.recut P Z)) :
    (Q.recut P Z).allReads x ρ = Q.allReads x (BRho.old P Q.ann Z hK ρ) := by
  classical
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.biUnion_congr rfl fun j _ => ?_
  cases x j with
  | none => rfl
  | some xj =>
    show Q.loc.extReads xj (Rho.old P (ρ.slot j)) =
      Q.loc.extReads xj ((BRho.old P Q.ann Z hK ρ).slot j)
    rw [slot_old]

theorem readsAtMost_recut {Q : BatchInteractiveOracleProof X E} (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann)
    (hK : AXPlan.Kinds P Q.ann Z) {N q : ℕ} (h : Q.ReadsAtMost N q) :
    (Q.recut P Z).ReadsAtMost N q :=
  fun x ρ => by rw [allReads_recut Q P Z hK]; exact h x _

theorem extShared_recut {Q : BatchInteractiveOracleProof X E} (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann)
    (hK : AXPlan.Kinds P Q.ann Z) (h : Q.ExtShared) : (Q.recut P Z).ExtShared :=
  fun x x' ρ ρ' hρ => h x x' (Rho.old P ρ) (Rho.old P ρ') (by rw [← sh_old P Q.ann Z hK, ← sh_old P Q.ann Z hK]; exact congrArg (RhoSh.old P Q.ann Z hK) hρ)

/-! ## 6. One slot of the honest prover -/

theorem zip_recut {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ (hK : AXPlan.Kinds P A Z) (σ0 : SStrat s A) (σj : LStrat s A),
        (SStrat.recut P A Z hK σ0).zip (LStrat.recut P A Z σj) = Strat.recut P (σ0.zip σj) := by
  induction P with
  | nil => intro _ _ _ _ _ _; rfl
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hZ hK ⟨m0, k0⟩ ⟨mj, kj⟩
      show (a.join m0 mj,
          fun ch : r.Chal =>
            (SStrat.recut P A Z hK (k0 (a.kind.shOf ch))).zip (LStrat.recut P A Z (kj ch))) =
        ((a.join m0 mj,
          fun ch : r.Chal =>
            Strat.recut P
              ((k0 (a.kind.shOf ch)).zip (kj ch))) : r.Msg × (r.Chal → Strat P.shape Unit))
      congr 1
      funext ch
      rw [ih A Z hZ hK]
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ hK ⟨m0, k0⟩ ⟨mj, kj⟩
      show (b.ann1.join (b.m0 m0).1 (b.mj mj).1,
          fun _ : Unit =>
            (SStrat.recut P (b.ann2, A) Z hK ((b.m0 m0).2, k0)).zip
              (LStrat.recut P (b.ann2, A) Z ((b.mj mj).2, kj))) =
        ((c.left (a.join m0 mj),
          fun _ : Unit =>
            Strat.recut P
              (c.right (a.join m0 mj),
                fun ch : r.Chal =>
                  (k0 (a.kind.shOf ch)).zip (kj ch))) : c.fst.Msg × (Unit → Strat P.shape Unit))
      rw [hZ.1.join, RCut.left_join, RCut.right_join]
      congr 1
      funext _
      rw [ih (b.ann2, A) Z hZ.2 hK]
      rfl
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ⟨m0, k0⟩ ⟨mj, kj⟩
      refine (ih (a1.joinMsg a2, A) Z hZ hK _ _).trans ?_
      rcases h0 : k0 (a1.kind.shOf u) with ⟨m0', k0'⟩
      rcases hj : kj u with ⟨mj', kj'⟩
      show Strat.recut P
          (show Strat (r1.joinMsg r2 :: s) Unit
            from ((a1.joinMsg a2).join (m0, (k0 (a1.kind.shOf u)).1) (mj, (kj u).1),
            fun ch : r2.Chal => ((k0 (a1.kind.shOf u)).2 (a2.kind.shOf ch)).zip ((kj u).2 ch))) =
        Strat.recut P
          (show Strat (r1.joinMsg r2 :: s) Unit
            from (Round.msgPair (a1.join m0 mj)
              (SStrat.zip (s := r2 :: s) (A := (a2, A)) (k0 (a1.kind.shOf u)) (kj u)).1,
            (SStrat.zip (s := r2 :: s) (A := (a2, A)) (k0 (a1.kind.shOf u)) (kj u)).2))
      rw [h0, hj]
      rfl
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ⟨m0, k0⟩ ⟨mj, kj⟩
      refine (ih (a1.joinChal r2, A) Z hZ hK.2 _ _).trans ?_
      show Strat.recut P
          (show Strat (r1.joinChal r2 :: s) Unit
            from (a1.join m0 mj,
            fun ch : r1.Chal × r2.Chal =>
              ((k0 (a1.kind.mapSh Prod.fst (a1.kind.shOf ch))).2
                  (Kind.sndSh a1.kind a2.kind hK.1 (a1.kind.shOf ch))).zip
                ((kj ch.1).2 ch.2))) =
        Strat.recut P
          (show Strat (r1.joinChal r2 :: s) Unit
            from (a1.join m0 mj,
            fun ch : r1.Chal × r2.Chal =>
              (SStrat.zip (s := r2 :: s) (A := (a2, A)) (k0 (a1.kind.shOf ch.1)) (kj ch.1)).2 ch.2))
      refine congrArg
        (fun k : r1.Chal × r2.Chal → Strat s Unit =>
          Strat.recut P (show Strat (r1.joinChal r2 :: s) Unit from (a1.join m0 mj, k)))
        (funext fun ch => ?_)
      rw [BatchPull.shOf_map, sndSh_shOf]
      rcases h0 : k0 (a1.kind.shOf ch.1) with ⟨m0', k0'⟩
      rcases hj : kj ch.1 with ⟨mj', kj'⟩
      rfl

variable {Wt : Type}

theorem one_strat_recut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : XPlan Q.loc.shape}
    {Z : AXPlan P Q.ann} (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) (w : Wt)
    (x : X) (c : H.Coin0 × H.Coin) :
    (H.recut P Z hK).one.strat w x c = Strat.recut P (H.one.strat w x c) :=
  zip_recut P Q.ann Z hZ hK _ _

theorem mem_one_withheld_recut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (P : XPlan Q.loc.shape)
    (Z : AXPlan P Q.ann) (hK : AXPlan.Kinds P Q.ann Z) (w : Wt) (x : X) (ρ : Rho P.shape) :
    ρ ∈ (H.recut P Z hK).one.withheld w x ↔ Rho.old P ρ ∈ H.one.withheld w x := by
  show ((RhoLo.old P Q.ann Z hK (Rho.lo (Q.ann.recut P Z) ρ) ∈ H.Bad ∨
        H.stop0 (RhoSh.old P Q.ann Z hK (Rho.sh (Q.ann.recut P Z) ρ)) = true) ∨
      RhoLo.old P Q.ann Z hK (Rho.lo (Q.ann.recut P Z) ρ) ∈ H.Hid w x) ↔
    ((Rho.lo Q.ann (Rho.old P ρ) ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann (Rho.old P ρ)) = true) ∨
      Rho.lo Q.ann (Rho.old P ρ) ∈ H.Hid w x)
  rw [lo_old, sh_old]

theorem acc_recut {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {valid : Wt → X → Prop}
    (h : H.Acc valid) {P : XPlan Q.loc.shape} {Z : AXPlan P Q.ann} (hP : P.OK)
    (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) : (H.recut P Z hK).Acc valid := by
  intro w x c ρ hv hρ
  show Q.loc.accept x (H.ext w) (Tr.old P (((H.recut P Z hK).one.strat w x c).run ρ).1) = true
  rw [one_strat_recut H hZ hK]
  exact (congrArg (Q.loc.accept x (H.ext w)) (Strat.run_recut P hP (H.one.strat w x c) ρ)).trans
    (h w x c (Rho.old P ρ) hv fun hm => hρ ((mem_one_withheld_recut H P Z hK w x ρ).2 hm))

theorem prRho_one_withheld_recut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : XPlan Q.loc.shape}
    (hP : P.OK) (Z : AXPlan P Q.ann) (hK : AXPlan.Kinds P Q.ann Z) (w : Wt) (x : X) :
    prRho ((H.recut P Z hK).one.withheld w x) = prRho (H.one.withheld w x) := by
  have e : (H.recut P Z hK).one.withheld w x = {ρ | Rho.old P ρ ∈ H.one.withheld w x} :=
    Set.ext fun ρ => mem_one_withheld_recut H P Z hK w x ρ
  rw [e]
  exact prRho_old P hP (H.one.withheld w x)

/-! ## 7. The whole verifier randomness of a batch: a bijection, under `P.OK` and `AXPlan.Kinds` -/

theorem new_old {N : ℕ} {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (hK : AXPlan.Kinds P A Z) (ρ : BRho N P.shape (A.recut P Z)),
      BRho.new P A Z hK (BRho.old P A Z hK ρ) = ρ := by
  induction P with
  | nil => intro _ _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z hK ⟨v, ρ⟩
      exact Prod.ext rfl (ih A Z hK ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hK ⟨v, ρ⟩
      exact Prod.ext (unitAll_eq b.kind v) (ih (b.ann2, A) Z hK ρ)
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z hK ρ
      exact ih (a1.joinMsg a2, A) Z hK ρ
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z hK ρ
      have e := ih (a1.joinChal r2, A) Z hK.2 ρ
      show BRho.new P (a1.joinChal r2, A) Z hK.2
          (Kind.pairAll a1.kind a2.kind hK.1
              (a1.kind.mapAll Prod.fst (BRho.old P (a1.joinChal r2, A) Z hK.2 ρ).1)
              (Kind.sndAll a1.kind a2.kind hK.1 (BRho.old P (a1.joinChal r2, A) Z hK.2 ρ).1),
            (BRho.old P (a1.joinChal r2, A) Z hK.2 ρ).2) = ρ
      rw [pairAll_fst_snd]
      exact e

theorem old_new {N : ℕ} {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (hK : AXPlan.Kinds P A Z) (ρ : BRho N s A),
      BRho.old P A Z hK (BRho.new P A Z hK ρ) = ρ := by
  induction P with
  | nil => intro _ _ _ _; rfl
  | keep r P ih =>
      rintro ⟨a, A⟩ Z hK ⟨v, ρ⟩
      exact Prod.ext rfl (ih hP A Z hK ρ)
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hK ρ
      exact ih hP.2 (b.ann2, A) Z hK ρ
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z hK ⟨v, ρ⟩
      exact Prod.ext (eq_constAll hP.1 a1.kind v) (ih hP.2 (a1.joinMsg a2, A) Z hK ρ)
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z hK ⟨v1, v2, ρ⟩
      have e := ih hP.2 (a1.joinChal r2, A) Z hK.2 (Kind.pairAll a1.kind a2.kind hK.1 v1 v2, ρ)
      show (a1.kind.mapAll Prod.fst
            (BRho.old P (a1.joinChal r2, A) Z hK.2
              (BRho.new P (a1.joinChal r2, A) Z hK.2
                (Kind.pairAll a1.kind a2.kind hK.1 v1 v2, ρ))).1,
          Kind.sndAll a1.kind a2.kind hK.1
            (BRho.old P (a1.joinChal r2, A) Z hK.2
              (BRho.new P (a1.joinChal r2, A) Z hK.2
                (Kind.pairAll a1.kind a2.kind hK.1 v1 v2, ρ))).1,
          (BRho.old P (a1.joinChal r2, A) Z hK.2
            (BRho.new P (a1.joinChal r2, A) Z hK.2
              (Kind.pairAll a1.kind a2.kind hK.1 v1 v2, ρ))).2) = (v1, v2, ρ)
      rw [e, fst_pairAll, snd_pairAll]

def oldEquiv (N : ℕ) {s : Shape} (P : XPlan s) (hP : P.OK) (A : RoundSplits s)
    (Z : AXPlan P A) (hK : AXPlan.Kinds P A Z) :
    BRho N P.shape (A.recut P Z) ≃ BRho N s A :=
  ⟨BRho.old P A Z hK, BRho.new P A Z hK, new_old P A Z hK, old_new P hP A Z hK⟩

/-- Under `P.OK`, `AXPlan.Kinds`: the preimage of a set of values of a batch's verifier randomness
has the same probability. -/
theorem prBRho_old {N : ℕ} {s : Shape} (P : XPlan s) (hP : P.OK) (A : RoundSplits s) (Z : AXPlan P A)
    (hK : AXPlan.Kinds P A Z) (S : Set (BRho N s A)) :
    prBRho {ρ : BRho N P.shape (A.recut P Z) | BRho.old P A Z hK ρ ∈ S} = prBRho S := by
  unfold prBRho
  rw [← map_unif_equiv (oldEquiv N P hP A Z hK), pr_map]
  rfl

/-! ## 8. Honest-verifier zero knowledge for sets of slots (`BatchHonestProver.HVZK`) -/

open BatchPull (slotOut output_eq)

theorem slotOut_recut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : XPlan Q.loc.shape} (hP : P.OK)
    {Z : AXPlan P Q.ann} (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) (w : Wt)
    (ox : Option X) (ρ : Rho P.shape) (c : H.Coin0 × H.Coin) :
    slotOut (H.recut P Z hK) w ox ρ c = (slotOut H w ox (Rho.old P ρ) c).map (DView.recut P) := by
  classical
  cases ox with
  | none => rfl
  | some xj =>
    by_cases h : Rho.old P ρ ∈ H.one.withheld w xj
    · have e1 : slotOut (H.recut P Z hK) w (some xj) ρ c = none :=
        if_pos ((mem_one_withheld_recut H P Z hK w xj ρ).2 h)
      have e2 : slotOut H w (some xj) (Rho.old P ρ) c = none := if_pos h
      rw [e1, e2]
      rfl
    · have e1 : slotOut (H.recut P Z hK) w (some xj) ρ c =
          some ((Q.loc.recut P).dview xj (H.ext w) (((H.recut P Z hK).one.strat w xj c).run ρ).1) :=
        if_neg fun hm => h ((mem_one_withheld_recut H P Z hK w xj ρ).1 hm)
      have e2 : slotOut H w (some xj) (Rho.old P ρ) c =
          some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj c).run (Rho.old P ρ)).1) := if_neg h
      rw [e1, e2, one_strat_recut H hZ hK, InteractiveOracleProof.dview_recut hP]
      exact congrArg (fun t => some (DView.recut P (Q.loc.dview xj (H.ext w) t)))
        (Strat.run_recut P hP (H.one.strat w xj c) ρ)

theorem output_recut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {P : XPlan Q.loc.shape} (hP : P.OK)
    {Z : AXPlan P Q.ann} (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) {N : ℕ} (w : Wt)
    (x : Fin N → Option X) (ρ : BRho N P.shape (Q.ann.recut P Z)) (S : Finset (Fin N)) :
    (H.recut P Z hK).output w x ρ S =
      (H.output w x (BRho.old P Q.ann Z hK ρ) S).map fun f j => (f j).map (DView.recut P) := by
  rw [output_eq, output_eq, PMF.map_comp]
  refine congrArg (fun g => PMF.map g (unif (H.Coin0 × (Fin N → H.Coin)))) ?_
  funext c j
  show slotOut (H.recut P Z hK) w (x j) (ρ.slot j.1) (c.1, c.2 j) =
    (slotOut H w (x j) ((BRho.old P Q.ann Z hK ρ).slot j.1) (c.1, c.2 j)).map (DView.recut P)
  rw [slotOut_recut H hP hZ hK, slot_old]
  rfl

/-! ## 9. The pattern `RoundSplits.Fmt` -/

theorem fmtFrom_recut {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z → AXPlan.Kinds P A Z →
      ∀ ph : FPhase,
        RoundSplits.FmtFrom s A ph → AXPlan.Fit P A Z ph → RoundSplits.FmtFrom P.shape (A.recut P Z) ph := by
  induction P with
  | nil => intro _ _ _ _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨a, A⟩ Z hZ hK ph h hF
      obtain ⟨h1, h2⟩ := (fmtFrom_cons a A ph).1 h
      exact (fmtFrom_cons a (RoundSplits.recut P A Z) ph).2 ⟨h1, ih A Z hZ hK _ h2 hF⟩
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hZ hK ph h hF
      obtain ⟨h1, h2⟩ := (fmtFrom_cons a A ph).1 h
      obtain ⟨t1, t2, t3⟩ :=
        fit_table b.kind a.kind ph (noShared_cut hZ.1) (noSlot_cut hZ.1) h1 hF.1
      refine (fmtFrom_cons b.ann1 (RoundSplits.recut P (b.ann2, A) Z) ph).2
        ⟨t1, ih (b.ann2, A) Z hZ.2 hK _ ?_ hF.2⟩
      exact (fmtFrom_cons b.ann2 A _).2
        ⟨t2, by rw [show FPhase.after b.ann2.kind _ = FPhase.after a.kind ph from t3]; exact h2⟩
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ph h hF
      obtain ⟨h1, h'⟩ := (fmtFrom_cons a1 (show RoundSplits (r2 :: _) from (a2, A)) ph).1 h
      obtain ⟨h2, h3⟩ := (fmtFrom_cons a2 A _).1 h'
      obtain ⟨t1, t2⟩ := fitMsg_table a1.kind a2.kind ph noShared_msg noSlot_msg h1 h2 hF.1
      exact ih (a1.joinMsg a2, A) Z hZ hK ph ((fmtFrom_cons (a1.joinMsg a2) A ph).2 ⟨t1, by rw [show FPhase.after (a1.joinMsg a2).kind ph = FPhase.after a2.kind ph from rfl, ← t2]; exact h3⟩) hF.2
  | chal r1 r2 np P ih =>
      rintro ⟨a1, a2, A⟩ Z hZ hK ph h hF
      obtain ⟨h1, h'⟩ := (fmtFrom_cons a1 (show RoundSplits (r2 :: _) from (a2, A)) ph).1 h
      obtain ⟨-, h3⟩ := (fmtFrom_cons a2 A _).1 h'
      rw [hK.1, after_after] at h3
      exact ih (a1.joinChal r2, A) Z hZ hK.2 ph ((fmtFrom_cons (a1.joinChal r2) A ph).2 ⟨h1, h3⟩) hF

end BatchRecut

section Named
variable {X : Type} {E : ExtSpec} {Wt : Type}

/-- The simulator for sets of slots of the new protocol, as a term. -/
def simRecutB {Q : BatchInteractiveOracleProof X E} (P : XPlan Q.loc.shape)
    (Z : AXPlan P Q.ann) {N : ℕ}
    (Sim : (S : Finset (Fin N)) → (S → X) → (S → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (S → Option (DView Q.loc)))
    (S : Finset (Fin N)) (xs : S → X)
    (ρs : S → Rho (Q.recut P Z).loc.shape) (a : E.Pos → Option E.Sym) :
    PMF (S → Option (DView (Q.recut P Z).loc)) :=
  (Sim S xs (fun j => Rho.old P (ρs j)) a).map fun f j => (f j).map (DView.recut P)

/-- Under `P.OK`, `AXPlan.OK`, `AXPlan.Kinds`: if `Sim` is exact outside a set of probability at
most z, so is `simRecutB`. -/
theorem simRecutB_good {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} {P : XPlan Q.loc.shape}
    {Z : AXPlan P Q.ann} (hP : P.OK) (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z)
    (Sim : (S : Finset (Fin N)) → (S → X) → (S → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (S → Option (DView Q.loc)))
    (w : Wt) (x : Fin N → Option X) (S : Finset (Fin N)) (xs : S → X) {z : ℝ≥0∞}
    (h : prBRho {ρ | H.output w x ρ S ≠
          Sim S xs (fun j => ρ.slot j.1) (Q.extAnsJ S xs (fun j => ρ.slot j.1) (H.ext w))} ≤ z) :
    prBRho {ρ | (H.recut P Z hK).output w x ρ S ≠
          simRecutB P Z Sim S xs (fun j => ρ.slot j.1)
            ((Q.recut P Z).extAnsJ S xs (fun j => ρ.slot j.1) ((H.recut P Z hK).ext w))} ≤ z := by
  refine le_trans (le_trans (pr_mono _ ?_) (le_of_eq (BatchRecut.prBRho_old P hP Q.ann Z hK _))) h
  intro ρ hρ heq
  apply hρ
  rw [BatchRecut.output_recut H hP hZ hK, heq]
  have e : (fun j : S => (BRho.old P Q.ann Z hK ρ).slot j.1) =
      fun j : S => Rho.old P (ρ.slot j.1) :=
    funext fun j => BatchRecut.slot_old j.1 P Q.ann Z hK ρ
  rw [e]
  rfl

theorem BatchHonestProver.HVZK.recut {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop}
    {z : ℝ≥0∞} (h : H.HVZK N valid z) {P : XPlan Q.loc.shape} {Z : AXPlan P Q.ann} (hP : P.OK)
    (hZ : AXPlan.OK P Q.ann Z) (hK : AXPlan.Kinds P Q.ann Z) :
    (H.recut P Z hK).HVZK N valid z :=
  let ⟨Sim, hS⟩ := h
  ⟨simRecutB P Z Sim,
    fun w x hv S xs hxs => simRecutB_good hP hZ hK Sim w x S xs (hS w x hv S xs hxs)⟩

end Named

/-! ## 10. The statements -/


theorem recutFmtB : Spec.recutFmtB := fun _ _ Q P Z =>
  ⟨fun hZ hK h hF => BatchRecut.fmtFrom_recut P Q.ann Z hZ hK .first h hF,
    fun hK => BatchRecut.extShared_recut P Z hK⟩

open BatchRecut in
/-- `BatchProtocol.Props` except soundness is preserved, with the same numbers, under the hypotheses of
`Spec.recutPropsB`. -/
theorem recutPropsB : Spec.recutPropsB := by
  intro I X L Ryes Rno M XT XL XB ZB hK εs' hT hL hB hZ h hS
  exact
    { sub := h.sub
      wired := ⟨h.wired.dec_enc, h.wired.extT, h.wired.extL, h.wired.extB⟩
      sound := hS
      reads :=
        ⟨fun x ρ => h.reads.cntT x (Rho.old XT ρ),
          fun x ρ => h.reads.cntLp x (Rho.old XL ρ),
          fun x ρ => h.reads.cntLc x (Rho.old XL ρ),
          readsAtMost_recut XB ZB hK h.reads.cntB,
          h.reads.hidE⟩
      hidden := ⟨h.hidden.hidT.recut hT, h.hidden.hidL.recut hL, h.hidden.hidB.recut hB hZ hK⟩
      complete :=
        ⟨h.complete.accT.recut hT,
          h.complete.accL.recut hL,
          acc_recut h.complete.accB hB hZ hK,
          fun w x => (le_of_eq (L.honestOfflineProver.prRho_withheld_recut hT w x)).trans (h.complete.prT w x),
          fun w x => (le_of_eq (L.honestLinkProver.prRho_withheld_recut hL w x)).trans (h.complete.prL w x),
          fun w x hv =>
            (le_of_eq (prRho_one_withheld_recut L.honestOnlineBatchProver hB ZB hK w x)).trans (h.complete.prB w x hv)⟩
      localT := h.localT.recut hT
      localL := h.localL.recut hL
      localB := h.localB.recut hB
      cohB := coherent_recut XB hB L.onlineBatch.ann ZB hZ h.cohB
      pointT := h.pointT.map (Shape.IsPoint.recut XT hT)
      pointL := h.pointL.map (Shape.IsPoint.recut XL hL)
      pointB := h.pointB.map (Shape.IsPoint.recut XB hB) }

/-- `BatchProtocol.SoundAt` is preserved, with the lists `Err.recut`, if 0 < maxBatchSize, the list of Batch satisfies
`Err.UnitZero`, and the plan for Batch `XPlan.OK`, `AXPlan.OK`, `AXPlan.Kinds` and, at `late`,
`AXPlan.Late`. -/
theorem BatchProtocol.SoundAt.recut {I X : Type} {L : BatchProtocol I X} {Rno : I → X → Prop} {εT : Err L.offline.shape}
    {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape} (h : L.SoundAt Rno εT εL εB)
    {XT : XPlan L.offline.shape} {XL : XPlan L.link.shape} {XB : XPlan L.onlineBatch.loc.shape}
    {ZB : AXPlan XB L.onlineBatch.ann} (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (hB : XB.OK)
    (hZ : AXPlan.OK XB L.onlineBatch.ann ZB) (hN : 0 < L.maxBatchSize) (hU : εB.UnitZero)
    (hl : ∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) :
    (L.recut XT XL XB ZB hK).SoundAt Rno (Err.recut XT εT) (Err.recut XL εL) (Err.recut XB εB) :=
  ⟨h.sndT.recut XT, h.sndL.recut XL, BatchRecut.sndBL_recut hB hZ hK hN hl hU h.sndB⟩


end Iop
