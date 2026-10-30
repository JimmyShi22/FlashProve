-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/NzSub.lean: the calls of a sub-proof's engine, the routines of the masked
sumcheck and attention's two kinds of sumcheck keep the property `NzCtx`.

`NzCtx` (OnBytes/Tie/Pv/Psc/Run/NzCtx.lean) is the one premise on a context from which the reading
of every masked sumcheck's beta is not 0. OnBytes/Tie/Pv/Psc/Run/NzRounds.lean shows that the
routines on the channel keep it and names the ways in which routines of a sub-proof are made. Here
these are applied, call by call.

Main names:
  `keeps_test`: a condition on values.
  `keepsS_must`, `keepsS_test`, `keepsS_get`, `keepsS_read`, `keepsS_readSum`, `keepsS_answer`,
    `keepsS_answerNotZero`, `keepsS_point`, `keepsS_batch`, `keepsS_batchOpen`, `keepsS_batchRows`,
    `keepsS_empty`, `keepsS_trits`, `keepsS_claimsIn`: the calls of OnBytes/Model/Hide.lean that
    touch the channel. Its other calls are made by SubM.ask, SubM.take or SubM.change alone:
    `keepsS_ask`, `keepsS_take`, `keepsS_change` serve as they are.
  `keepsS_pscBegin`, `keepsS_pscRound`, `keepsS_roundIn`, `keepsS_pscEnds`, `keepsS_pscRow`: the
    routines of OnBytes/Model/Psc.lean.
  `keepsS_foldlM`: a fold of steps that keep it.
  `keepsS_sc3In`, `keepsS_sc3Row`, `keepsS_scdIn`, `keepsS_scdRow`, `keepsS_keyAtIndexIn`:
    attention's two kinds of sumcheck.

Limits: as in OnBytes/Tie/Pv/Psc/Run/NzCtx.lean. Attention's other routines are not treated here.
-/
import OnBytes.Model.AttentionDivide
import OnBytes.Tie.Pv.Psc.Run.NzRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Attention

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem keeps_test (b : Bool) : Keeps ρ (Blk.test b) := fun c _ c' h y => by
  obtain ⟨_, rfl⟩ := (Blk.yields_test b c c' h.1).1 y
  exact h

theorem keepsS_must (b : Bool) : KeepsS ρ (SubM.must b) := keepsS_lift ρ _ (keeps_must ρ b)
theorem keepsS_test (b : Bool) : KeepsS ρ (SubM.test b) := keepsS_lift ρ _ (keeps_test ρ b)
theorem keepsS_get {α : Type} (x : Option α) : KeepsS ρ (SubM.get x) :=
  keepsS_lift ρ _ (keeps_get ρ x)
theorem keepsS_read (n : Nat) : KeepsS ρ (SubM.read n) := keepsS_lift ρ _ (keeps_trRead ρ n)
theorem keepsS_readSum : KeepsS ρ SubM.readSum := keepsS_lift ρ _ (keeps_trSum ρ)
theorem keepsS_answer (r : RoundName) : KeepsS ρ (SubM.answer r) :=
  keepsS_lift ρ _ (keeps_trAnswer ρ r)
theorem keepsS_answerNotZero (r : RoundName) : KeepsS ρ (SubM.answerNotZero r) :=
  keepsS_lift ρ _ (keeps_trAnswerNotZero ρ r)
theorem keepsS_point (r : RoundName) (n : Nat) : KeepsS ρ (SubM.point r n) :=
  keepsS_lift ρ _ (keeps_trPoint ρ r n)
theorem keepsS_batch (rows : Nat) : KeepsS ρ (SubM.batch rows) :=
  keepsS_lift ρ _ (keeps_trBatch ρ rows)
theorem keepsS_batchOpen : KeepsS ρ SubM.batchOpen := keepsS_lift ρ _ (keeps_trBatchOpen ρ)
theorem keepsS_batchRows (rows : Nat) : KeepsS ρ (SubM.batchRows rows) :=
  keepsS_lift ρ _ (keeps_trBatchRows ρ rows)
theorem keepsS_empty (r : RoundName) : KeepsS ρ (SubM.empty r) :=
  keepsS_lift ρ _ (keeps_trEmpty ρ r)
theorem keepsS_trits (a b : Nat) : KeepsS ρ (SubM.trits a b) :=
  keepsS_lift ρ _ (keeps_trTrits ρ a b)

theorem keepsS_claimsIn (n : Nat) : KeepsS ρ (SubM.claimsIn n) :=
  keepsS_bind ρ _ _ (keepsS_read ρ n) fun _ =>
    keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
      keepsS_bind ρ _ _ (keepsS_take ρ _) fun _ =>
        keepsS_bind ρ _ _ (keepsS_change ρ _) fun _ => keepsS_pure ρ _

/-! ## The masked sumcheck -/

theorem keepsS_pscBeginAt (target : E) : KeepsS ρ (pscBeginAt target) :=
  keepsS_bind ρ _ _ (keepsS_take ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_readSum ρ) fun _ =>
      keepsS_bind ρ _ _ (keepsS_answer ρ _) fun _ => keepsS_pure ρ _

theorem keepsS_pscBegin (C : Aff) : KeepsS ρ (pscBegin C) :=
  keepsS_bind ρ _ _ (keepsS_ask ρ _) fun x =>
    keepsS_bind ρ _ _ (keepsS_pscBeginAt ρ x) fun _ => keepsS_pure ρ _

theorem keepsS_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Blk E) (hd : Keeps ρ draw) :
    KeepsS ρ (pscRound p w draw) :=
  keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_read ρ _) fun _ =>
      keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
        keepsS_bind ρ _ _ (keepsS_lift ρ _ hd) fun _ =>
          keepsS_bind ρ _ _ (keepsS_take ρ _) fun _ => keepsS_pure ρ _

theorem keepsS_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    KeepsS ρ (roundIn form p z degree) :=
  keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_get ρ _) fun w => keepsS_pscRound ρ p w _ (keeps_trAnswer ρ _)

theorem keepsS_pscEnds (p : Psc) (degreeInY n : Nat) : KeepsS ρ (pscEnds p degreeInY n) :=
  keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_pscRound ρ p _ _ (keeps_trAnswerNotZero ρ _)) fun ⟨_, _⟩ =>
      keepsS_bind ρ _ _ (keepsS_read ρ n) fun _ =>
        keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
          keepsS_bind ρ _ _ (keepsS_empty ρ _) fun _ =>
            keepsS_bind ρ _ _ (keepsS_take ρ _) fun _ =>
              keepsS_bind ρ _ _ (keepsS_change ρ _) fun _ => keepsS_pure ρ _

theorem keepsS_pscRow (p : Psc) (S0 : E) (kept : Aff) : KeepsS ρ (pscRow p S0 kept) :=
  keepsS_bind ρ _ _ (keepsS_must ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_change ρ _) fun _ => keepsS_pure ρ _

/-! ## Attention's two kinds of sumcheck -/

theorem keepsS_foldlM {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, KeepsS ρ (f b a)) :
    ∀ (l : List α) (b : β), KeepsS ρ (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact keepsS_pure ρ b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact keepsS_bind ρ _ _ (hf b a) fun b' => keepsS_foldlM f hf l b'

theorem keepsS_sc3Rounds : ∀ (n : Nat) (p : Psc) (r : Array E), KeepsS ρ (sc3Rounds n p r)
  | 0, p, r => keepsS_pure ρ (r, p)
  | n + 1, p, r => keepsS_bind ρ _ _ (keepsS_roundIn ρ _ p _ _) fun x =>
    keepsS_sc3Rounds n x.2 (r.push x.1)

theorem keepsS_scdRounds : ∀ (ds : List Nat) (p : Psc) (r : Array E), KeepsS ρ (scdRounds ds p r)
  | [], p, r => keepsS_pure ρ (r, p)
  | d :: ds, p, r => keepsS_bind ρ _ _ (keepsS_roundIn ρ _ p _ d) fun x =>
    keepsS_scdRounds ds x.2 (r.push x.1)

theorem keepsS_sc3In (nv nb : Nat) (C : Aff) : KeepsS ρ (sc3In nv nb C) :=
  keepsS_bind ρ _ _ (keepsS_pscBegin ρ C) fun p0 =>
    keepsS_bind ρ _ _ (keepsS_sc3Rounds ρ nv p0 #[]) fun x =>
      keepsS_bind ρ _ _ (keepsS_pscEnds ρ x.2 2 (2 * nb)) fun _ => keepsS_pure ρ _

theorem keepsS_scdIn (ds : List Nat) (dY n : Nat) (C : Aff) : KeepsS ρ (scdIn ds dY n C) :=
  keepsS_bind ρ _ _ (keepsS_pscBegin ρ C) fun p0 =>
    keepsS_bind ρ _ _ (keepsS_scdRounds ρ ds p0 #[]) fun x =>
      keepsS_bind ρ _ _ (keepsS_pscEnds ρ x.2 dY n) fun _ => keepsS_pure ρ _

theorem keepsS_sc3Shown (o : Sc3) (W : Array E) : ∀ (n b : Nat) (s : E),
    KeepsS ρ (sc3Shown o W n b s)
  | 0, _, s => keepsS_pure ρ s
  | n + 1, b, _ => keepsS_bind ρ _ _ (keepsS_ask ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_ask ρ _) fun _ => keepsS_sc3Shown o W n (b + 1) _

theorem keepsS_sc3Row (o : Sc3) (W : Array E) : KeepsS ρ (sc3Row o W) :=
  keepsS_bind ρ _ _ (keepsS_lift ρ _ (keeps_mustAs ρ _ _)) fun _ =>
    keepsS_bind ρ _ _ (keepsS_sc3Shown ρ o W _ _ _) fun s0 =>
      keepsS_bind ρ _ _ (keepsS_pscRow ρ o.p s0 {}) fun _ => keepsS_pure ρ _

theorem keepsS_scdRow (o : Scd) (s0 : E) : KeepsS ρ (scdRow o s0) :=
  keepsS_bind ρ _ _ (keepsS_pscRow ρ o.p s0 {}) fun _ => keepsS_pure ρ _

theorem keepsS_keyTerm (S : Shape) (sKC : Nat) (pj : Array E) (w : E) (b : Nat) :
    KeepsS ρ (keyTerm S sKC pj w b) :=
  keepsS_bind ρ _ _ (keepsS_ask ρ _) fun _ =>
    keepsS_foldlM ρ _ (fun _ _ => keepsS_bind ρ _ _ (keepsS_ask ρ _) fun _ => keepsS_pure ρ _) _ _

theorem keepsS_keyAtIndexIn (S : Shape) (scF : Sc3) : KeepsS ρ (keyAtIndexIn S scF) :=
  keepsS_bind ρ _ _ (keepsS_batch ρ _) fun _ =>
    keepsS_bind ρ _ _ (keepsS_scdIn ρ _ _ _ _) fun o =>
      keepsS_bind ρ _ _
        (keepsS_foldlM ρ _
          (fun _ _ => keepsS_bind ρ _ _ (keepsS_keyTerm ρ S _ _ _ _) fun _ => keepsS_pure ρ _) _ _)
        fun _ => keepsS_scdRow ρ o _

end OnBytes.Model.Road

#print axioms OnBytes.Model.Road.keepsS_claimsIn
#print axioms OnBytes.Model.Road.keepsS_pscEnds
#print axioms OnBytes.Model.Road.keepsS_sc3In
#print axioms OnBytes.Model.Road.keepsS_sc3Row
#print axioms OnBytes.Model.Road.keepsS_keyAtIndexIn
