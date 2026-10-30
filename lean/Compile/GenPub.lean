-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GenPub.lean: a part of every proof that the committer already knows may also be put into the
verification key, from which the verifier then reads it. Generic in the scheme; completeness and
index binding only.

Given a scheme A = (C, P, V) of ZKCP/Gen.lean and u = (pub, re):
    pub ivk isk    what the committer adds to the verification key: a function of its own output
                   (ivk, isk);
    re ℓ π         the proof π with some of its fields overwritten from the published datum ℓ;
`pubArg A u` is the scheme (C', P, V'): C' runs C and outputs ((ivk, pub ivk isk), isk); P is
unchanged; V' ((ivk, ℓ), x, π) = V (ivk, x, re ℓ π). So V' never uses the fields of π that re
overwrites: it reads them from its key. (Dropping these fields from the proof is then a map on
proofs: Compile/GenMap.lean.)

  `completeness`   If on every proof π that P (isk, ·) can output, on every path, V runs the same
                   program on re (pub ivk isk) π as on π (`Pub.Honest`), the two experiments of
                   completeness are one program (`completenessExp_pub`): the same error.
  `binding`        Index binding transfers from A to `pubArg A u` with the same bound at the same
                   numbers of queries, and with the extractor `pubE u E`.

Limits: nothing on privacy: pub could be all of isk. Privacy of a scheme with a published datum has
to be proved for the concrete scheme. An adversarial committer's ℓ is arbitrary, as an adversarial
prover's fields were. Nothing says that V' reads all of ℓ. The plan follows Compile/GenMap.lean.
-/
import Compile.GenMap

noncomputable section

namespace Compile.GenPub
open ZKCP.Gen Rom Prob Compile.GenMap
open scoped ENNReal

variable {S : OSpec} {I X W PP IVK ISK Pf Λ : Type}

/-- what is published (`pub`), and how a proof is read with it (`re`) -/
structure Pub (IVK ISK Pf Λ : Type) where
  pub : IVK → ISK → Λ
  re : Λ → Pf → Pf

/-- The scheme with the datum in the verification key. -/
def pubArg (A : Arg S I X W IVK ISK Pf) (u : Pub IVK ISK Pf Λ) : Arg S I X W (IVK × Λ) ISK Pf where
  C := fun i => (A.C i).bind fun o => .pure ((o.1, u.pub o.1 o.2), o.2)
  P := A.P
  V := fun v x π => A.V v.1 x (u.re v.2 π)

/-! ## Outputs on all paths -/

/-- every output of the algorithm, on every path of its tree (whatever the oracles answer and the
coins show), has the property Q -/
def AllOut {α : Type} (Q : α → Prop) : OComp S α → Prop
  | .pure a => Q a
  | .query _ _ k => ∀ r, AllOut Q (k r)
  | .sample _ k => ∀ r, AllOut Q (k r)

theorem AllOut.bind {α β : Type} {c : OComp S α} {g : α → OComp S β} {Q' : α → Prop} {Q : β → Prop}
    (h : AllOut Q' c) (hg : ∀ a, Q' a → AllOut Q (g a)) : AllOut Q (c.bind g) := by
  induction c with
  | pure a => exact hg a h
  | query o q k ih => exact fun r => ih r (h r)
  | sample n k ih => exact fun r => ih r (h r)

theorem allOut_true {α : Type} (c : OComp S α) : AllOut (fun _ => True) c := by
  induction c with
  | pure a => trivial
  | query o q k ih => exact fun r => ih r
  | sample n k ih => exact fun r => ih r

theorem AllOut.mono {α : Type} {c : OComp S α} {Q Q' : α → Prop}
    (h : AllOut Q c) (hq : ∀ a, Q a → Q' a) : AllOut Q' c := by
  induction c with
  | pure a => exact hq a h
  | query o q k ih => exact fun r => ih r (h r)
  | sample n k ih => exact fun r => ih r (h r)

/-- two continuations that agree on all outputs give the same program -/
theorem bind_congr_allOut {α β : Type} {c : OComp S α}
    {g g' : α → OComp S β} (h : AllOut (fun a => g a = g' a) c) : c.bind g = c.bind g' := by
  induction c with
  | pure a => exact h
  | query o q k ih => exact congrArg (OComp.query o q) (funext fun r => ih r (h r))
  | sample n k ih => exact congrArg (OComp.sample n) (funext fun r => ih r (h r))

/-! ## Completeness -/

/-- To V the honest prover's proofs already hold what is published: on every path of P, for every
key, V is the same program on the proof as it is and on the proof overwritten from the published
datum. -/
def Pub.Honest (u : Pub IVK ISK Pf Λ) (A : Arg S I X W IVK ISK Pf) : Prop :=
  ∀ (v : IVK) (k : ISK) (b : List (X × W)), AllOut
    (fun πs : Slots Pf b => ∀ π ∈ πs.val, ∀ x, A.V v x (u.re (u.pub v k) π) = A.V v x π) (A.P k b)

variable {A : Arg S I X W IVK ISK Pf} {u : Pub IVK ISK Pf Λ}

theorem verifyAll_pub (v : IVK) (ℓ : Λ) :
    ∀ l : List (X × Pf), (∀ e ∈ l, A.V v e.1 (u.re ℓ e.2) = A.V v e.1 e.2) →
      verifyAll (pubArg A u) (v, ℓ) l = verifyAll A v l
  | [], _ => rfl
  | (x, π) :: t, h => by
      show (A.V v x (u.re ℓ π)).bind
          (fun c => (verifyAll (pubArg A u) (v, ℓ) t).bind fun cs => .pure (c && cs)) =
        (A.V v x π).bind fun c => (verifyAll A v t).bind fun cs => .pure (c && cs)
      rw [verifyAll_pub v ℓ t fun e he => h e (List.mem_cons_of_mem _ he),
        h (x, π) List.mem_cons_self]

theorem sessionExp_pub (h : u.Honest A) (v : IVK) (k : ISK) (b : List (X × W)) :
    sessionExp (pubArg A u) (v, u.pub v k) k b = sessionExp A v k b := by
  show (A.P k b).bind
      (fun πs => verifyAll (pubArg A u) (v, u.pub v k) ((b.map Prod.fst).zip πs.val)) =
    (A.P k b).bind fun πs => verifyAll A v ((b.map Prod.fst).zip πs.val)
  refine bind_congr_allOut ((h v k b).mono fun πs hπ => ?_)
  exact verifyAll_pub v _ _ fun e he => hπ e.2 (List.of_mem_zip he).2 e.1

/-- Under `Honest`: the two experiments of completeness are one program. -/
theorem completenessExp_pub (h : u.Honest A) (i : I) (b : List (X × W)) :
    completenessExp (pubArg A u) i b = completenessExp A i b := by
  show ((A.C i).bind fun o => OComp.pure ((o.1, u.pub o.1 o.2), o.2)).bind
      (fun o => sessionExp (pubArg A u) o.1 o.2 b) =
    (A.C i).bind fun o => sessionExp A o.1 o.2 b
  rw [OComp.bind_assoc]
  exact congrArg _ (funext fun o => sessionExp_pub h o.1 o.2 b)

theorem completeness (h : u.Honest A) (R : RelPair I X W PP) {B : ℕ}
    {α : ℝ≥0∞} (hc : HasCompletenessError R A B α) :
    HasCompletenessError R (pubArg A u) B α :=
  fun i b hb => by
    rw [completenessExp_pub h]
    exact hc i b hb

/-! ## Index binding -/

/-- the extractor: E_i reads ivk and the committer's trace and ignores the published datum; E_w
reads the proof as V' does -/
def pubE (u : Pub IVK ISK Pf Λ) (E : Extractor S I X W IVK Pf) :
    Extractor S I X W (IVK × Λ) Pf where
  Ei := fun v tr => E.Ei v.1 tr
  Ew := fun v tr x π tr' => E.Ew v.1 tr x (u.re v.2 π) tr'

/-- The experiment of index binding against the scheme with the datum in the key is the experiment
against A: the adversarial committer passes the datum to its prover, who applies re to its proof. -/
theorem bindingExp_pub (A : Arg S I X W IVK ISK Pf) (u : Pub IVK ISK Pf Λ)
    (E : Extractor S I X W IVK Pf) {St : Type}
    (Ct : OComp S ((IVK × Λ) × St)) (Pt : St → OComp S (X × Pf)) :
    bindingExp A E (Ct.bind fun o => .pure (o.1.1, (o.1.2, o.2)))
        (fun st : Λ × St => (Pt st.2).bind fun o => .pure (o.1, u.re st.1 o.2)) =
      bindingExp (pubArg A u) (pubE u E) Ct Pt := by
  show ((Ct.bind fun o => OComp.pure (o.1.1, (o.1.2, o.2))).withTrace).bind (fun a =>
      (((Pt a.1.2.2).bind fun o => OComp.pure (o.1, u.re a.1.2.1 o.2)).withTrace).bind fun b =>
      (A.V a.1.1 b.1.1 b.1.2).bind fun c =>
        .pure (⟨c, E.Ei a.1.1 a.2, b.1.1, E.Ew a.1.1 a.2 b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)) =
    Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
      (A.V a.1.1.1 b.1.1 (u.re a.1.1.2 b.1.2)).bind fun c =>
        .pure (⟨c, E.Ei a.1.1.1 a.2, b.1.1,
          E.Ew a.1.1.1 a.2 b.1.1 (u.re a.1.1.2 b.1.2) b.2⟩ : BindingOutcome I X W)
  rw [withTrace_bind, OComp.bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  show (((Pt a.1.2).bind fun o => OComp.pure (o.1, u.re a.1.1.2 o.2)).withTrace).bind
      (fun b =>
        (A.V a.1.1.1 b.1.1 b.1.2).bind fun c =>
          .pure (⟨c, E.Ei a.1.1.1 (a.2 ++ []), b.1.1,
              E.Ew a.1.1.1 (a.2 ++ []) b.1.1 b.1.2 b.2⟩ : BindingOutcome I X W)) = _
  rw [withTrace_bind, OComp.bind_assoc, List.append_nil]
  refine congrArg _ (funext fun b => ?_)
  show (A.V a.1.1.1 b.1.1 (u.re a.1.1.2 b.1.2)).bind (fun c =>
      .pure (⟨c, E.Ei a.1.1.1 a.2, b.1.1,
          E.Ew a.1.1.1 a.2 b.1.1 (u.re a.1.1.2 b.1.2) (b.2 ++ [])⟩ : BindingOutcome I X W)) = _
  rw [List.append_nil]

/-- Index binding transfers to the scheme with the datum in the key: the same bound at the same
numbers of queries. -/
theorem binding (u : Pub IVK ISK Pf Λ) (R : RelPair I X W PP) {E : Extractor S I X W IVK Pf}
    {ε : ℕ → ℕ → ℝ≥0∞} (hb : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R (pubArg A u) (pubE u E) ε :=
  fun tC tP St Ct Pt hC hP => by
    rw [← bindingExp_pub]
    exact hb tC tP (Λ × St) _ _
      ((hC.bind (g := fun o => OComp.pure (o.1.1, (o.1.2, o.2))) (t := 0) fun _ => trivial).mono
        (Nat.add_zero _).le) fun st =>
          ((hP st.2).bind (g := fun o => OComp.pure (o.1, u.re st.1 o.2))
              (t := 0) fun _ => trivial).mono
            (Nat.add_zero _).le

end Compile.GenPub
