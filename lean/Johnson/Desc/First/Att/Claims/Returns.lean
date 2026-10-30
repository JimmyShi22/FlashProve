-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Returns.lean: kind K5: where the three named runs return: the other
half of the law of Johnson/Desc/First/Att/Claims/Top.lean. Each statement is a definition of type
Prop in the namespace Spec; each theorem has that name as its type.

Main names:
  `Spec.FirstTogether`, `SecondTogether`, `KeysTogether`: at two records that agree in what is
    public (`Same`: numbers and lengths alone) a run returns at both or at neither; "first" then
    hands on one array of counts.
  `Spec.ReturnsWhere`: if the three runs return at one record, they return at every record that
    agrees with it in what is public.
  `Spec.DryGives`: where the kind's test on the plan alone says yes (claimsOk … = true,
    Johnson/Desc/First/Att/ClaimsOk.lean), there are the blank points and the blank tables of that
    test, and at every record that agrees in what is public with the blank record the three runs
    return. The tables' own tests are not covered: the two tests of tablesP on values do not carry
    over.
  `Spec.LawAtOld`: both halves at `inOld h`: under A.NC = h.S.calls.size, Same (inOld h) i0 and the
    three runs' return at i0: "first" is the written lists of claims 3, 4, 5 with the written key
    forms, "keys" is the written key forms, "second" is the written lists of claims 6, 7, 8:
    equations.
Limits: a run that always returns, with another list, fails LawAtOld. A run that never returns meets
all six statements idly: for it AllReturn is false at every record, and claimsOk, which itself runs
the runs at the blank record, is false. What bars that run is one closed fact at a real plan,
claimsOk … = true: not shown in this file or in what it imports. It bears on completeness alone.
Used of OnBytes: in FirstTogether … DryGives nothing; in LawAtOld what
Johnson/Desc/First/Att/Claims/Top.lean names.
Not claimed: that a claim holds.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SameClaims
import Johnson.Desc.First.Att.Claims.Top

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts TablesP ParC)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP PadIn)

variable {K : ℕ}

theorem gather_rel {α α' : Type} {R : α → α' → Prop} {r : W α} {r' : W α'} (h : RS K R r r') :
    OptRel (fun x x' => R x.1 x'.1) (P.Runs.gather K r) (P.Runs.gather K r') := by
  unfold P.Runs.gather
  have h0 := h #[] #[]
  have e : (r.run K).run #[] = r K #[] := rfl
  have e' : (r'.run K).run #[] = r' K #[] := rfl
  rw [e, e']
  cases h1 : r K #[] <;> cases h2 : r' K #[] <;> rw [h1, h2] at h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact h0

theorem OptRel.map {α α' β β' : Type} {R : α → α' → Prop} {Q : β → β' → Prop} {x : Option α}
    {x' : Option α'} (h : OptRel R x x') (f : α → β) (f' : α' → β')
    (hf : ∀ a a', R a a' → Q (f a) (f' a')) : OptRel Q (x.map f) (x'.map f') := by
  cases x <;> cases x'
  · trivial
  · exact h.elim
  · exact h.elim
  · exact hf _ _ h

theorem OptRel.isSome {α α' : Type} {R : α → α' → Prop} {x : Option α} {x' : Option α'}
    (h : OptRel R x x') : x.isSome = x'.isSome := by
  cases x <;> cases x'
  · rfl
  · exact h.elim
  · exact h.elim
  · rfl

namespace Spec

def FirstTogether : Prop :=
  ∀ (i i' : In) (K : ℕ), Same i i' →
    OptRel (fun x x' => JR x.2 x'.2) (P.Runs.firstRun i K) (P.Runs.firstRun i' K)

def SecondTogether : Prop :=
  ∀ (i i' : In) (K : ℕ), Same i i' → (P.Runs.secondRun i K).isSome = (P.Runs.secondRun i' K).isSome

def KeysTogether : Prop :=
  ∀ (i i' : In) (k3 : PadIn) (j j' : JoinsP), i.g = i'.g → JR j j' →
    (P.Runs.keysRun i k3 j).isSome = (P.Runs.keysRun i' k3 j').isSome

/-- The three runs return at i, at K, with the lookup's data k3. -/
def AllReturn (i : In) (K : ℕ) (k3 : PadIn) : Prop :=
  ∃ l₁ j kf l₂, P.Runs.firstRun i K = some (l₁, j) ∧ P.Runs.keysRun i k3 j = some kf ∧
    P.Runs.secondRun i K = some l₂

def ReturnsWhere : Prop :=
  ∀ (i i0 : In) (K : ℕ) (k3 : PadIn), Same i i0 → AllReturn i0 K k3 → AllReturn i K k3

/-- What the lookup's kind would hand in, all zeros: the very record inside dryOk. -/
def blankLook (g : P.Geo) (planesOk : Bool) (nzx : ℕ) : P.LookIn :=
  { zx := P.zeros nzx, planesOk := planesOk, phiB0 := P.zeros (2 ^ g.lmb), phiB1 := P.zeros (2 ^ g.lmb), phiP := P.zeros (2 ^ g.lmb) }

/-- The blank record at which dryOk runs the three runs. -/
def blankIn (c : ParC) (p0 : Pts) (t0 : TablesP) : In :=
  { g := c.geo, p := p0, t := t0, zk := P.blankZk c.geo, iU3 := c.iU3 }

def DryGives : Prop :=
  ∀ (c : ParC) (K : ℕ) (k3 : PadIn) (planesOk : Bool) (nzx : ℕ),
    P.claimsOk c K k3 planesOk nzx = true →
      ∃ (p0 : Pts) (t0 : TablesP), P.blankPts c.geo = some p0 ∧
        P.tablesP c.geo c.mats c.nW (blankLook c.geo planesOk nzx) p0 = some t0 ∧
        ∀ i : In, Same i (blankIn c p0 t0) → AllReturn i K k3

def LawAtOld : Prop :=
  ∀ (A : Attention.Plan) (h : Attention.Heard) (i0 : In) (K : ℕ) (k3 : PadIn),
    A.NC = h.S.calls.size → Same (inOld h) i0 → AllReturn i0 K k3 →
      P.Runs.firstRun (inOld h) K =
          some (Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K), jP (Fo.attJoinsT A h)) ∧
        P.Runs.keysRun (inOld h) k3 (jP (Fo.attJoinsT A h)) = some (Fo.attJoinsT A h).kf ∧
        P.Runs.secondRun (inOld h) K = some (Fo.claim6T h K ++ (Fo.claim7T h K ++ Fo.claim8T h K))

end Spec

theorem first_together : Spec.FirstTogether := by
  intro i i' K H
  unfold P.Runs.firstRun
  refine OptRel.map (R := fun x x' => JR x.1 x'.1) (gather_rel ?_) _ _ fun _ _ h => h
  rw [H.g]
  exact RS.bind (rs_claim3 H rfl) fun _ _ h3 => RS.bind (rs_claim4 H h3) fun _ _ h4 => rs_claim5 H h4

theorem second_together : Spec.SecondTogether := by
  intro i i' K H
  unfold P.Runs.secondRun
  refine OptRel.isSome (R := Any) (OptRel.map (R := fun x x' => Any x.1 x'.1) (gather_rel ?_) _ _
    fun _ _ _ => trivial)
  exact RS.bind (rs_claim6 H) fun _ _ _ => RS.bind (rs_claim7 H) fun _ _ _ => rs_claim8 H

theorem keys_together : Spec.KeysTogether := by
  intro i i' k3 j j' hg hj
  have key : ∀ (i i' : In) (j j' : JoinsP), i.g = i'.g → JR j j' →
      (P.Runs.keysRun i k3 j).isSome = true → (P.Runs.keysRun i' k3 j').isSome = true := by
    intro i i' j j' hg hj h
    obtain ⟨kf, hk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨_, h1, h2, h3⟩ := (keys_iff i k3 j kf).1 hk
    rw [hg] at h2 h3
    rw [show j.joined = j'.joined from hj] at h1
    exact Option.isSome_iff_exists.2 ⟨j'.kf, (keys_iff i' k3 j' j'.kf).2 ⟨rfl, h1, h2, h3⟩⟩
  exact Bool.eq_iff_iff.2 ⟨key i i' j j' hg hj, key i' i j' j hg.symm hj.symm⟩

theorem returns_where : Spec.ReturnsWhere := by
  intro i i0 K k3 H ⟨l₁, j, kf, l₂, h1, hk, h2⟩
  have r1 := first_together i i0 K H
  rw [h1] at r1
  cases e1 : P.Runs.firstRun i K with
  | none => rw [e1] at r1; exact r1.elim
  | some x =>
    rw [e1] at r1
    have rk := keys_together i i0 k3 x.2 j H.g r1
    rw [hk] at rk
    obtain ⟨kf', hk'⟩ := Option.isSome_iff_exists.1 rk
    have r2 := second_together i i0 K H
    rw [h2] at r2
    obtain ⟨l₂', h2'⟩ := Option.isSome_iff_exists.1 r2
    exact ⟨x.1, x.2, kf', l₂', e1, hk', h2'⟩

theorem dry_gives : Spec.DryGives := by
  intro c K k3 planesOk nzx h
  unfold P.claimsOk at h
  rw [Bool.and_eq_true] at h
  have hd := h.2
  unfold P.dryOk at hd
  dsimp only at hd
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hu
  obtain ⟨p0, hp, t0, ht, f, hf, kf, hk, l₂, h2, _⟩ := hu
  exact ⟨p0, t0, hp, ht, fun i H => returns_where i _ K k3 H ⟨f.1, f.2, kf, l₂, hf, hk, h2⟩⟩

theorem law_at_old : Spec.LawAtOld := by
  intro A h i0 K k3 hN H h0
  obtain ⟨l₁, j, kf, l₂, h1, hk, h2⟩ := returns_where _ _ K k3 H h0
  obtain ⟨e1, ej⟩ := first_is_at A h K l₁ j hN h1
  have ek := keys_is _ _ _ _ hk
  have e2 := second_is h K l₂ h2
  subst e1 ej e2 ek
  exact ⟨h1, hk, h2⟩

end K5Law
