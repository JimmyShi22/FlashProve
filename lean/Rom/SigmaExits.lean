-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SigmaExits.lean: the three changes of oracles, for many families of oracles side by side:
  1. splitting answers in two parts (Rom/SpecCut.lean);
  2. expanding long answers from a state, under an adaptive rule for which hash blocks are queried
     (Rom/StateFirstLazy.lean);
  3. the step to one hash function (Rom/Family.lean).
Generic.

Rom/SigmaSpec.lean puts families S t side by side (`OSpec.sigma`, "the whole" in the comments). The
three steps are functions on algorithms over any family, from data on that family. Here the data of
the whole are made from the data at each t (`cutSigma`, `needCutSigma`, `linksSigma`, `needASigma`),
and each step is shown to commute with "an algorithm at t, seen in the whole" (`OComp.inT`,
Rom/SigmaSpec.lean; `OComp.inT1`, `OComp.inT2`): equalities of programs. `cut_inT` and
`stateFirstA_inT1` hold for every algorithm at t; `overOne_inT2` for an algorithm that queries only
where the query encoding of the whole and that at t answer by the same program (`OComp.AsksIn`,
`SameAns`). The whole has one added oracle dr of expansion queries from a state (`stSpec`,
Rom/StateFirst.lean), for all t.

Notation:
  `C`: for each t and each oracle o of S t, an `OCut` (Rom/SpecCut.lean): how an oracle with answers
      in R is treated
  `NeedCut`: a rule: after the first part a of the answer at q, is the second part queried?
      (Rom/SpecCut.lean)
  `C2`: for each t and each oracle x of the split family at t, a `Link lam` (Rom/StateFirst.lean):
      how an oracle with answers in R is treated; its cases: `plain`, `chain K e`
  `NeedA`: a rule that says which hash blocks are queried (Rom/NeedA.lean)
  `lam`: a natural number; `Dg lam` is `Fin lam → Bool`: a hash block (Rom/NeedA.lean)
  query encoding: `OracleCoding`, with the field `code` (Rom/Family.lean)
  C, P, V under "Limits": the fields of a scheme, `Gen.Arg` (ZKCP/Gen.lean): ARG = (C, P, V)

Limits: nothing on schemes, probabilities or bounds. No query encoding of the whole is given. An
algorithm at t that queries where the encodings differ (C and P of a scheme that derives coins
through an auxiliary oracle) becomes two different algorithms over the hash function: where these
equalities are used for a scheme, they are used for V only. (`needCutSigma` and `cut_inT` are for
any rule; in the larger library the use is at the rule "always" (`needCutSigma_true`); the file that
uses them is not in this library.) No other file of this library uses any of these equalities.
-/
import Rom.SigmaSpec
import Rom.SpecCut
import Rom.StateFirstLazy

set_option autoImplicit false

namespace Rom
variable {T : Type} [DecidableEq T] {S : T → OSpec} (S₀ : OSpec) {α β : Type}

/-! ## Splitting answers in two parts -/

section Cut
variable (C : ∀ t o, OCut ((S t).Rng o))

/-- the oracle (t, o) is split as o at t; an oracle of S₀ is not split -/
def cutSigma : ∀ o : (OSpec.sigma S S₀).ι, OCut ((OSpec.sigma S S₀).Rng o)
  | .inl o => C o.1 o.2
  | .inr _ => .whole

/-- the rule of the whole for the second parts -/
def needCutSigma (need : ∀ t, NeedCut (C t)) : NeedCut (cutSigma S₀ C)
  | .inl o => need o.1 o.2
  | .inr _ => fun _ _ => true

theorem needCutSigma_true : needCutSigma S₀ C (fun _ _ _ _ => true) = fun _ _ _ => true := by
  funext o
  cases o <;> rfl

/-- an algorithm over the split family at t (`cutSpec (S t) (C t)`), seen over the split family of
the whole -/
def OComp.inT1 (t : T) :
    OComp (cutSpec (S t) (C t)) α → OComp (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).inT1 t
  | .query (.inl o) q k =>
    .query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C))
      (.inl (.inl ⟨t, o⟩)) q fun r => (k r).inT1 t
  | .query (.inr o) q k =>
    .query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C))
      (.inr (.inl ⟨t, o⟩)) q fun r => (k r).inT1 t

/-- Splitting commutes: (c seen in the whole), split, is (c split at t), seen in the whole. -/
theorem cut_inT (need : ∀ t, NeedCut (C t)) (t : T) (c : OComp (S t) α) :
    (c.inT S₀ t).cut (cutSigma S₀ C) (needCutSigma S₀ C need) =
      (c.cut (C t) (need t)).inT1 S₀ C t := by
  induction c with
  | pure a => rfl
  | sample n k ih =>
      show OComp.sample n (fun r => ((k r).inT S₀ t).cut (cutSigma S₀ C) (needCutSigma S₀ C need)) =
        OComp.sample n fun r => ((k r).cut (C t) (need t)).inT1 S₀ C t
      exact congrArg _ (funext ih)
  | query o q k ih =>
      show OComp.query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C))
          (.inl (.inl ⟨t, o⟩)) q (fun a =>
            if (C t o).isWhole || !need t o q a then
              ((k ((C t o).alone a)).inT S₀ t).cut (cutSigma S₀ C) (needCutSigma S₀ C need)
            else
              .query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C))
                (.inr (.inl ⟨t, o⟩)) q fun b =>
                  ((k ((C t o).join a b)).inT S₀ t).cut (cutSigma S₀ C) (needCutSigma S₀ C need))
        = OComp.query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C))
          (.inl (.inl ⟨t, o⟩)) q fun a =>
            (if (C t o).isWhole || !need t o q a then (k ((C t o).alone a)).cut (C t) (need t)
                else
                  .query (S := cutSpec (S t) (C t)) (.inr o) q fun b =>
                    (k ((C t o).join a b)).cut (C t) (need t)).inT1
              S₀ C t
      refine congrArg _ (funext fun a => ?_)
      by_cases h : ((C t o).isWhole || !need t o q a) = true
      · rw [if_pos h, if_pos h, ih]
      · rw [if_neg h, if_neg h]
        show _ = OComp.query (S := cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) (.inr (.inl ⟨t, o⟩))
            q fun b => ((k ((C t o).join a b)).cut (C t) (need t)).inT1 S₀ C t
        exact congrArg _ (funext fun b => ih _)

end Cut

/-! ## The expansion from a state under an adaptive rule -/

section St
variable {lam : ℕ} (C : ∀ t o, OCut ((S t).Rng o))
  (C2 : ∀ t x, Link lam ((cutSpec (S t) (C t)).Rng x))

/-- a part of (t, o) is treated as that part of o at t; a part of an oracle of S₀ is unchanged
(`plain`) -/
def linksSigma :
    ∀ x : (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)).ι,
      Link lam ((cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)).Rng x)
  | .inl (.inl o) => C2 o.1 (.inl o.2)
  | .inr (.inl o) => C2 o.1 (.inr o.2)
  | .inl (.inr _) => .plain
  | .inr (.inr _) => .plain

/-- the adaptive rule of the whole -/
def needASigma (need : ∀ t, NeedA (cutSpec (S t) (C t)) lam) :
    NeedA (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam
  | .inl (.inl o) => need o.1 (.inl o.2)
  | .inr (.inl o) => need o.1 (.inr o.2)
  | .inl (.inr _) => fun _ _ _ => false
  | .inr (.inr _) => fun _ _ _ => false

/-- an algorithm over the family after the two steps at t, seen over that of the whole; the
expansion queries from a state go to the one added oracle dr -/
def OComp.inT2 (t : T) :
    OComp (stSpec (cutSpec (S t) (C t)) lam (C2 t)) α →
    OComp (stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2)) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).inT2 t
  | .query (.inl (.inl o)) q k =>
    .query (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
      (.inl (.inl (.inl ⟨t, o⟩))) q fun r => (k r).inT2 t
  | .query (.inl (.inr o)) q k =>
    .query (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
      (.inl (.inr (.inl ⟨t, o⟩))) q fun r => (k r).inT2 t
  | .query (.inr u) q k =>
    .query (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
      (.inr u) q fun r => (k r).inT2 t

theorem OComp.inT2_bind (t : T) (c : OComp (stSpec (cutSpec (S t) (C t)) lam (C2 t)) α)
    (g : α → OComp (stSpec (cutSpec (S t) (C t)) lam (C2 t)) β) :
    (c.bind g).inT2 S₀ C C2 t = (c.inT2 S₀ C C2 t).bind fun a => (g a).inT2 S₀ C C2 t := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query x q k ih =>
      rcases x with (o | o) | u
      · exact congrArg
          (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inl (.inl ⟨t, o⟩))) q) (funext ih)
      · exact congrArg
          (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inr (.inl ⟨t, o⟩))) q) (funext ih)
      · exact congrArg
          (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inr u) q) (funext ih)

theorem askAd_inT2 (t : T) (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam),
      (askAd (C2 t) σ nd K j acc).inT2 S₀ C C2 t = askAd (linksSigma S₀ C C2) σ nd K j acc
  | 0, _, _ => rfl
  | K + 1, j, acc => by
      unfold askAd
      cases nd j acc with
      | true =>
        exact congrArg
          (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inr ()) (σ, j))
          (funext fun r => askAd_inT2 t σ nd K (j + 1) _)
      | false => exact askAd_inT2 t σ nd K (j + 1) acc

theorem expandA_inT2 (t : T) {R : Type} (c : Link lam R)
    (nd : ℕ → (ℕ → Dg lam) → Bool) (a : c.Ans) :
    (expandA (C2 t) c nd a).inT2 S₀ C C2 t = expandA (linksSigma S₀ C C2) c nd a := by
  cases c with
  | plain => rfl
  | chain K e =>
      show ((askAd (C2 t) a nd K 0 (acc0 lam)).bind fun acc =>
            .pure (e.symm ((fun i : Fin K => acc i.val), a))).inT2
          S₀ C C2 t =
        (askAd (linksSigma S₀ C C2) a nd K 0 (acc0 lam)).bind fun acc =>
          .pure (e.symm ((fun i : Fin K => acc i.val), a))
      rw [OComp.inT2_bind, askAd_inT2]
      rfl

/-- The expansion from a state under an adaptive rule commutes with "seen in the whole". -/
theorem stateFirstA_inT1 (need : ∀ t, NeedA (cutSpec (S t) (C t)) lam)
    (t : T) (c : OComp (cutSpec (S t) (C t)) α) :
    (c.inT1 S₀ C t).stateFirstA (linksSigma S₀ C C2) (needASigma S₀ C need) =
      (c.stateFirstA (C2 t) (need t)).inT2 S₀ C C2 t := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query x q k ih =>
      rcases x with o | o
      · show OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inl (.inl ⟨t, o⟩))) q (fun a =>
              (expandA (linksSigma S₀ C C2) (C2 t (.inl o)) (need t (.inl o) q) a).bind fun r =>
                ((k r).inT1 S₀ C t).stateFirstA (linksSigma S₀ C C2) (needASigma S₀ C need)) =
          OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inl (.inl ⟨t, o⟩))) q fun a =>
              ((expandA (C2 t) (C2 t (.inl o)) (need t (.inl o) q) a).bind fun r =>
                  (k r).stateFirstA (C2 t) (need t)).inT2
                S₀ C C2 t
        refine congrArg _ (funext fun a => ?_)
        rw [OComp.inT2_bind, expandA_inT2]
        exact congrArg _ (funext ih)
      · show OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inr (.inl ⟨t, o⟩))) q (fun a =>
              (expandA (linksSigma S₀ C C2) (C2 t (.inr o)) (need t (.inr o) q) a).bind fun r =>
                ((k r).inT1 S₀ C t).stateFirstA (linksSigma S₀ C C2) (needASigma S₀ C need)) =
          OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inr (.inl ⟨t, o⟩))) q fun a =>
              ((expandA (C2 t) (C2 t (.inr o)) (need t (.inr o) q) a).bind fun r =>
                  (k r).stateFirstA (C2 t) (need t)).inT2
                S₀ C C2 t
        refine congrArg _ (funext fun a => ?_)
        rw [OComp.inT2_bind, expandA_inT2]
        exact congrArg _ (funext ih)

end St

/-! ## The step to one hash function -/

section One
variable {lam : ℕ}

/-- the program over the hash function that answers the typed query (o, q) under a query encoding m
-/
def ansProg {S : OSpec} (m : OracleCoding S lam) (o : S.ι) (q : S.Dom o) : OComp (rom lam) (S.Rng o) :=
  (askAll lam (m.blocks o) (m.code o q)).bind fun bs => .pure ((m.rng o).symm bs)

theorem bind_bindO {S : OSpec} {γ : Type} (c : OComp S α) (g : α → OComp S β) (h : β → OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q k ih => exact congrArg (OComp.query o q) (funext ih)

theorem overOne_query {S : OSpec} (m : OracleCoding S lam) (o : S.ι)
    (q : S.Dom o) (k : S.Rng o → OComp S α) :
    (OComp.query o q k).overOne m = (ansProg m o q).bind fun r => (k r).overOne m := by
  show (askAll lam (m.blocks o) (m.code o q)).bind (fun bs => (k ((m.rng o).symm bs)).overOne m) =
    ((askAll lam (m.blocks o) (m.code o q)).bind fun bs => .pure ((m.rng o).symm bs)).bind
      fun r => (k r).overOne m
  rw [bind_bindO]
  rfl

/-- every query of the algorithm, on every path, has the property P -/
def OComp.AsksIn {S : OSpec} (P : (o : S.ι) → S.Dom o → Prop) : OComp S α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, (k r).AsksIn P
  | .query o q k => P o q ∧ ∀ r, (k r).AsksIn P

variable (C : ∀ t o, OCut ((S t).Rng o)) (C2 : ∀ t x, Link lam ((cutSpec (S t) (C t)).Rng x))

/-- an oracle of the family after the two steps at t, as an oracle of the whole -/
def nameT2 (t : T) :
    (stSpec (cutSpec (S t) (C t)) lam (C2 t)).ι →
    (stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2)).ι
  | .inl (.inl o) => .inl (.inl (.inl ⟨t, o⟩))
  | .inl (.inr o) => .inl (.inr (.inl ⟨t, o⟩))
  | .inr u => .inr u

/-- at the query (x, q) the query encoding of the whole and that at t answer by the same program -/
def SameAns
    (mS : OracleCoding (stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2)) lam)
    (t : T) (m : OracleCoding (stSpec (cutSpec (S t) (C t)) lam (C2 t)) lam) :
    (x : (stSpec (cutSpec (S t) (C t)) lam (C2 t)).ι) →
    (stSpec (cutSpec (S t) (C t)) lam (C2 t)).Dom x → Prop
  | .inl (.inl o), q => ansProg mS (.inl (.inl (.inl ⟨t, o⟩))) q = ansProg m (.inl (.inl o)) q
  | .inl (.inr o), q => ansProg mS (.inl (.inr (.inl ⟨t, o⟩))) q = ansProg m (.inl (.inr o)) q
  | .inr u, q => ansProg mS (.inr u) q = ansProg m (.inr u) q

/-- The step to one hash function commutes, for an algorithm that queries only where the two query
encodings answer by the same program (`AsksIn`, `SameAns`). -/
theorem overOne_inT2
    (mS : OracleCoding (stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2)) lam)
    (t : T) (m : OracleCoding (stSpec (cutSpec (S t) (C t)) lam (C2 t)) lam)
    (c : OComp (stSpec (cutSpec (S t) (C t)) lam (C2 t)) α)
    (h : c.AsksIn (SameAns S₀ C C2 mS t m)) :
    (c.inT2 S₀ C C2 t).overOne mS = c.overOne m := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext fun r => ih r (h r))
  | query x q k ih =>
      rcases x with (o | o) | u
      · show (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inl (.inl ⟨t, o⟩))) q fun r => (k r).inT2 S₀ C C2 t).overOne mS = _
        rw [overOne_query, overOne_query,
          show ansProg mS (.inl (.inl (.inl ⟨t, o⟩))) q = ansProg m (.inl (.inl o)) q from h.1]
        exact congrArg _ (funext fun r => ih r (h.2 r))
      · show (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inl (.inr (.inl ⟨t, o⟩))) q fun r => (k r).inT2 S₀ C C2 t).overOne mS = _
        rw [overOne_query, overOne_query,
          show ansProg mS (.inl (.inr (.inl ⟨t, o⟩))) q = ansProg m (.inl (.inr o)) q from h.1]
        exact congrArg _ (funext fun r => ih r (h.2 r))
      · show (OComp.query
            (S := stSpec (cutSpec (OSpec.sigma S S₀) (cutSigma S₀ C)) lam (linksSigma S₀ C C2))
            (.inr u) q fun r => (k r).inT2 S₀ C C2 t).overOne mS = _
        rw [overOne_query, overOne_query,
          show ansProg mS (.inr u) q = ansProg m (.inr u) q from h.1]
        exact congrArg _ (funext fun r => ih r (h.2 r))

end One

end Rom
