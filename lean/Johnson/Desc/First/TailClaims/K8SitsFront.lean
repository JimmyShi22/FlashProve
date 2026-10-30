-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8SitsFront.lean: FROM THE VERIFIER's STATE THAT A LINK's BATCHING IS
HANDED TO THE STATE AT WHICH "K8.equations" IS CALLED: where each run of claims that the link's
order lays ahead of that run leaves a field of the verifier's state, and the batching's own writings
leave it, the field is at that call what it was when the batching's block began.

Statements and proofs.
Main names:
  claimsInBy_keeps: the gathering over a stretch from the start leaves a field that each of its runs
    leaves.
  **K08FrontLink** (a closed Prop), **k08_front_link**: at any list of blocks bs, any test each, any
    entry o, any field f beside what the batching writes (K9.Beside f): IF each run of pre leaves f
    and the batching's block over the gathering (pre ++ o :: post) says yes from s: THEN there is
    SOME writing a such that the run that bs states at o was called, and said yes, at the number of
    x's claims and at x's state, x being what the gathering over pre returns from atS.set s a; and f
    at x's state is f s.
  k08_front_field: the same at o := (i, "K8.equations"), f := k8Field: the smallness test's
    structure and the list of tables.
  IN THESE TWO THE LETTER a STANDS LOOSE UNDER THE ∃, AND x AND y HANG ON IT: THEY CANNOT BE JOINED
    WITH ANOTHER THEOREM's a. TO JOIN, CALL ONE OF THE FOUR THAT FOLLOW:
  **K08FrontAt** (a closed Prop), **k08_front_at**: the gathering alone, at ANY state t and any z as
    given letters, any field f: x is what the gathering over pre returns from t; f at x's state is f
    t.
  k08_front_set: that at o := (i, "K8.equations"), f := k8Field, t := atS.set s a, AT EVERY a.
  k08_front_batch: from the yes of the batching's block from s: some a, b, z (batch_writes), and
    with THESE the clauses of k08_front_set: one a, b, z, x for all.
  **k08_sits_front**: the front and the three runs together, at given s, a, b, z: K08SitsLink's
    conclusion at t := atS.set s a, and: the parts q at which equations said yes hold the smallness
    test's structure and the list of tables OF s; and that list is that structure's own closed list
    (eq_funs, EquationsOut.lean).
Limits. GENERAL IN THE LINK: bs, each, the orders' shape and the staying of the field over pre's,
post's and mid's runs are premises. OF a AND b NOTHING IS SAID BUT THAT THEY ARE THERE: that a is
the draw's writing wants a stronger law on the batching's block than batch_writes. The batching is
K9.batch atS w over the gathering, bare. From yeses alone.

-/
import Johnson.Desc.First.TailClaims.K8SitsLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

/-- The gathering over a stretch from the start leaves a field that each of its runs leaves. -/
theorem claimsInBy_keeps {T Cl β : Type} (f : T → β)
    {each : Nat × String → List Cl → T → Except String Unit} {bs : List (Block T Cl)}
    (l : List (Nat × String)) (t : T) (x : List Cl × T)
    (hk : ∀ o ∈ l, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    (h : claimsInBy each bs l t = .ok x) : f x.2 = f t :=
  stepsFrom_keeps f l ([], t) x hk h

/-- **From the state that the batching is handed to the state at which a run is called.** -/
def K08FrontLink : Prop :=
  ∀ (β : Type) (f : S → β), VerifiableInference.Desc.K9.Beside f →
    ∀ (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
      (o : Nat × String) (pre post : List (Nat × String))
      (w : VerifiableInference.Desc.K9.Where),
      (∀ o' ∈ pre, ∀ run, ((bs[o'.1]?).bind fun b => b.claims.lookup o'.2) = some run →
        ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e) →
      ∀ (s sB : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w
          (claimsInBy each bs (pre ++ o :: post))).decide s rs gs = .ok sB →
        ∃ (a : VerifiableInference.Desc.K9.Part) (x : List Claim × S)
          (run : Nat → S → Except String (List Claim × S)) (y : List Claim × S),
          claimsInBy each bs pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
          ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
          run x.1.length x.2 = .ok y ∧ f x.2 = f s

theorem k08_front_link : K08FrontLink := by
  intro β f hf each bs o pre post w hpre s sB rs gs hb
  obtain ⟨a, z, b, hz, -⟩ := VerifiableInference.Desc.K9.batch_writes _ w _ hb
  obtain ⟨x, run, y, hx, hl, hr, -⟩ := claimsInBy_cut hz
  exact ⟨a, x, run, y, hx, hl, hr, (claimsInBy_keeps f pre _ x hpre hx).trans
    (VerifiableInference.Desc.K9.atS_set_keeps hf s a)⟩

/-- The same at "K8.equations" and the smallness test's structure with the list of tables. -/
theorem k08_front_field (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (i : Nat) (pre post : List (Nat × String))
    (w : VerifiableInference.Desc.K9.Where)
    (hpre : ∀ o' ∈ pre, ∀ run, ((bs[o'.1]?).bind fun b => b.claims.lookup o'.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e)
    (s sB : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hb : (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w
      (claimsInBy each bs (pre ++ (i, "K8.equations") :: post))).decide s rs gs = .ok sB) :
    ∃ (a : VerifiableInference.Desc.K9.Part) (x : List Claim × S)
      (run : Nat → S → Except String (List Claim × S)) (y : List Claim × S),
      claimsInBy each bs pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some run ∧
      run x.1.length x.2 = .ok y ∧ x.2.tl? = s.tl? ∧ x.2.funs? = s.funs? := by
  obtain ⟨a, x, run, y, h1, h2, h3, h4⟩ :=
    k08_front_link _ k8Field beside_k8Field each bs (i, "K8.equations") pre post w hpre s sB rs gs
      hb
  exact ⟨a, x, run, y, h1, h2, h3, (Prod.mk.inj h4).1, (Prod.mk.inj h4).2⟩

/-- **From the state at which the gathering starts to the state at which a run is called.** t, z:
given letters. -/
def K08FrontAt : Prop :=
  ∀ (β : Type) (f : S → β)
    (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (o : Nat × String) (pre post : List (Nat × String)),
    (∀ o' ∈ pre, ∀ run, ((bs[o'.1]?).bind fun b => b.claims.lookup o'.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e) →
    ∀ (t : S) (z : List Claim × S), claimsInBy each bs (pre ++ o :: post) t = .ok z →
      ∃ (x : List Claim × S) (run : Nat → S → Except String (List Claim × S))
        (y : List Claim × S), claimsInBy each bs pre t = .ok x ∧
        ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
        run x.1.length x.2 = .ok y ∧ f x.2 = f t

theorem k08_front_at : K08FrontAt := by
  intro β f each bs o pre post hpre t z hz
  obtain ⟨x, run, y, hx, hl, hr, -⟩ := claimsInBy_cut hz
  exact ⟨x, run, y, hx, hl, hr, claimsInBy_keeps f pre t x hpre hx⟩

/-- The same at "K8.equations", the smallness test's structure with the list of tables, and a start
atS.set s a: AT EVERY a. -/
theorem k08_front_set (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (i : Nat) (pre post : List (Nat × String))
    (hpre : ∀ o' ∈ pre, ∀ run, ((bs[o'.1]?).bind fun b => b.claims.lookup o'.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e)
    (s : S) (a : VerifiableInference.Desc.K9.Part) (z : List Claim × S)
    (hz : claimsInBy each bs (pre ++ (i, "K8.equations") :: post)
      (VerifiableInference.Desc.K9.atS.set s a) = .ok z) :
    ∃ (x : List Claim × S) (run : Nat → S → Except String (List Claim × S))
      (y : List Claim × S),
      claimsInBy each bs pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some run ∧
      run x.1.length x.2 = .ok y ∧ x.2.tl? = s.tl? ∧ x.2.funs? = s.funs? := by
  obtain ⟨x, run, y, h1, h2, h3, h4⟩ :=
    k08_front_at _ k8Field each bs (i, "K8.equations") pre post hpre _ z hz
  have h5 := h4.trans (VerifiableInference.Desc.K9.atS_set_keeps beside_k8Field s a)
  exact ⟨x, run, y, h1, h2, h3, (Prod.mk.inj h5).1, (Prod.mk.inj h5).2⟩

/-- **From the yes of the batching's block**: ONE a, b, z, x FOR ALL CLAUSES. -/
theorem k08_front_batch (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (i : Nat) (pre post : List (Nat × String))
    (w : VerifiableInference.Desc.K9.Where)
    (hpre : ∀ o' ∈ pre, ∀ run, ((bs[o'.1]?).bind fun b => b.claims.lookup o'.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e)
    (s sB : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hb : (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w
      (claimsInBy each bs (pre ++ (i, "K8.equations") :: post))).decide s rs gs = .ok sB) :
    ∃ (a b : VerifiableInference.Desc.K9.Part) (z x : List Claim × S)
      (run : Nat → S → Except String (List Claim × S)) (y : List Claim × S),
      claimsInBy each bs (pre ++ (i, "K8.equations") :: post)
        (VerifiableInference.Desc.K9.atS.set s a) = .ok z ∧
      sB = VerifiableInference.Desc.K9.atS.set z.2 b ∧
      claimsInBy each bs pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some run ∧
      run x.1.length x.2 = .ok y ∧ x.2.tl? = s.tl? ∧ x.2.funs? = s.funs? := by
  obtain ⟨a, b, z, hz, e⟩ := k08_sits_batch each bs i pre post w s sB rs gs hb
  obtain ⟨x, run, y, h1, h2, h3, h4, h5⟩ := k08_front_set each bs i pre post hpre s a z hz
  exact ⟨a, b, z, x, run, y, hz, e, h1, h2, h3, h4, h5⟩

/-- **The front and the three runs together**: K08SitsLink's conclusion at t := atS.set s a, with:
the parts q at which equations said yes hold the smallness test's structure and the list of tables
OF s; and that list is that structure's own closed list. -/
theorem k08_sits_front (p : K8.ParW)
    (each : Nat × String → List Claim → S → Except String Unit) (bs : List (Block S Claim))
    (i : Nat) (pre post mid : List (Nat × String))
    (hE : ∀ r', ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some r' →
      ∃ r, ("K8.equations", r) ∈ (K8.whole p).claims ∧ RunUnder r' r)
    (hL : ∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r' →
      ∃ r, ("K8.lsTail", r) ∈ (K8.whole p).after ∧ AfterUnder r' r)
    (hT : ∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some r' →
      ∃ r, ("K8.tests", r) ∈ (K8.whole p).after ∧ AfterUnder r' r)
    (hpre : ∀ o ∈ pre, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e)
    (hpost : ∀ o ∈ post, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e)
    (hmid : ∀ o ∈ mid, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → k8Field e₁ = k8Field e)
    (s sE : S) (a b : VerifiableInference.Desc.K9.Part) (z : List Claim × S)
    (hz : claimsInBy each bs (pre ++ (i, "K8.equations") :: post)
      (VerifiableInference.Desc.K9.atS.set s a) = .ok z)
    (ha : afterIn bs ((i, "K8.lsTail") :: mid ++ [(i, "K8.tests")])
      (VerifiableInference.Desc.K9.atS.set z.2 b) = .ok sE) :
    ∃ (x : List Claim × S) (cls rest : List Claim) (s3' : S) (rT' : S → Except String S)
      (q : K8Part) (tl' ts : HTailF2) (F1 G' Fc : Fork),
      claimsInBy each bs pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      z.1 = x.1 ++ cls ++ rest ∧ partOf x.2 = some q ∧
      s.tl? = some q.tl ∧ s.funs? = some q.funs ∧ q.funs = q.tl.funs ∧
      equations (q.F.nClaim + x.1.length) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
      (∀ u, blank u ts = blank u q.tl) ∧ rkSelfTestP ts Fc = .ok () ∧
      afterIn bs ((i, "K8.lsTail") :: mid) (VerifiableInference.Desc.K9.atS.set z.2 b) =
        .ok s3' ∧
      ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some rT' ∧ rT' s3' = .ok sE ∧
      s3'.fork? = some G' ∧ Fc.theta = G'.theta ∧ partOf sE = some ⟨ts, q.funs, Fc⟩ := by
  obtain ⟨x, cls, rest, s3', rT', q, tl', ts, F1, G', Fc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12⟩ := k08_sits_link p each bs i pre post mid hE hL hT hpost hmid _ sE z b hz ha
  have k := (claimsInBy_keeps k8Field pre _ x hpre h1).trans
    (VerifiableInference.Desc.K9.atS_set_keeps beside_k8Field s a)
  obtain ⟨q1, -, q3⟩ := partOf_some.1 h3
  exact ⟨x, cls, rest, s3', rT', q, tl', ts, F1, G', Fc, h1, h2, h3,
    (Prod.mk.inj k).1.symm.trans q1, (Prod.mk.inj k).2.symm.trans q3, eq_funs h4, h4, h5, h6, h7,
    h8, h9, h10, h11, h12⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_front_link
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_front_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_front_at
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_front_batch
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_front
