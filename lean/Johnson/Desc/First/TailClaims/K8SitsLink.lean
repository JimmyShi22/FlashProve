-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8SitsLink.lean: THE SMALLNESS TEST's THREE RUNS ALONG A LINK's FRAME:
the frame's two folds (the gathering of a link's claims; the runs behind the batching:
Johnson/Desc/Block.lean) are cut at the three runs, and with the batching's two writings between
them the yeses of the batching's block and of the runs behind it give what K08SitsField
(K8SitsBetween.lean) concludes.

Statements and proofs.
Main names:
  foldl_bind_error: a fold of steps that may refuse stays at a refusal.
  claimsInStep_ok; stepsFrom; claimsInBy_cut: a yes of the gathering over pre ++ o :: post gives the
    gathering over pre, the run that the order names at o, its yes, and the steps over post from
    there.
  stepsFrom_keeps: a field of the verifier's state that each run of a stretch leaves stays over the
    stretch.
  stepsFrom_list: what is gathered over a stretch stands behind what was gathered so far.
  afterIn_cons, afterIn_cons_of, afterIn_keeps: the like for the runs behind the batching: cut
    behind the first; put together again; cut between two stretches, with the first stretch's own
    yes handed out.
  RunUnder, AfterUnder: a run that hands on another's yes or refuses (a wrapper's run under the bare
    one). guarded_claims_under, guarded_after_under: the runs of Block.guarded (SeatGuard.lean)
    stand under the bare block's, name by name (the bare run is handed out both as a lookup and as a
    member). whole_guarded: so the first three premises of K08SitsLink hold where bs[i] is, under
    that wrapper, any block that has K8.whole p's runs, whatever its name, place and decision.
  **K08SitsLink** (a closed Prop), **k08_sits_link**: at any list of blocks bs, any test each, any
    index i, ANY state t, any z and any b: IF the runs that bs states at i under the three names
    stand under those of K8.whole p, each run of post and of mid leaves k8Field, the gathering from
    t says yes with z, and the runs behind the batching say yes from atS.set z.2 b to sE: THEN at x,
    what the gathering over pre returns from t, equations says yes at x's state's parts and the
    ledger's count + the number of x's claims; its list cls stands in z's list right behind x's; s3'
    is what the runs "K8.lsTail" and mid's return from atS.set z.2 b; the run that bs states at i
    under "K8.tests" says yes at s3' with sE; G' is s3''s ledger; and K08SitsField's conclusion
    holds. t, z, b ARE GIVEN LETTERS; EVERY LETTER UNDER THE ∃ IS THE VALUE OF A FUNCTION AT THEM (a
    gathering's or a run's return, a lookup, a field of a state).
  k08_sits_batch: a yes of the batching's block (K9.batch atS w over the gathering) gives SOME a, b,
    z with the gathering's yes from atS.set s a and sB = atS.set z.2 b (batch_writes).
Limits. GENERAL IN THE LINK: WHAT SITS AT bs[i], THE ORDERS' SHAPE (pre ++ (i, "K8.equations") ::
post; (i, "K8.lsTail") :: mid ++ [(i, "K8.tests")]) AND THE STAYING OF k8Field OVER post AND mid ARE
PREMISES: that a description's link has this shape with K8.whole under its wrappers at i is not said
here. OF a AND b NOTHING IS SAID BUT THAT THEY ARE THERE: that a is the draw's writing and b the
adding's, and what they lay, wants a stronger law on the batching's block than batch_writes: whoever
has one calls k08_sits_link at its own t and b. The batching is bare: under a wrapper its yes must
first be handed down. The link's tests behind the adding (Link.tests) are not read. From yeses
alone.

-/
import Johnson.Desc.First.TailClaims.K8SitsBetween
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

/-- A fold of steps that may refuse stays at a refusal. -/
theorem foldl_bind_error {α β ε : Type} (g : β → α → Except ε β) (l : List α) (e : ε) :
    l.foldl (fun (acc : Except ε β) o => acc.bind fun x => g x o) (.error e) = .error e := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

section Frame

variable {T Cl : Type}

/-- A yes of one step of the gathering. -/
theorem claimsInStep_ok {each : Nat × String → List Cl → T → Except String Unit}
    {bs : List (Block T Cl)} {x x1 : List Cl × T} {o : Nat × String}
    (h : claimsInStep each bs x o = .ok x1) :
    ∃ run y, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
      run x.1.length x.2 = .ok y ∧ x1 = (x.1 ++ y.1, y.2) := by
  unfold claimsInStep at h
  cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
  | none => rw [hl] at h; exact nomatch h
  | some run =>
    rw [hl] at h
    change (match run x.1.length x.2 with
      | .ok y => match each o y.1 y.2 with
        | .ok _ => .ok (x.1 ++ y.1, y.2)
        | .error e => .error (o.2 ++ ": behind the run: " ++ e)
      | .error e => .error (o.2 ++ ": " ++ e)) = Except.ok x1 at h
    cases hr : run x.1.length x.2 with
    | error e => rw [hr] at h; exact nomatch h
    | ok y =>
      rw [hr] at h
      cases he : each o y.1 y.2 with
      | error e => simp only [he] at h; exact nomatch h
      | ok u =>
        simp only [he] at h
        exact ⟨run, y, rfl, hr, (Except.ok.inj h).symm⟩

/-- The gathering's steps over a stretch of an order, from what is gathered so far. -/
def stepsFrom (each : Nat × String → List Cl → T → Except String Unit) (bs : List (Block T Cl))
    (l : List (Nat × String)) (x : List Cl × T) : Except String (List Cl × T) :=
  l.foldl (fun (acc : Except String (List Cl × T)) o => acc.bind fun x => claimsInStep each bs x o)
    (.ok x)

/-- **The gathering, cut at an entry of the order.** -/
theorem claimsInBy_cut {each : Nat × String → List Cl → T → Except String Unit}
    {bs : List (Block T Cl)} {pre post : List (Nat × String)} {o : Nat × String} {s : T}
    {z : List Cl × T} (h : claimsInBy each bs (pre ++ o :: post) s = .ok z) :
    ∃ x run y, claimsInBy each bs pre s = .ok x ∧
      ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run ∧
      run x.1.length x.2 = .ok y ∧ stepsFrom each bs post (x.1 ++ y.1, y.2) = .ok z := by
  unfold claimsInBy at h
  rw [List.foldl_append, List.foldl_cons] at h
  cases hx : pre.foldl (fun (acc : Except String (List Cl × T)) o =>
      acc.bind fun x => claimsInStep each bs x o) (.ok ([], s)) with
  | error e =>
    rw [hx] at h
    change post.foldl _ (Except.error e) = _ at h
    rw [foldl_bind_error] at h
    exact nomatch h
  | ok x =>
    rw [hx] at h
    change post.foldl _ (claimsInStep each bs x o) = _ at h
    cases hs : claimsInStep each bs x o with
    | error e =>
      rw [hs, foldl_bind_error] at h
      exact nomatch h
    | ok x1 =>
      rw [hs] at h
      obtain ⟨run, y, hl, hr, rfl⟩ := claimsInStep_ok hs
      exact ⟨x, run, y, hx, hl, hr, h⟩

/-- A field that each run of a stretch leaves stays over the stretch. -/
theorem stepsFrom_keeps {β : Type} (f : T → β)
    {each : Nat × String → List Cl → T → Except String Unit} {bs : List (Block T Cl)} :
    ∀ (l : List (Nat × String)) (x z : List Cl × T),
      (∀ o ∈ l, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
        ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e) →
      stepsFrom each bs l x = .ok z → f z.2 = f x.2
  | [], x, z, _, h => by
    obtain rfl : x = z := Except.ok.inj h
    rfl
  | o :: l, x, z, hk, h => by
    unfold stepsFrom at h
    rw [List.foldl_cons] at h
    change l.foldl _ (claimsInStep each bs x o) = _ at h
    cases hs : claimsInStep each bs x o with
    | error e =>
      rw [hs, foldl_bind_error] at h
      exact nomatch h
    | ok x1 =>
      rw [hs] at h
      obtain ⟨run, y, hl, hr, rfl⟩ := claimsInStep_ok hs
      exact (stepsFrom_keeps f l _ z (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) h).trans
        (hk o List.mem_cons_self run hl _ _ y.1 y.2 hr)

/-- What is gathered over a stretch stands behind what was gathered so far. -/
theorem stepsFrom_list {each : Nat × String → List Cl → T → Except String Unit}
    {bs : List (Block T Cl)} :
    ∀ (l : List (Nat × String)) (x z : List Cl × T), stepsFrom each bs l x = .ok z →
      ∃ rest, z.1 = x.1 ++ rest
  | [], x, z, h => by
    obtain rfl : x = z := Except.ok.inj h
    exact ⟨[], (List.append_nil _).symm⟩
  | o :: l, x, z, h => by
    unfold stepsFrom at h
    rw [List.foldl_cons] at h
    change l.foldl _ (claimsInStep each bs x o) = _ at h
    cases hs : claimsInStep each bs x o with
    | error e =>
      rw [hs, foldl_bind_error] at h
      exact nomatch h
    | ok x1 =>
      rw [hs] at h
      obtain ⟨run, y, _, _, rfl⟩ := claimsInStep_ok hs
      obtain ⟨rest, e⟩ := stepsFrom_list l _ z h
      exact ⟨y.1 ++ rest, by rw [e, List.append_assoc]⟩

/-- One step of the runs behind the batching. -/
def afterStep (bs : List (Block T Cl)) (x : T) (o : Nat × String) : Except String T :=
  (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
    match run x with
    | .ok y => .ok y
    | .error e => .error (o.2 ++ ": " ++ e)

theorem afterStep_ok {bs : List (Block T Cl)} {x y : T} {o : Nat × String}
    (h : afterStep bs x o = .ok y) :
    ∃ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run ∧ run x = .ok y := by
  unfold afterStep at h
  cases hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) with
  | none => rw [hl] at h; exact nomatch h
  | some run =>
    rw [hl] at h
    change (match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)) = Except.ok y at h
    cases hr : run x with
    | error e => rw [hr] at h; exact nomatch h
    | ok y' =>
      rw [hr] at h
      obtain rfl : y' = y := Except.ok.inj h
      exact ⟨run, rfl, hr⟩

/-- The runs behind the batching, cut behind the first. -/
theorem afterIn_cons {bs : List (Block T Cl)} {o : Nat × String} {l : List (Nat × String)}
    {s z : T} (h : afterIn bs (o :: l) s = .ok z) :
    ∃ run y, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run ∧ run s = .ok y ∧
      afterIn bs l y = .ok z := by
  unfold afterIn at h
  rw [List.foldl_cons] at h
  change l.foldl (fun (acc : Except String T) o => acc.bind fun x => afterStep bs x o)
    (afterStep bs s o) = _ at h
  cases hs : afterStep bs s o with
  | error e =>
    rw [hs, foldl_bind_error] at h
    exact nomatch h
  | ok y =>
    rw [hs] at h
    obtain ⟨run, hl, hr⟩ := afterStep_ok hs
    exact ⟨run, y, hl, hr, h⟩

/-- The other way: a run's yes and the rest's yes give the whole's. -/
theorem afterIn_cons_of {bs : List (Block T Cl)} {o : Nat × String} {l : List (Nat × String)}
    {s y z : T} {run : T → Except String T}
    (hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run) (hr : run s = .ok y)
    (h : afterIn bs l y = .ok z) : afterIn bs (o :: l) s = .ok z := by
  have hs : afterStep bs s o = .ok y := by
    unfold afterStep
    rw [hl]
    change (match run s with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)) = Except.ok y
    rw [hr]
  unfold afterIn
  rw [List.foldl_cons]
  change l.foldl (fun (acc : Except String T) o => acc.bind fun x => afterStep bs x o)
    (afterStep bs s o) = _
  rw [hs]
  exact h

/-- The runs behind the batching, cut between two stretches; and a field that each run of the first
stretch leaves stays over it. -/
theorem afterIn_keeps {β : Type} (f : T → β) {bs : List (Block T Cl)} :
    ∀ (l r : List (Nat × String)) (s z : T),
      (∀ o ∈ l, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
        ∀ e e₁, run e = .ok e₁ → f e₁ = f e) →
      afterIn bs (l ++ r) s = .ok z →
      ∃ y, afterIn bs l s = .ok y ∧ f y = f s ∧ afterIn bs r y = .ok z
  | [], _, s, _, _, h => ⟨s, rfl, rfl, h⟩
  | o :: l, r, s, z, hk, h => by
    obtain ⟨run, y, hl, hr, h'⟩ := afterIn_cons (l := l ++ r) h
    obtain ⟨y', h0, e, h''⟩ :=
      afterIn_keeps f l r y z (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) h'
    exact ⟨y', afterIn_cons_of hl hr h0, e.trans (hk o List.mem_cons_self run hl s y hr), h''⟩

end Frame

/-- A run of claims that hands on another's yes, or refuses. -/
def RunUnder (r' r : Nat → S → Except String (List Claim × S)) : Prop :=
  ∀ n t y, r' n t = .ok y → r n t = .ok y

/-- The like behind the batching. -/
def AfterUnder (r' r : S → Except String S) : Prop := ∀ t y, r' t = .ok y → r t = .ok y

/-- What is found under a key in a list whose second components were mapped. -/
theorem lookup_map_snd {α β : Type} (g : α → β) :
    ∀ (l : List (String × α)) (k : String) (v : β),
      (l.map fun c => (c.1, g c.2)).lookup k = some v →
      ∃ u, l.lookup k = some u ∧ (k, u) ∈ l ∧ v = g u
  | [], _, _, h => nomatch h
  | c :: l, k, v, h => by
    rw [List.map_cons, List.lookup_cons] at h
    cases hk : k == c.1 with
    | true =>
      simp only [hk] at h
      have e : k = c.1 := by simpa using hk
      exact ⟨c.2, by rw [show c = (c.1, c.2) from rfl, List.lookup_cons, hk],
        by rw [e]; exact List.mem_cons_self, (Option.some.inj h).symm⟩
    | false =>
      simp only [hk] at h
      obtain ⟨u, hl, hu, e⟩ := lookup_map_snd g l k v h
      exact ⟨u, by rw [show c = (c.1, c.2) from rfl, List.lookup_cons, hk]; exact hl,
        List.mem_cons_of_mem _ hu, e⟩

/-- The runs of claims of a block under Block.guarded stand under the bare block's. -/
theorem guarded_claims_under (same : S → S → Bool) (but : Place → Bool) (b : Block S Claim)
    (k : String) (r' : Nat → S → Except String (List Claim × S))
    (h : (b.guarded same but).claims.lookup k = some r') :
    ∃ r, b.claims.lookup k = some r ∧ (k, r) ∈ b.claims ∧ RunUnder r' r := by
  obtain ⟨r, hl, hr, rfl⟩ := lookup_map_snd
    (fun (c : Nat → S → Except String (List Claim × S)) n t =>
      (c n t).bind fun y => (seatSame same t y.2).map fun _ => y) b.claims k r' h
  refine ⟨r, hl, hr, fun n t y hy => ?_⟩
  cases hc : r n t with
  | error e => simp only [hc] at hy; exact nomatch hy
  | ok y0 =>
    simp only [hc] at hy
    change (seatSame same t y0.2).map (fun _ => y0) = .ok y at hy
    cases hs : seatSame same t y0.2 with
    | error e => rw [hs] at hy; exact nomatch hy
    | ok u =>
      rw [hs] at hy
      exact congrArg Except.ok (Except.ok.inj hy)

/-- The like behind the batching. -/
theorem guarded_after_under (same : S → S → Bool) (but : Place → Bool) (b : Block S Claim)
    (k : String) (r' : S → Except String S) (h : (b.guarded same but).after.lookup k = some r') :
    ∃ r, b.after.lookup k = some r ∧ (k, r) ∈ b.after ∧ AfterUnder r' r := by
  obtain ⟨r, hl, hr, rfl⟩ := lookup_map_snd
    (fun (c : S → Except String S) t => (c t).bind (seatSame same t)) b.after k r' h
  refine ⟨r, hl, hr, fun t y hy => ?_⟩
  cases hc : r t with
  | error e => simp only [hc] at hy; exact nomatch hy
  | ok y0 =>
    simp only [hc] at hy
    change seatSame same t y0 = .ok y at hy
    unfold seatSame at hy
    split at hy
    · exact hy
    · exact nomatch hy

/-- A run that stands under one that leaves a field leaves it. -/
theorem RunUnder.keeps {β : Type} {f : S → β} {r' r : Nat → S → Except String (List Claim × S)}
    (h : RunUnder r' r) (hk : ∀ n e c e₁, r n e = .ok (c, e₁) → f e₁ = f e) :
    ∀ n e c e₁, r' n e = .ok (c, e₁) → f e₁ = f e :=
  fun n e c e₁ hr => hk n e c e₁ (h n e _ hr)

theorem AfterUnder.keeps {β : Type} {f : S → β} {r' r : S → Except String S}
    (h : AfterUnder r' r) (hk : ∀ e e₁, r e = .ok e₁ → f e₁ = f e) :
    ∀ e e₁, r' e = .ok e₁ → f e₁ = f e :=
  fun e e₁ hr => hk e e₁ (h e _ hr)

/-- **The three runs along a link's frame.** t: the verifier's state from which the gathering
starts; z: what it returns; b: what is laid behind it. -/
def K08SitsLink : Prop :=
  ∀ (p : K8.ParW) (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (i : Nat) (pre post mid : List (Nat × String)),
    (∀ r', ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some r' →
      ∃ r, ("K8.equations", r) ∈ (K8.whole p).claims ∧ RunUnder r' r) →
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r' →
      ∃ r, ("K8.lsTail", r) ∈ (K8.whole p).after ∧ AfterUnder r' r) →
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some r' →
      ∃ r, ("K8.tests", r) ∈ (K8.whole p).after ∧ AfterUnder r' r) →
    (∀ o ∈ post, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e) →
    (∀ o ∈ mid, ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
      ∀ e e₁, run e = .ok e₁ → k8Field e₁ = k8Field e) →
    ∀ (t sE : S) (z : List Claim × S) (b : VerifiableInference.Desc.K9.Part),
      claimsInBy each bs (pre ++ (i, "K8.equations") :: post) t = .ok z →
      afterIn bs ((i, "K8.lsTail") :: mid ++ [(i, "K8.tests")])
        (VerifiableInference.Desc.K9.atS.set z.2 b) = .ok sE →
      ∃ (x : List Claim × S) (cls rest : List Claim) (s3' : S) (rT' : S → Except String S)
        (q : K8Part) (tl' ts : HTailF2) (F1 G' Fc : Fork),
        claimsInBy each bs pre t = .ok x ∧ z.1 = x.1 ++ cls ++ rest ∧ partOf x.2 = some q ∧
        equations (q.F.nClaim + x.1.length) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
        (∀ u, blank u ts = blank u q.tl) ∧ rkSelfTestP ts Fc = .ok () ∧
        afterIn bs ((i, "K8.lsTail") :: mid) (VerifiableInference.Desc.K9.atS.set z.2 b) =
          .ok s3' ∧
        ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some rT' ∧ rT' s3' = .ok sE ∧
        s3'.fork? = some G' ∧ Fc.theta = G'.theta ∧ partOf sE = some ⟨ts, q.funs, Fc⟩

theorem k08_sits_link : K08SitsLink := by
  intro p each bs i pre post mid hE hL hT hpost hmid t sE z b hz ha
  obtain ⟨x, rE', y, hx, hlE, hrE, hst⟩ := claimsInBy_cut hz
  obtain ⟨rest, hrest⟩ := stepsFrom_list post _ z hst
  obtain ⟨rE, hmE, huE⟩ := hE rE' hlE
  have k1 : k8Field z.2 = k8Field y.2 :=
    stepsFrom_keeps k8Field post (x.1 ++ y.1, y.2) z hpost hst
  have k2 : k8Field (VerifiableInference.Desc.K9.atS.set z.2 b) = k8Field y.2 :=
    (VerifiableInference.Desc.K9.atS_set_keeps beside_k8Field z.2 b).trans k1
  obtain ⟨rL', s3, hlL, hrL, ha'⟩ := afterIn_cons ha
  obtain ⟨rL, hmL, huL⟩ := hL rL' hlL
  obtain ⟨s3', hmidRan, k3, ha''⟩ :=
    afterIn_keeps k8Field mid [(i, "K8.tests")] s3 sE hmid ha'
  obtain ⟨rT', s4, hlT, hrT, hend⟩ := afterIn_cons ha''
  obtain rfl : s4 = sE := Except.ok.inj hend
  obtain ⟨rT, hmT, huT⟩ := hT rT' hlT
  obtain ⟨q, tl', ts, F1, G', Fc, h1, h2, h3, h4, h5, h6, h7⟩ :=
    k08_sits_field p rE rL rT hmE hmL hmT x.1.length x.2 y.2 _ s3 s3' s4 y.1
      (huE _ _ _ hrE) k2 (huL _ _ hrL) k3 (huT _ _ hrT)
  exact ⟨x, y.1, rest, s3', rT', q, tl', ts, F1, G', Fc, hx, hrest, h1, h2, h3, h4,
    afterIn_cons_of hlL hrL hmidRan, hlT, hrT, h5, h6, h7⟩

/-- The same from the yes of the batching's block: t and b are then SOME writings that batch_writes
hands out: nothing more is said of them. -/
theorem k08_sits_batch (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (i : Nat) (pre post : List (Nat × String))
    (w : VerifiableInference.Desc.K9.Where) (s sB : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hb : (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w
      (claimsInBy each bs (pre ++ (i, "K8.equations") :: post))).decide s rs gs = .ok sB) :
    ∃ (a b : VerifiableInference.Desc.K9.Part) (z : List Claim × S),
      claimsInBy each bs (pre ++ (i, "K8.equations") :: post)
        (VerifiableInference.Desc.K9.atS.set s a) = .ok z ∧
      sB = VerifiableInference.Desc.K9.atS.set z.2 b := by
  obtain ⟨a, z, b, hz, e⟩ := VerifiableInference.Desc.K9.batch_writes _ w _ hb
  exact ⟨a, b, z, hz, e⟩

/-- Where bs[i] is, under Block.guarded, a block b0 that has K8.whole p's runs (whatever its name,
place and decision), the first three premises of K08SitsLink hold. -/
theorem whole_guarded (p : K8.ParW) (same : S → S → Bool) (but : Place → Bool)
    (b0 : Block S Claim) (hc : b0.claims = (K8.whole p).claims)
    (ha : b0.after = (K8.whole p).after) (bs : List (Block S Claim)) (i : Nat)
    (h : bs[i]? = some (b0.guarded same but)) :
    (∀ r', ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some r' →
      ∃ r, ("K8.equations", r) ∈ (K8.whole p).claims ∧ RunUnder r' r) ∧
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r' →
      ∃ r, ("K8.lsTail", r) ∈ (K8.whole p).after ∧ AfterUnder r' r) ∧
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some r' →
      ∃ r, ("K8.tests", r) ∈ (K8.whole p).after ∧ AfterUnder r' r) := by
  rw [h]
  refine ⟨fun r' hr => ?_, fun r' hr => ?_, fun r' hr => ?_⟩
  · obtain ⟨r, -, hm, hu⟩ := guarded_claims_under same but b0 _ r' hr
    exact ⟨r, hc ▸ hm, hu⟩
  · obtain ⟨r, -, hm, hu⟩ := guarded_after_under same but b0 _ r' hr
    exact ⟨r, ha ▸ hm, hu⟩
  · obtain ⟨r, -, hm, hu⟩ := guarded_after_under same but b0 _ r' hr
    exact ⟨r, ha ▸ hm, hu⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.whole_guarded
#print axioms VerifiableInference.Desc.First.TailClaims.Law.claimsInBy_cut
#print axioms VerifiableInference.Desc.First.TailClaims.Law.afterIn_keeps
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_link
