-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PlanAtPolicy.lean: two parameter files whose strict scans differ only in the numbers of
the lines C, theta and cap give the same plan, except at the places where a plan holds these three
numbers.

Why. The planner's text with the digest as an argument (`plannedAt`, OnBytes/Tie/ChainsAtCfg.lean)
makes a plan from a parameter file, a scale file, a layout file and a digest c. A statement that is
shown at one plan can be carried to the plan of a file with another acceptance policy only if one
knows what the two plans share.

Where a plan holds the three numbers: at four places. `X.hS` (three fields); `X.P.h` (three fields);
`X.P.values` (three pairs of a name and a value); and the field `run` of the head's link in
`built.links`, a function made from `X.hS` (`headPlanOf`, OnBytes/Model/VerifyLinks.lean).

Main names.
* `Hdr.withPol`, `Head.Shape.withPol`, `valuesWithPol`, `PolScan.withPol`, `Public.withPol`: a
  record with the three numbers replaced by C, theta, cap.
* `headRun r l`: the link l with r as its field `run` if l is the head's (kind 2); else l.
  `sansRun l`: the link l with a fixed value in the field `run`.
* `plannedAt_withPol`: THE LAW. Hypotheses: h, `plannedAt` returns p at pol; h', it returns p' at
  pol', with the same scale file, layout file and digest c; hs, the strict scan of pol' is
  `p.X.P.withPol C theta cap`. Then `p'.X = p.X.withPol C theta cap`, `p'.cfg = p.cfg`,
  `p'.chains = p.chains`, and `p'.built.links` is `p.built.links` with the head's link's `run`
  replaced by that of `headPlanOf (p.X.withPol C theta cap) default`.
* `plannedAt_withPol_eq`: the same as one equation: `Planned` has four fields and `LinksH` one, so
  the four clauses fix p' whole.
* `plannedAt_withPol_sansRun`: so the two lists of links agree in every field but `run`, the names
  of the arrays (`arrayOf`) among them. `planZero_withPol`: the law at 32 zero bytes for c.
* `publicOf_withPol`, `chainsOf_withPol`, `builtOf_withPol`: the law's three steps.
  `declareLinks_headRun`: `declareLinks` (OnBytes/Model/StagesLinks.lean) does not read the `run`
  that `headRun r` replaces, where both calls return.
* `publicOf_hS`, `plannedAt_hS`: the three numbers in `X.hS` are those in `X.P.h`. `plannedAt_scan`:
  the scan in a plan is the scan of the parameter file.
* On the way: `lookup_map_keep`, `value_withPol`, `layerShape_withPol` (seven numbers of a layer
  sub-proof are read by name); `headRun_arrayOf`, `declareOwn_headRun`, `foreign_headRun`,
  `fold_headRun`, `linksOf_withPol`, `forIn_two`; `shapesWith_withPol`, `shapesOf_withPol`;
  `polLayout_withPol`, `layout_withPol`; `sansRun_headRun`.

The first clause is an equation of whole records. `Public` has nine fields, and `Public.withPol`
says of each: P and hS are replaced; digests, layers, HLy, G, A, H and owner stay. `X.y`, `X.p4`,
`X.NGr` and `X.T` are no fields: they are definitions on `X.layers`, so they stay too.

Limits.
* Both plans are hypotheses. Nothing here shows that `plannedAt` returns at any file. In particular
  the tests that read the three numbers (`Head.policy` and three lines of `Head.h9`,
  OnBytes/Model/HeadLayout.lean) and the hash of the parameter file's bytes (`hPar`) are not shown
  to pass or to return.
* hs is a hypothesis. Nothing here shows it of any two files. No byte of a file is read here.
* The digest c is the same on both sides. `Verify.planned` (OnBytes/Model/Verify.lean) forms c from
  the three files, so it has two digests at two parameter files: the law does not speak of it.
  `plannedAt_at` (OnBytes/Tie/ChainsAtCfg.lean) brings a plan from one digest of 32 bytes to
  another, if its seven strings of parameter bytes are short: so one file's plan can be brought to
  the other's digest, and the law be applied there.
* Nothing is said on what `run` does, at either plan.
* NOT SAID: that what is made by running links is the same at the two plans. `linksOf p.X cov` makes
  the head's check from `X.hS`, so a dry run of the links' block can depend on the three numbers.
  That the head's check states the same rounds whatever the three numbers are is another law:
  OnBytes/Flat/PolicyFreeHead.lean; at plans: OnBytes/Tie/PlanAtPolicyDry.lean. So no equation
  between data made by dry runs at the two plans (such as `dataPFull`, Johnson/Flat/WireAt.lean)
  follows from this file.
* The three pairs in `X.P.values` are read outside the planner: `statementHeld`
  (OnBytes/Model/VerifyStatement.lean) compares words of the item request with the values under the
  names of `Proof.names130` (OnBytes/Proof/RequestItem.lean), among them C, theta, cap.
* At C, theta, cap equal to the first file's own numbers the law is not shown to give p' = p: that
  `withPol` at a record's own numbers is the record is not stated here.
* Nothing on soundness, on hiding or on a security level.

Hash functions. The digest is the argument c: no statement of this file calls the format's hash
(`formatHashFastForm`, OnBytes/Hash/H.lean), and none forms the format's digest of the three files
(`Params.configurationDigest`). The format's second hash, a fixed function built on Lean's text of
BLAKE2b (`secondHashFunction`, `secondHashFunctionTree`, OnBytes/Hash/SecondHashFunction.lean), is called inside `publicOf`, and so inside
`plannedAt` and `planZero`, at both parameter files alike: for the digests of the public tables and
of the lists of lookup calls, and in `hPar`, another digest of the same three files, whose value is
dropped. So it stands beneath every statement here that names one of these three, and beneath no
other. This is read off the definitions that the statements name: it is not a theorem. The head of
OnBytes/Tie/PlanAtDigest.lean says the same of `plannedAt`.

For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.PlanAtDigest
import OnBytes.Tie.Pv.Lookup.Ends.FoBare

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Params (exc_bind)
open OnBytes.Model OnBytes.Model.Verify
open OnBytes.Model.Stages

/-! ### records with the three numbers replaced -/

/-- The value lines as a record, with the numbers of the lines C, theta, cap replaced. -/
def _root_.OnBytes.Model.Hdr.withPol (h : Hdr) (C theta cap : Nat) : Hdr :=
  { h with clipC := C, theta := theta, cap := cap }

/-- The numbers of the head's sub-proof, with the same three replaced. -/
def _root_.OnBytes.Model.Head.Shape.withPol (h : Head.Shape) (C theta cap : Nat) : Head.Shape :=
  { h with clipC := C, theta := theta, cap := cap }

/-- The list of names and values, with the value replaced at every pair whose name is C, theta or
cap. In the list of a strict scan each of the three names stands once: by a reading of `valueNames`
and `polScan` (OnBytes/Model/Config.lean); no theorem here says it, and none here needs it. -/
def valuesWithPol (v : List (String × Nat)) (C theta cap : Nat) : List (String × Nat) :=
  v.map fun x =>
    if x.1 = "C" then (x.1, C) else if x.1 = "theta" then (x.1, theta)
    else if x.1 = "cap" then (x.1, cap) else x

/-- A strict scan with the three numbers replaced, in the list and in the record. All its other
fields stay. -/
def _root_.OnBytes.Model.PolScan.withPol (P : PolScan) (C theta cap : Nat) : PolScan :=
  { P with values := valuesWithPol P.values C theta cap, h := P.h.withPol C theta cap }

/-- The public part with the three numbers replaced: in the scan P and in hS. Its seven other fields
stay. -/
def _root_.OnBytes.Model.Verify.Public.withPol (X : Public) (C theta cap : Nat) : Public :=
  { X with P := X.P.withPol C theta cap, hS := X.hS.withPol C theta cap }

/-- A link with the check r in the place of its own, if it is the head's (kind 2). -/
def headRun (r : LinkM (Option WsForkOut)) (l : LinkH) : LinkH :=
  { l with run := if l.kind = 2 then r else l.run }

/-- A link with a fixed value in the place of its check. -/
def sansRun (l : LinkH) : LinkH := { l with run := pure none }


/-! ### the scan -/

/-- A map over a list of pairs that keeps every name, and every pair under the name n, keeps what is
looked up under n. -/
theorem lookup_map_keep {β : Type} (n : String) (f : String × β → String × β)
    (hk : ∀ x, (f x).1 = x.1) (hv : ∀ x, x.1 = n → f x = x) :
    ∀ l : List (String × β), (l.map f).lookup n = l.lookup n
  | [] => rfl
  | x :: l => by
    obtain ⟨k, v⟩ := x
    have e : f (k, v) = (k, (f (k, v)).2) := Prod.ext (hk (k, v)) rfl
    rw [List.map_cons, e, List.lookup_cons, List.lookup_cons, lookup_map_keep n f hk hv l]
    by_cases c : n = k
    · have e2 := hv (k, v) c.symm
      rw [e2]
    · have c' : (n == k) = false := by simpa using c
      rw [c']

/-- A line's value by a name other than C, theta, cap is not changed. -/
theorem value_withPol (P : PolScan) (C theta cap : Nat) (n : String) (h1 : n ≠ "C")
    (h2 : n ≠ "theta") (h3 : n ≠ "cap") : (P.withPol C theta cap).value n = P.value n := by
  unfold PolScan.value
  show ((valuesWithPol P.values C theta cap).lookup n).getD 0 = _
  unfold valuesWithPol
  rw [lookup_map_keep n]
  · intro x
    dsimp only
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · intro x hx
    dsimp only
    rw [if_neg (fun c => h1 (hx.symm.trans c)), if_neg (fun c => h2 (hx.symm.trans c)),
      if_neg (fun c => h3 (hx.symm.trans c))]

/-- The numbers of a layer sub-proof are not changed. Seven of them are read by name. -/
theorem layerShape_withPol (P : PolScan) (C theta cap : Nat) :
    layerShape (P.withPol C theta cap) = layerShape P := by
  have e : ∀ n : String, n ≠ "C" → n ≠ "theta" → n ≠ "cap" →
      (P.withPol C theta cap).value n = P.value n := value_withPol P C theta cap
  unfold layerShape
  rw [e "hq" (by decide) (by decide) (by decide), e "hv" (by decide) (by decide) (by decide),
    e "ho" (by decide) (by decide) (by decide), e "hgD" (by decide) (by decide) (by decide),
    e "huD" (by decide) (by decide) (by decide), e "hdD" (by decide) (by decide) (by decide),
    e "hr" (by decide) (by decide) (by decide)]
  rfl

/-! ### the links -/

/-- `headRun` and the filling of `arrayOf` can be done in either order. -/
theorem headRun_arrayOf (r : LinkM (Option WsForkOut)) (X : LinkH) (a : Array (Nat × String)) :
    headRun r { X with arrayOf := a } = { headRun r X with arrayOf := a } := rfl

/-- `declareOwn` does not read `run`. -/
theorem declareOwn_headRun (r : LinkM (Option WsForkOut)) (X : LinkH) (l : Nat) :
    declareOwn (headRun r X) l = declareOwn X l := rfl

/-- `foreign` does not read `run`, of the link or of the list. -/
theorem foreign_headRun (r : LinkM (Option WsForkOut)) (links : Array LinkH) (NGr : Nat) (p4 : Bool)
    (l : Nat) (X : LinkH) (s : Array (Nat × String) × Array FrameLink) (tree : Nat) (pl : PlaceF) :
    foreign (links.map (headRun r)) NGr p4 l (headRun r X) s tree pl =
      foreign links NGr p4 l X s tree pl := by
  unfold foreign
  simp only [Array.getElem?_map]
  cases pl.owner with
  | none => rfl
  | some owner =>
    dsimp only
    cases links[layersLink p4 owner]? with
    | none => rfl
    | some Y => rfl

/-- The links before the head's have the kinds 0 and 1: `headRun` leaves them. -/
theorem fold_headRun (r : LinkM (Option WsForkOut)) (NGr : Nat) (p4 : Bool) (A : Array SubPlanH) :
    ∀ (l : List SubPlanH) (k : Nat) (acc : Array LinkH),
      ((l.zipIdx k).foldl (Fo.linksStep NGr p4 A) acc).map (headRun r) =
        (l.zipIdx k).foldl (Fo.linksStep NGr p4 A) (acc.map (headRun r))
  | [], _, _ => rfl
  | s :: l, k, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, List.foldl_cons, fold_headRun r NGr p4 A l (k + 1)]
    congr 1
    unfold Fo.linksStep
    dsimp only
    split
    · split
      · rw [Array.map_push, Array.map_push]
        rfl
      · rw [Array.map_push]
        rfl
    · rw [Array.map_push]
      rfl

/-- Hypotheses: `linksOf` returns at X and at `X.withPol C theta cap`, at one cov. Then the second
list is the first with the head's link's `run` replaced. -/
theorem linksOf_withPol (X : Public) (C theta cap : Nat) (cov : Head.Covered)
    {ls ls' : Array LinkH} (h : linksOf X cov = .ok ls)
    (h' : linksOf (X.withPol C theta cap) cov = .ok ls') :
    ls' = ls.map (headRun (headPlanOf (X.withPol C theta cap) cov).run) := by
  unfold linksOf at h h'
  have e0 : (#[] : Array LinkH).map (headRun (headPlanOf (X.withPol C theta cap) cov).run) = #[] :=
    by simp
  rw [Fo.listLinksH_eq _ _ _ _ _ _ h, Fo.listLinksH_eq _ _ _ _ _ _ h', Array.map_push,
    fold_headRun, e0]
  rfl

/-- Two loops over one list, the second through a map of the members: a relation between the two
states that every pair of passes keeps holds at the two ends. Every pass goes on. -/
theorem forIn_two {α α' σ σ' : Type} (a2 : α → α') (R : σ → σ' → Prop)
    (f : α → σ → Except String (ForInStep σ)) (f' : α' → σ' → Except String (ForInStep σ'))
    (hf : ∀ a s s' t t', R s s' → f a s = .ok t → f' (a2 a) s' = .ok t' →
      ∃ u u', t = .yield u ∧ t' = .yield u' ∧ R u u') :
    ∀ (l : List α) (s : σ) (s' : σ') (r : σ) (r' : σ'), R s s' → forIn l s f = .ok r →
      forIn (l.map a2) s' f' = .ok r' → R r r'
  | [], s, s', r, r', hR, h, h' => by
    rw [List.forIn_nil] at h
    rw [List.map_nil, List.forIn_nil] at h'
    cases h
    cases h'
    exact hR
  | a :: l, s, s', r, r', hR, h, h' => by
    rw [List.forIn_cons] at h
    rw [List.map_cons, List.forIn_cons] at h'
    obtain ⟨t, ht, h⟩ := exc_bind h
    obtain ⟨t', ht', h'⟩ := exc_bind h'
    obtain ⟨u, u', rfl, rfl, hR'⟩ := hf a s s' t t' hR ht ht'
    exact forIn_two a2 R f f' hf l u u' r r' hR' h h'

/-- **`declareLinks` does not read the `run` that `headRun r` replaces.** Hypotheses: it returns x
at a list of links, and x' at the list with `headRun r` applied. Then the links in x' are those in x
with `headRun r` applied, and the declared arrays are the same. -/
theorem declareLinks_headRun (r : LinkM (Option WsForkOut)) (links : Array LinkH) (NGr : Nat)
    (p4 : Bool) {x x' : Array LinkH × Array FrameLink} (h : declareLinks links NGr p4 = .ok x)
    (h' : declareLinks (links.map (headRun r)) NGr p4 = .ok x') :
    x'.1 = x.1.map (headRun r) ∧ x'.2 = x.2 := by
  unfold declareLinks at h h'
  dsimp only at h h'
  obtain ⟨⟨d, n⟩, hr, h⟩ := exc_bind h
  obtain ⟨⟨d', n'⟩, hr', h'⟩ := exc_bind h'
  cases h
  cases h'
  rw [Array.toList_map, List.zipIdx_map] at hr'
  have key := forIn_two (Prod.map (headRun r) id)
    (fun (s s' : MProd (Array FrameLink) (Array LinkH)) =>
      s'.snd = s.snd.map (headRun r) ∧ s'.fst = s.fst) _ _ ?_ _ _ _ _ _ ⟨by simp, rfl⟩ hr hr'
  · exact key
  · rintro ⟨X, l⟩ ⟨dd, nn⟩ ⟨dd', nn'⟩ t t' ⟨e1, e2⟩ hq hq'
    dsimp only [Prod.map, id] at hq hq' e1 e2
    subst e1 e2
    simp only [foreign_headRun] at hq'
    rw [declareOwn_headRun] at hq'
    obtain ⟨d0, hd, hq⟩ := exc_bind hq
    obtain ⟨d0', hd', hq'⟩ := exc_bind hq'
    have ed : d0' = d0 := Except.ok.inj (hd'.symm.trans hd)
    subst ed
    obtain ⟨s0, hs0, hq⟩ := exc_bind hq
    obtain ⟨s0', hs0', hq'⟩ := exc_bind hq'
    have es : s0' = s0 := Except.ok.inj (hs0'.symm.trans hs0)
    subst es
    split at hq
    · obtain ⟨_, e, _⟩ := exc_bind hq
      cases e
    · rename_i hc
      rw [if_neg hc] at hq'
      cases hq
      cases hq'
      refine ⟨_, _, rfl, rfl, ?_, rfl⟩
      show (Array.map (headRun r) nn).push _ = Array.map (headRun r) (nn.push _)
      rw [Array.map_push]
      rfl

/-- `shapesWith` reads none of the three numbers: by unfolding. -/
theorem shapesWith_withPol (X : Public) (C theta cap : Nat) (links : List Params.ReqLink)
    (layout : Params.ReqLayout) (ids : List Nat) :
    shapesWith (X.withPol C theta cap) links layout ids = shapesWith X links layout ids := rfl

/-- Hypotheses: `shapesOf` returns at X and at `X.withPol C theta cap`. Then the two give the
planner the same shapes. -/
theorem shapesOf_withPol (X : Public) (C theta cap : Nat) (layout : Option ByteArray)
    {x x' : Array LinkH × Params.Shapes} (h : shapesOf X layout = .ok x)
    (h' : shapesOf (X.withPol C theta cap) layout = .ok x') : x'.2 = x.2 := by
  unfold shapesOf at h h'
  obtain ⟨ls, hl, h⟩ := exc_bind h
  obtain ⟨ls', hl', h'⟩ := exc_bind h'
  have el := linksOf_withPol X C theta cap default hl hl'
  subst el
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨⟨nm, dc⟩, hd, h⟩ := exc_bind h
  obtain ⟨⟨nm', dc'⟩, hd', h'⟩ := exc_bind h'
  obtain ⟨e1, e2⟩ := declareLinks_headRun _ ls X.NGr X.p4 hd hd'
  dsimp only at e1 e2 h h'
  subst e1 e2
  split at h
  · rename_i f hf
    split at h'
    · rename_i f' hf'
      have ef : f' = f := Option.some.inj (hf'.symm.trans hf)
      subst ef
      obtain ⟨y, hy, h⟩ := exc_bind h
      cases hy
      obtain ⟨y', hy', h'⟩ := exc_bind h'
      cases hy'
      split at h
      · rename_i q hq
        split at h'
        · rename_i q' hq'
          have eq : q' = q := Option.some.inj (hq'.symm.trans hq)
          subst eq
          obtain ⟨y, hy, h⟩ := exc_bind h
          cases hy
          obtain ⟨y', hy', h'⟩ := exc_bind h'
          cases hy'
          obtain ⟨sh, hsh, h⟩ := exc_bind h
          obtain ⟨sh', hsh', h'⟩ := exc_bind h'
          cases h
          cases h'
          rw [shapesWith_withPol, Array.toList_map, List.map_map] at hsh'
          exact Except.ok.inj (hsh'.symm.trans hsh)
        · obtain ⟨_, e, _⟩ := exc_bind h'
          cases e
      · obtain ⟨_, e, _⟩ := exc_bind h
        cases e
    · obtain ⟨_, e, _⟩ := exc_bind h'
      cases e
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e

/-- **The seven chains.** Hypotheses: `chainsOf` returns at X and at `X.withPol C theta cap`, at one
layout file and one digest. Then it returns the same chains. -/
theorem chainsOf_withPol (X : Public) (C theta cap : Nat) (layout : Option ByteArray)
    (c : ByteArray) {ch ch' : Chains} (h : chainsOf X layout c = .ok ch)
    (h' : chainsOf (X.withPol C theta cap) layout c = .ok ch') : ch' = ch := by
  unfold chainsOf at h h'
  obtain ⟨⟨ls, sh⟩, hs, h⟩ := exc_bind h
  obtain ⟨⟨ls', sh'⟩, hs', h'⟩ := exc_bind h'
  have e : sh' = sh := shapesOf_withPol X C theta cap layout hs hs'
  subst e
  dsimp only at h h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨made, hm, h⟩ := exc_bind h
  obtain ⟨made', hm', h'⟩ := exc_bind h'
  have em : made' = made := Except.ok.inj (hm'.symm.trans hm)
  subst em
  exact Except.ok.inj (h'.symm.trans h)

/-- **The links as built.** Hypotheses: `builtOf` returns at X and at `X.withPol C theta cap`, at
the same chains. Then the second list is the first with the head's link's `run` replaced. -/
theorem builtOf_withPol (X : Public) (C theta cap : Nat) (ch : Chains) {B B' : LinksH}
    (h : builtOf X ch = .ok B) (h' : builtOf (X.withPol C theta cap) ch = .ok B') :
    B'.links = B.links.map (headRun (headPlanOf (X.withPol C theta cap) default).run) := by
  unfold builtOf at h h'
  obtain ⟨ls, hl, h⟩ := exc_bind h
  obtain ⟨ls', hl', h'⟩ := exc_bind h'
  have el := linksOf_withPol X C theta cap default hl hl'
  subst el
  unfold buildLinksH at h h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨⟨nm, dc⟩, hd, h⟩ := exc_bind h
  obtain ⟨⟨nm', dc'⟩, hd', h'⟩ := exc_bind h'
  obtain ⟨e1, e2⟩ := declareLinks_headRun _ ls X.NGr X.p4 hd hd'
  dsimp only at e1 e2 h h'
  subst e1 e2
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  split at h
  · obtain ⟨_, e, _⟩ := exc_bind h
    cases e
  · split at h'
    · obtain ⟨_, e, _⟩ := exc_bind h'
      cases e
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      cases h
      cases h'
      rfl

/-! ### the public part -/

/-- One step on both sides whose values are not compared. k, k': the two hypotheses. -/
local macro "skip2 " k:ident k':ident : tactic =>
  `(tactic| (obtain ⟨_, _, $k:ident⟩ := exc_bind $k; obtain ⟨_, _, $k':ident⟩ := exc_bind $k'
             try dsimp only at $k:ident $k':ident))

/-- One step on both sides that is the same term up to unfolding: so the two values are one. -/
local macro "same2 " k:ident k':ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             obtain ⟨a', ha', $k':ident⟩ := exc_bind $k'
             have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
             subst ea
             clear ha ha'
             try dsimp only at $k:ident $k':ident))

/-- Hypotheses: `polLayout` returns at both files, and hs: the scan of the second is the first's
with the three numbers replaced. Then the two layouts of a layer sub-proof are one. -/
theorem polLayout_withPol {pol pol' : ByteArray} {P P' : PolScan} {y y' : Layer.Lay}
    {C theta cap : Nat} (h : polLayout pol = .ok (P, y)) (h' : polLayout pol' = .ok (P', y'))
    (hs : polScan pol' = .ok (P.withPol C theta cap)) :
    P' = P.withPol C theta cap ∧ y' = y := by
  have e : P' = P.withPol C theta cap := Except.ok.inj ((polLayout_scan h').symm.trans hs)
  subst e
  unfold polLayout at h h'
  obtain ⟨P0, h0, h⟩ := exc_bind h
  obtain ⟨P0', h0', h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨y0, hy, h⟩ := exc_bind h
  obtain ⟨y0', hy', h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  cases h
  cases h'
  rw [layerShape_withPol] at hy'
  exact ⟨rfl, Except.ok.inj (hy'.symm.trans hy)⟩

/-- Hypotheses: `Head.layout` returns at h and at `h.withPol C theta cap`. Then it returns the same
layout. The tests that read the three numbers return no value, and are not compared. -/
theorem layout_withPol (h : Head.Shape) (C theta cap : Nat) (t : Array F) {L L' : Head.HL}
    (k : Head.layout h t = .ok L) (k' : Head.layout (h.withPol C theta cap) t = .ok L') :
    L' = L := by
  unfold Head.layout at k k'
  skip2 k k'
  skip2 k k'
  same2 k k'
  same2 k k'
  skip2 k k'
  skip2 k k'
  same2 k k'
  skip2 k k'
  same2 k k'
  skip2 k k'
  same2 k k'
  skip2 k k'
  skip2 k k'
  skip2 k k'
  cases k
  cases k'
  rfl

/-- The steps of `publicOf` behind the branch on attention. -/
local macro "rest4 " k:ident k':ident : tactic =>
  `(tactic| (same2 $k $k'; same2 $k $k'; same2 $k $k'; same2 $k $k'; same2 $k $k'; same2 $k $k'
             skip2 $k $k'; cases $k:ident; cases $k':ident; rfl))

/-- The steps of `publicOf` behind the branch on the sigmoid's table. y: the layers' layout; C, th,
cap: the three numbers. -/
local macro "rest3 " k:ident k':ident y:ident C:ident th:ident cap:ident : tactic =>
  `(tactic| (
    skip2 $k $k'; skip2 $k $k'; skip2 $k $k'; skip2 $k $k'; same2 $k $k'; same2 $k $k'
    skip2 $k $k'
    obtain ⟨HLy, hL, $k:ident⟩ := exc_bind $k
    obtain ⟨HLy', hL', $k':ident⟩ := exc_bind $k'
    have eL : HLy' = HLy := layout_withPol _ $C $th $cap _ hL hL'
    subst eL
    by_cases c4 : ($y).h.p4 = true
    · rw [if_pos c4] at $k:ident $k':ident
      same2 $k $k'
      rest4 $k $k'
    · rw [if_neg c4] at $k:ident $k':ident
      rest4 $k $k'))

/-- **The public part.** Hypotheses: `publicOf` returns X and X' at the two parameter files, with
one scale file and one layout file; hs: the scan of the second is `X.P.withPol C theta cap`. Then X'
is `X.withPol C theta cap`: an equation of whole records. -/
theorem publicOf_withPol {pol pol' KL : ByteArray} {layout : Option ByteArray} {X X' : Public}
    {C theta cap : Nat} (h : publicOf pol KL layout = .ok X) (h' : publicOf pol' KL layout = .ok X')
    (hs : polScan pol' = .ok (X.P.withPol C theta cap)) : X' = X.withPol C theta cap := by
  have hP := publicOf_scan h
  unfold publicOf at h h'
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  obtain ⟨⟨P', y'⟩, h0', h'⟩ := exc_bind h'
  have eP : X.P = P := Except.ok.inj (hP.symm.trans (polLayout_scan h0))
  rw [eP] at hs
  obtain ⟨rfl, rfl⟩ := polLayout_withPol h0 h0' hs
  dsimp only at h h'
  same2 h h'
  skip2 h h'
  skip2 h h'
  by_cases c3 : y'.h.p3 = true
  · rw [if_pos c3] at h h'
    skip2 h h'
    rest3 h h' y' C theta cap
  · rw [if_neg c3] at h h'
    skip2 h h'
    rest3 h h' y' C theta cap

/-- **The head's shape has the scan's three numbers.** Hypothesis: `publicOf` returns X. -/
theorem publicOf_hS {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) :
    X.hS.clipC = X.P.h.clipC ∧ X.hS.theta = X.P.h.theta ∧ X.hS.cap = X.P.h.cap := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-! ### the plan -/

/-- The scan in a plan is the scan of the parameter file: at every digest c. -/
theorem plannedAt_scan {pol KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {p : Verify.Planned} (h : plannedAt pol KL layout c = .ok p) : polScan pol = .ok p.X.P := by
  unfold plannedAt at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact publicOf_scan hX

/-- The head's shape in a plan has the three numbers of the plan's scan: at every digest c. -/
theorem plannedAt_hS {pol KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {p : Verify.Planned} (h : plannedAt pol KL layout c = .ok p) :
    p.X.hS.clipC = p.X.P.h.clipC ∧ p.X.hS.theta = p.X.P.h.theta ∧ p.X.hS.cap = p.X.P.h.cap := by
  unfold plannedAt at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact publicOf_hS hX

/-- **THE LAW.** Hypotheses: h and h': `plannedAt` returns p and p' at the two parameter files, with
one scale file, one layout file and one digest c; hs: the strict scan of the second file is
`p.X.P.withPol C theta cap`. Then the two plans agree but for the three numbers, at the four places
where a plan holds them (the head of this file). -/
theorem plannedAt_withPol {pol pol' KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {p p' : Verify.Planned} {C theta cap : Nat} (h : plannedAt pol KL layout c = .ok p)
    (h' : plannedAt pol' KL layout c = .ok p')
    (hs : polScan pol' = .ok (p.X.P.withPol C theta cap)) :
    p'.X = p.X.withPol C theta cap ∧ p'.cfg = p.cfg ∧ p'.chains = p.chains ∧
      p'.built.links =
        p.built.links.map (headRun (headPlanOf (p.X.withPol C theta cap) default).run) := by
  unfold plannedAt at h h'
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨X', hX', h'⟩ := exc_bind h'
  obtain ⟨ch, hc, h⟩ := exc_bind h
  obtain ⟨ch', hc', h'⟩ := exc_bind h'
  obtain ⟨B, hB, h⟩ := exc_bind h
  obtain ⟨B', hB', h'⟩ := exc_bind h'
  cases h
  cases h'
  obtain rfl : X' = X.withPol C theta cap := publicOf_withPol hX hX' hs
  obtain rfl : ch' = ch := chainsOf_withPol X C theta cap layout c hc hc'
  exact ⟨rfl, rfl, rfl, builtOf_withPol X C theta cap _ hB hB'⟩

/-- The law as one equation: under its hypotheses p' is this record. -/
theorem plannedAt_withPol_eq {pol pol' KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {p p' : Verify.Planned} {C theta cap : Nat} (h : plannedAt pol KL layout c = .ok p)
    (h' : plannedAt pol' KL layout c = .ok p')
    (hs : polScan pol' = .ok (p.X.P.withPol C theta cap)) :
    p' = { X := p.X.withPol C theta cap, cfg := p.cfg, chains := p.chains,
           built := ⟨p.built.links.map
             (headRun (headPlanOf (p.X.withPol C theta cap) default).run)⟩ } := by
  obtain ⟨e1, e2, e3, e4⟩ := plannedAt_withPol h h' hs
  obtain ⟨X', cfg', ch', ⟨l'⟩⟩ := p'
  dsimp only at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rfl

/-- `sansRun` forgets what `headRun` replaced. -/
theorem sansRun_headRun (r : LinkM (Option WsForkOut)) (l : LinkH) :
    sansRun (headRun r l) = sansRun l := rfl

/-- Under the law's hypotheses the two lists of links agree in every field but `run`. -/
theorem plannedAt_withPol_sansRun {pol pol' KL : ByteArray} {layout : Option ByteArray}
    {c : ByteArray} {p p' : Verify.Planned} {C theta cap : Nat}
    (h : plannedAt pol KL layout c = .ok p) (h' : plannedAt pol' KL layout c = .ok p')
    (hs : polScan pol' = .ok (p.X.P.withPol C theta cap)) :
    p'.built.links.map sansRun = p.built.links.map sansRun := by
  rw [(plannedAt_withPol h h' hs).2.2.2, Array.map_map]
  rfl

/-- The law at 32 zero bytes in the digest's place. -/
theorem planZero_withPol {pol pol' KL lay : ByteArray} {p p' : Verify.Planned}
    {C theta cap : Nat} (h : planZero pol KL lay = .ok p) (h' : planZero pol' KL lay = .ok p')
    (hs : polScan pol' = .ok (p.X.P.withPol C theta cap)) :
    p'.X = p.X.withPol C theta cap ∧ p'.cfg = p.cfg ∧ p'.chains = p.chains ∧
      p'.built.links =
        p.built.links.map (headRun (headPlanOf (p.X.withPol C theta cap) default).run) :=
  plannedAt_withPol h h' hs

end OnBytes.Tie

#print axioms OnBytes.Tie.lookup_map_keep
#print axioms OnBytes.Tie.value_withPol
#print axioms OnBytes.Tie.layerShape_withPol
#print axioms OnBytes.Tie.headRun_arrayOf
#print axioms OnBytes.Tie.declareOwn_headRun
#print axioms OnBytes.Tie.foreign_headRun
#print axioms OnBytes.Tie.fold_headRun
#print axioms OnBytes.Tie.linksOf_withPol
#print axioms OnBytes.Tie.forIn_two
#print axioms OnBytes.Tie.declareLinks_headRun
#print axioms OnBytes.Tie.shapesWith_withPol
#print axioms OnBytes.Tie.shapesOf_withPol
#print axioms OnBytes.Tie.chainsOf_withPol
#print axioms OnBytes.Tie.builtOf_withPol
#print axioms OnBytes.Tie.polLayout_withPol
#print axioms OnBytes.Tie.layout_withPol
#print axioms OnBytes.Tie.publicOf_withPol
#print axioms OnBytes.Tie.publicOf_hS
#print axioms OnBytes.Tie.plannedAt_scan
#print axioms OnBytes.Tie.plannedAt_hS
#print axioms OnBytes.Tie.plannedAt_withPol
#print axioms OnBytes.Tie.plannedAt_withPol_eq
#print axioms OnBytes.Tie.sansRun_headRun
#print axioms OnBytes.Tie.plannedAt_withPol_sansRun
#print axioms OnBytes.Tie.planZero_withPol
