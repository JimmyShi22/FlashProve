-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsTopProofs.lean: the proof of the statement of Run/PageIsTop.lean, and of one part of
Run/PageIs.lean, `pi_typed`.

Run/PageIs.lean compares two verifiers of a proof file, the compiled verifier behind a lenient
reader and the format's strict verifier; it states four main statements and six parts.

Main names:
  `pi_typed`: proves `Spec.pi_typed`: the parser's last step does not refuse on what the lenient
    reader hands out. Under `ok S = true`, which the proof does not use, and `LaxFacts h S o`,
    `toBPrfP` gives an argument string.
  `pi_top`: proves `Spec.pi_top` (Run/PageIsTop.lean), from the four steps `formula_of`, `kits_of`,
    `half_of`, `core_of`.

Limits: `pi_top` is a conditional statement. What it does not claim is told in the head of
Run/PageIsTop.lean, under 4.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsTop
import Run.LaxDomProofs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-! ### The parser's last step does not refuse on what the lenient reader hands out (`LaxFacts`) -/

/-- A message's items, read, can be typed: if `Fmt.readItems f l b i = some (g, j)`, then
`PlainOf.ofGots l g` is some p. -/
theorem ofGots_read (f : _root_.Fmt.Fld) :
    ∀ (l : List _root_.Fmt.Item) (b : ByteArray) (i : ℕ) (g : List _root_.Fmt.ItemValue) (j : ℕ),
      _root_.Fmt.readItems f l b i = some (g, j) → ∃ p, PlainOf.ofGots l g = some p
  | [], _, _, g, _, e => by
    simp only [_root_.Fmt.readItems, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]
    exact ⟨(), rfl⟩
  | t :: ts, b, i, g, j, e => by
    simp only [_root_.Fmt.readItems] at e
    split at e
    · rename_i x k e1
      split at e
      · rename_i l' k' e2
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨p, hp⟩ := ofGots_read f ts b k l' k' e2
        rw [← e.1]
        cases t <;> simp only [_root_.Fmt.readItem, Option.map_eq_some_iff] at e1
          <;> obtain ⟨y, -, hy⟩ := e1 <;> cases hy
          <;> simp only [PlainOf.ofGots, hp, Option.map_some] <;> exact ⟨_, rfl⟩
      · cases e
    · cases e

theorem ofGots_whole (f : _root_.Fmt.Fld) (l : List _root_.Fmt.Item) (b : ByteArray)
    (g : List _root_.Fmt.ItemValue) (e : _root_.Fmt.whole (_root_.Fmt.readItems f l) b = some g) :
    ∃ p, PlainOf.ofGots l g = some p := by
  unfold _root_.Fmt.whole at e
  split at e
  · rename_i x j e1
    split at e
    · cases e
      exact ofGots_read f l b 0 _ j e1
    · cases e
  · cases e

theorem plainsSL_some (h : HId) (S : _root_.Fmt.Spec) (C : CK) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round)
        (ros : List RoundOut) (c : Chain) (roots : Array ByteArray) (sent : ℕ),
      TraceL h P rs ros c roots → ∃ pl, plainsSL C (rdsFrom S sent rs) ros = some pl
  | [], [], _, _, _, _ => ⟨(), rfl⟩
  | r :: rs, ro :: ros, c, roots, sent, t => by
    obtain ⟨-, hv, -, -, -, t'⟩ := t
    obtain ⟨p, hp⟩ := ofGots_whole P.field r.items ro.msg ro.vals hv
    obtain ⟨pl, hpl⟩ := plainsSL_some h S C P rs ros _ _ (sent + r.entry.roots) t'
    refine ⟨(GPlain.mk r.entry.work p ro.nonce, pl), ?_⟩
    simp only [rdsFrom, plainsSL, hp, hpl]
  | [], _ :: _, _, _, _, t => t.elim
  | _ :: _, [], _, _, _, t => t.elim


theorem forall2_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, y, hy => absurd hy (List.not_mem_nil)
  | _, _, .cons (a := a) hab ht, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨x, hx, hr⟩ := forall2_right ht y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- Under `TraceL h P rs ros c roots`: every opening of a trace passes the parser's own test
(`OpenB.ok`). -/
theorem opens_ok (h : HId) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots →
      ∀ ro ∈ ros, ∀ x ∈ ro.opens,
        (⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩ : OpenB).ok P.salt x.1.W = true
  | [], [], _, _, _, ro, hro, _, _ => absurd hro (List.not_mem_nil)
  | r :: rs, ro' :: ros, c, roots, t, ro, hro, x, hx => by
    obtain ⟨-, -, -, -, ho, t'⟩ := t
    rcases List.mem_cons.1 hro with rfl | hro
    · obtain ⟨y, -, hy⟩ := forall2_right ho x hx
      rw [hy.sh]
      exact hy.okb
    · exact opens_ok h P rs ros _ _ t' ro hro x hx
  | [], _ :: _, _, _, t, _, _, _, _ => t.elim
  | _ :: _, [], _, _, t, _, _, _, _ => t.elim

theorem pi_typed' (h : HId) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)
    (o : ChainOut) (hf : LaxFacts h S o) :
    ∃ (run : ByteArray) (pl : Plains (uL C (rds S))),
      o.run = some run ∧
      plainsSL C (rds S) o.rounds.toList = some pl ∧
      toBPrfP (PSof C (rds S) dec) (TYS S C dec) o =
        some ([bytesToDig o.pd],
            mkBPrfP (PSof C (rds S) dec) run (rootsB o)
              ((), pl) (opensAt (TYS S C dec).up run o)) := by
  obtain ⟨rnd, -, hr⟩ := hf.run
  obtain ⟨pl, hpl⟩ : ∃ pl, plainsSL C (rds S) o.rounds.toList = some pl :=
    plainsSL_some h S C S.plan S.rounds o.rounds.toList _ _ 0 hf.trace
  refine ⟨_, pl, hr, hpl, ?_⟩
  rw [parseThin_to]
  refine (parseLaws_some (TYS S C dec).up o _).2 ⟨_, ((), pl), hr, ?_, ?_, rfl⟩
  · show (plainsSL C (rds S) o.rounds.toList).map (fun r => ((), r)) = some ((), pl)
    rw [hpl]
    rfl
  · rw [List.all_eq_true]
    intro y hy
    obtain ⟨ro, hro, hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact opens_ok h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx


/-! ### The four main statements, from the parts -/

theorem size_HO (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (n t i : ℕ) (s b : ByteArray) :
    ByteArray.size (_root_.Fmt.HO O n t i s b) = _root_.Fmt.dlen n := by
  unfold _root_.Fmt.HO _root_.Fmt.dlen
  split
  · rw [ByteArray.size_append, hO, hO]
  · exact hO _

theorem formula_of (hF : Spec.pi_facts) (hC : Spec.pi_chain) (hA : Spec.pi_after) :
    Spec.pi_formula := by
  intro O S C K chal dec file fit
  unfold laxV parseLaxWP
  simp only [idb, idp]
  cases hl : laxWhole (m := Id) (_root_.Fmt.HO O) S file with
  | none => rfl
  | some o =>
    have hf : LaxFacts (_root_.Fmt.HO O) S o := hF _ (size_HO O fit.size) S file o fit.ok hl
    obtain ⟨run, pl, hr, hp, ht⟩ := pi_typed' (_root_.Fmt.HO O) S C dec o hf
    obtain ⟨ρ, v, hc, hd, hps⟩ :=
      hC O fit.size S C K chal dec fit.ok fit.kit fit.room o run pl hf hr hp
    obtain ⟨a1, a2⟩ := hA O fit.size S C K chal dec fit.ok o run pl ρ v hf hr hp hd
    show (match toBPrfP (PSof C (rds S) dec) (TYS S C dec) o with
      | some ([cm], π) => VO O S C K chal dec cm π
      | _ => false) = _
    rw [ht]
    show VO O S C K chal dec (bytesToDig o.pd) _ = _
    unfold VO verifyP
    have hc' : chainP (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) id none .onl
          [bytesToDig o.pd] ((some : Unit → Option Unit) ())
          (mkBPrfP (PSof C (rds S) dec) run (rootsB o)
            ((), pl) (opensAt (TYS S C dec).up run o)).salt
          (mkBPrfP (PSof C (rds S) dec) run (rootsB o)
            ((), pl) (opensAt (TYS S C dec).up run o)).rtreq
          (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh
          (embPS C (rds S) dec) 0 .first
          (mkBPrfP (PSof C (rds S) dec) run (rootsB o)
            ((), pl) (opensAt (TYS S C dec).up run o)).roots
          (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl)
            (opensAt (TYS S C dec).up run o)).plains =
        some ((default, ρ), ((none, some none), rtSL C (rds S) o.rounds.toList), .loc v) := hc
    rw [hc']
    dsimp only
    rw [a1, if_pos rfl, a2, hps, hr]
    show _ = (_ && rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && _)
    cases passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩
      <;> cases rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList <;> rfl

theorem kits_of (hM : Spec.pi_formula) : Spec.pi_kits :=
  fun O S C K chal C' K' chal' dec file f f' =>
    (hM O S C K chal dec file f).trans (hM O S C' K' chal' dec file f').symm

theorem half_of (hM : Spec.pi_formula) (h1 : Spec.pi_strict1) : Spec.pi_half := by
  intro O S C K chal dec file fit hv
  rw [hM O S C K chal dec file fit]
  unfold _root_.Fmt.verifyW at hv
  simp only [idb] at hv
  cases hw : _root_.Fmt.wholeChain (m := Id) (_root_.Fmt.HO O) S file with
  | none => rw [hw] at hv; cases hv
  | some o' =>
    rw [hw] at hv
    obtain ⟨o, run, hl, hr, hview, hp, hro⟩ := h1 _ (size_HO O fit.size) S file o' fit.ok hw
    rw [hl]
    show (_ && rootsAll (_root_.Fmt.HO O) S.cfg (o.run.getD default) o.rounds.toList && _) = true
    rw [hp, hr, hview]
    show (true && rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && _) = true
    rw [hro]
    exact hv

theorem core_of (hM : Spec.pi_formula) (hF : Spec.pi_facts)
    (h1 : Spec.pi_strict1) (h2 : Spec.pi_strict2) : Spec.pi_core := by
  intro O S C K chal dec file fit hd
  cases hv : _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO O) S (fun (_ : Unit) => dec) () file with
  | true => exact half_of hM h1 O S C K chal dec file fit hv
  | false =>
    rw [hM O S C K chal dec file fit]
    cases hl : laxWhole (m := Id) (_root_.Fmt.HO O) S file with
    | none => rfl
    | some o =>
      obtain ⟨rnd, -, hr⟩ := (hF _ (size_HO O fit.size) S file o fit.ok hl).run
      show (passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ &&
          rootsAll (_root_.Fmt.HO O) S.cfg (o.run.getD default) o.rounds.toList &&
          dec (_root_.Fmt.viewOf S.firstTree o)) = false
      rw [hr]
      show (passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ &&
          rootsAll (_root_.Fmt.HO O) S.cfg
            (_root_.Fmt.HO O 172 0 S.label _root_.Fmt.zero32 (o.pd ++ rnd)) o.rounds.toList &&
          dec (_root_.Fmt.viewOf S.firstTree o)) = false
      cases hp : passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ with
      | false => rfl
      | true =>
        cases hro : rootsAll (_root_.Fmt.HO O) S.cfg
            (_root_.Fmt.HO O 172 0 S.label _root_.Fmt.zero32 (o.pd ++ rnd)) o.rounds.toList with
        | false => rfl
        | true =>
          obtain ⟨o', hw, hview⟩ := h2 _ (size_HO O fit.size) S file o _ fit.ok hl hr hp hro hd
          unfold _root_.Fmt.verifyW at hv
          simp only [idb] at hv
          rw [hw] at hv
          rw [← hview]
          exact hv

theorem pi_typed : Spec.pi_typed := fun h S C dec o _ hf => pi_typed' h S C dec o hf

theorem pi_top : Spec.pi_top := fun hF h1 h2 hC hA =>
  ⟨formula_of hF hC hA,
    half_of (formula_of hF hC hA) h1,
    core_of (formula_of hF hC hA) hF h1 h2,
    kits_of (formula_of hF hC hA)⟩

end Run.PQ
