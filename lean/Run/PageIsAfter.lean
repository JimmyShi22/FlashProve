-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsAfter.lean: this file proves `Spec.pi_after` (Run/PageIs.lean). That statement speaks of
the parser's argument string and takes what the chain yields as given. Under the hypotheses of that
statement the strict format holds on that string. Under the same hypotheses, on that string, what
follows the chain is "every opening walks to the root sent, the test bits pass, and dec says yes on
the view of what the lenient reader handed out".

The evaluable form of the compiled verifier (`verifyP`, Run/ThinDefs.lean) has three stages: the
hash chain (`chainP`), a test on the form of the argument string (`strictP`, the strict format), and
what follows the chain (`afterP`): bounds on the number and the depths of the checks, the checks of
the Merkle openings (and of the request tree, where the chain has joined) and the protocol's
`accept`. The parser's argument string is the string that the lenient parser makes of the reader's
output (`mkBPrfP`, Run/ParseThin.lean).

Main names (each under the hypotheses of its statement):
  `strict_top`: the first half: the first salt has 256 bits; no root is left over; an opening stands
    only under a root, only where the verifier reads, with a salt of the right length
    (`strict_ind`); no external opening, slot 0, no path.
  `after_top`: the second half; no request tree before the chain has joined.
  `pi_after`: the two halves together.

Notation:
  `o`: a chain as read (`ChainOut`, Fmt/Rules8.lean);
  `LaxFacts`: a `Prop` on `h`, `S`, `o`: what the lenient reader's output is (Run/PageIs.lean);
  `uL C ds`: the shape of the rounds after the round in front (Run/PlanQS.lean);
  `pl`: the plain parts of all prover messages (`Plains (uL C (rds S))`, Iop/Shape.lean);
  `ρ`: the verifier's randomness of a whole execution (`Rho (uL C (rds S))`, Iop/Shape.lean);
  `v`: the bits in `.loc v`, where the chain of a slot stands (`Phase`,
    Compile/Batch/Verifier.lean);
  `dec`: a decision: a function `View → Bool`.

Limits: what the head of Run/PageIs.lean leaves out is not said here either; see chiefly its 4,
"What is not claimed".
Terms: lean/GLOSSARY.md.
-/
import Run.PageIsRows
import Run.PageIsViewProofs
import Run.PageIsTopProofs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- No opening of a trace (`TraceL`, Run/PageIs.lean) has an empty list. -/
theorem opens_ne (h : HId) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → ∀ ro ∈ ros, ∀ x ∈ ro.opens, x.2.1 ≠ []
  | [], [], _, _, _, ro, hro, _, _ => absurd hro (List.not_mem_nil)
  | r :: rs, ro' :: ros, c, roots, t, ro, hro, x, hx => by
    obtain ⟨-, -, -, -, ho, t'⟩ := t
    rcases List.mem_cons.1 hro with rfl | hro
    · obtain ⟨y, -, hy⟩ := forall2_right ho x hx
      exact (WalkTie.listOK_spec _ _ hy.okl).1
    · exact opens_ne h P rs ros _ _ t' ro hro x hx
  | [], _ :: _, _, _, t, _, _, _, _ => t.elim
  | _ :: _, [], _, _, t, _, _, _, _ => t.elim

section
variable (h : HId) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- Under `hok`, `hf` and `hd`: the hypothesis round by round (`RowsL`, Run/PageIsForest.lean) holds
of what the lenient reader hands out, "read" being the protocol's own set of positions read. -/
theorem rows_top (o : ChainOut) (ρ : Rho (uL C (rds S))) (pls : Plains (up (SOf C (rds S))))
    (hok : ok S = true) (hf : LaxFacts h S o)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    RowsL C (opensB o) S.plan.salt (rds S) o.rounds.toList (fun q =>
      @decide (Sum.inr q ∈ (PSof C (rds S) dec).reads () (default, ρ) pls)
          (@Finset.decidableMem _ (decOS C (rds S)) _ _)) := by
  refine rows_ind C (opensB o) S.plan.salt
    (fun n y => (n, y) ∈ wanted (rds S) (o.rounds.toList.map (·.drawn))) (rds S) o.rounds.toList 0 _
    (pi_sent h S o hok hf) (fun n sh hs => ?_) fun q => ?_
  · rcases pi_row h S o hok hf n sh hs with ⟨x, row⟩ | bare
    · obtain ⟨ro, hro, hx⟩ := row.mem
      have hsh := row.shape
      subst hsh
      exact Or.inl
        ⟨obOf x, row.look, rfl,
          opens_ok h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx,
          opens_ne h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx,
          fun y => by rw [Nat.zero_add]; exact row.want y⟩
    · exact Or.inr ⟨bare.look, fun y => by rw [Nat.zero_add]; exact bare.want y⟩
  · rw [decide_eq_true_iff]
    show Sum.inr q ∈
        (((wanted (rds S) (drawnSL C (rds S) ρ)).filterMap fun nx =>
          (posAtS C (rds S) nx.1 nx.2).map fun p =>
            (Sum.inr p : OPos (Twin.up (SOf C (rds S)))))).toFinset ↔
      _
    rw [List.mem_toFinset, List.mem_filterMap, hd]
    constructor
    · rintro ⟨⟨n, y⟩, hw, hp⟩
      obtain ⟨q', hq', hq⟩ := Option.map_eq_some_iff.1 hp
      exact ⟨n, y, by rw [Nat.zero_add]; exact hw, by rw [hq', Sum.inr.inj hq]⟩
    · rintro ⟨n, y, hw, hp⟩
      exact ⟨(n, y),
        by rw [Nat.zero_add] at hw; exact hw,
        by show (posAtS C (rds S) n y).map _ = _; rw [hp]; rfl⟩

end

/-- The chain's roots, counted: as many as the roots among the items read, if the rounds go together
(`SentRel`, Run/PageIsRows.lean). -/
theorem cntP_rt (C : CK) :
    ∀ (ds : List RD) (ros : List RoundOut), List.Forall₂ SentRel ds ros →
      cntP (SL C ds) (rtSL C ds ros) = (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length
  | [], _, .nil => rfl
  | d :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    have ih := cntP_rt C ds ros ht
    show (0 + ((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig).toList.length +
        cntP (SL C ds) (rtSL C ds ros)) = _
    rw [ih, List.flatMap_cons, List.length_append]
    rcases hs with ⟨-, hv⟩ | ⟨-, r, -, hv⟩ <;> rw [hv] <;> rfl

section
variable (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

theorem run_size (hO : ∀ s, (O s).size = 32) (o : ChainOut) (run : ByteArray)
    (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run) : run.size = 32 := by
  obtain ⟨rnd, -, hr'⟩ := hf.run
  rw [Option.some.inj (hr.symm.trans hr')]
  exact size_HO O hO 172 _ _ _ _

/-- Under the hypotheses below, the strict format holds on the parser's argument string. -/
theorem strict_top (hO : ∀ s, (O s).size = 32) (hok : ok S = true) (o : ChainOut) (run : ByteArray)
    (pl : Plains (uL C (rds S))) (ρ : Rho (uL C (rds S))) (v : Bits)
    (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) 0 ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some none), rtSL C (rds S) o.rounds.toList) (.loc v) = true := by
  have hrun := run_size O S hO o run hf hr
  unfold strictP
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show decide ((bytesToBits run).length = 256) = true
    rw [length_bytesToBits, hrun]
    rfl
  · show decide (((rootsB o).map bytesToDig).length ≤
          0 + 0 + cntP (SL C (rds S)) (rtSL C (rds S) o.rounds.toList)) = true
    rw [cntP_rt C (rds S) o.rounds.toList (pi_sent _ S o hok hf), List.length_map]
    exact decide_eq_true (Nat.le_of_eq (by simp only [Nat.zero_add]; rfl))
  · have := strict_ind C K chal (opensB o) run S.plan.salt hrun (rds S) o.rounds.toList _
      (rows_top (_root_.Fmt.HO O) S C dec o ρ
        (effsP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
          ((none, some none), rtSL C (rds S) o.rounds.toList) ((), pl))
        hok hf hd)
    show (sCompP _ (s0 C) (fun _ => none) 0 _ _ _ && sCompP _ (s0 C) (fun _ => none) 0 _ _ _ &&
        sSP (256 + 8 * S.plan.salt) (SL C (rds S)) (allLo (SL C (rds S))) (wiresSL C K chal (rds S))
          (rtSL C (rds S) o.rounds.toList) _ _) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨List.all_eq_true.2 fun _ _ => rfl, List.all_eq_true.2 fun _ _ => rfl⟩, this⟩
  · rfl
  · rfl
  · rfl


/-- Under `hc`, the trivial round in front makes no forest. -/
theorem forestsP_front {I X : Type} {L : BatchProtocol I X} (ds : List RD)
    (emb : (p : OPos (up (SOf C ds))) → OSym (up (SOf C ds)) p → Body L) (rts : RootsOfChain 256 (uL C ds))
    (isRead : OPos (up (SOf C ds)) → Bool)
    (f : (p : OPos (up (SOf C ds))) → Option (Opening 256 (OSym (up (SOf C ds)) p)))
    (c : List (Forest 256 L))
    (hc : forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
        (fun p => emb (.inr p)) rts (fun p => isRead (.inr p)) (fun p => f (.inr p)) = some c) :
    forestsP (fun _ => L) (SOf C ds) (allLo (SOf C ds)) (wire0S C K chal, wiresSL C K chal ds) emb
        ((none, some none), rts) isRead f = some c := by
  simp only [forestsP]
  split
  · rename_i a b c' e1 e2 e3
    have ea : a = [] := Option.some.inj (e1.symm.trans rfl)
    have eb : b = [] := Option.some.inj (e2.symm.trans rfl)
    have ec : c' = c := Option.some.inj (e3.symm.trans hc)
    subst ea eb ec
    rfl
  · rename_i hne
    exact (hne [] [] c rfl rfl hc).elim

/-- What follows the chain: under the hypotheses below it equals the conjunction of three tests:
`rootsAll`, "the test bits pass" (`passSL`), and dec on the view of o. -/
theorem after_top (hO : ∀ s, (O s).size = 32) (hok : ok S = true) (o : ChainOut) (run : ByteArray)
    (pl : Plains (uL C (rds S))) (ρ : Rho (uL C (rds S))) (v : Bits)
    (hf : LaxFacts (_root_.Fmt.HO O) S o) (hr : o.run = some run)
    (hp : plainsSL C (rds S) o.rounds.toList = some pl)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    afterP (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) (PSof C (rds S) dec)
        (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
        (fun s => some (.inl s)) 0 [bytesToDig o.pd] ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some none), rtSL C (rds S) o.rounds.toList) (.loc v) =
      (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList &&
        (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o))) := by
  have hrun := run_size O S hO o run hf hr
  obtain ⟨Fs, g1, g2, g3, g4⟩ :=
    forests_ind (L := LbS C (rds S) dec) O (PDS S C dec) C K chal (opensB o) run S.plan.salt hO hrun
      (rds S) o.rounds.toList _ (fun s => ⟨.inr s.1, s.2⟩)
      (rows_top (_root_.Fmt.HO O) S C dec o ρ
        (effsP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
          ((none, some none), rtSL C (rds S) o.rounds.toList) ((), pl))
        hok hf hd) (fun s => rfl)
  have hFo : forestsOfP (fun _ => LbS C (rds S) dec) (PSof C (rds S) dec) (wqS C K chal (rds S) dec)
        (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (fun s => some (.inl s)) [bytesToDig o.pd] ()
        (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
        (default, ρ) ((none, some none), rtSL C (rds S) o.rounds.toList) =
      some (Fs ++ []) := by
    unfold forestsOfP
    dsimp only
    split
    · rename_i a b e1 e2
      have ea : a = Fs :=
        Option.some.inj (e1.symm.trans (forestsP_front C K chal (rds S) _ _ _ _ Fs g1))
      have eb : b = [] := Option.some.inj (e2.symm.trans rfl)
      rw [ea, eb]
    · rename_i hne
      exact (hne Fs [] (forestsP_front C K chal (rds S) _ _ _ _ Fs g1) rfl).elim
  unfold afterP
  rw [hFo]
  dsimp only
  rw [List.append_nil, if_pos ⟨by rw [g2]; exact cnt_le _ S o hok hf, List.all_eq_true.2 fun c hc => by
    obtain ⟨w, d, hdm, hdd⟩ := g3 c hc
    rw [Bool.and_eq_true]
    exact ⟨w, decide_eq_true
        (by rw [hdd]; exact (foldl_max_le (fun d => depthOf d.tree) (rds S) 0).2 d hdm)⟩⟩]
  have h4 := g4 [] []
  rw [List.append_nil, List.append_nil] at h4
  rw [h4, tree_roots O S C dec o run hok hf]
  refine Eq.trans ?_
    (congrArg (fun b => rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && b)
      (pi_view (_root_.Fmt.HO O) S C K chal dec hok o run pl ρ
        ((wqS C K chal (rds S) dec).ext.build fun _ => none) hf hr hp hd))
  show (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList && true && true && _) = _
  rw [Bool.and_true, Bool.and_true]
  rfl

theorem pi_after : Spec.pi_after := fun O hO S C K chal dec hok o run pl ρ v hf hr hp hd =>
  ⟨strict_top O S C K chal dec hO hok o run pl ρ v hf hr hd,
    after_top O S C K chal dec hO hok o run pl ρ v hf hr hp hd⟩

end

end Run.PQ
