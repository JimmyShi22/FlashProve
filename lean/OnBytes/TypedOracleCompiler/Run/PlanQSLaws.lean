-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQSLaws.lean: THE GENERIC PROTOCOL WITH A LIST OF TREES A ROUND IS LOCAL, AND ITS
WIRING, MADE BY THE MAKER, OBEYS OnBytes/TypedOracleCompiler's LAWS. After the library's Run/PlanQSLaws.lean and
Run/PlanQWireLaws.lean (ChalUnif, DrawnFits, share_len, foldl_max_le), declaration for declaration.
  TURNED BY MATTER     colAtS_congr, wireS_okg, wire0S_okg, depthSL, wqS_okg (its clause depth)
  NEW                  le_depthOf; d1 (a round's data without its trees, as the LIBRARY's RD)
  SAID AGAIN AS TEXT   ChalUnif, DrawnFits, share_len, foldl_max_le (here for any type), psof_up,
                       rhoS_eq, rvS_congr,
                       viewS_congr, psof_local, wiresS_okg, wantedSL_len, and the statements Spec.*
  LEFT TO THE LIBRARY unif_unique, filterMap_congr_mem, Twin.allLo_eq, Fmt.listOf_len; AND THE
                       LIBRARY's OWN wireS_okg, AS A BLACK BOX: that uniform blocks give a uniform
                       verifier message, test bits among them, and that the test's record is a lens,
                       hang on a round's entry, kind and items alone, not on its trees: both clauses
                       are taken from the library's theorem at d1 d.
  GONE                 wireS_eq, shapeS_eq (ties to the road without skeletons, which is not said)
  two_trees            the key's shared chain's round in shape: two roots, depths 21 | 12, columns
                       of 36 | 3 words:
                       the maker's wire has depthJ = [21, 12]; the whole wiring is lawful under the
                       library's own three hypotheses.
A LIMIT THAT WEIGHS (the library's own head): ChalUnif is an equation of laws:
uniform blocks give an EXACTLY uniform verifier message. With challenges as sampled values it is
FALSE for every round that draws a field element: wqS_okg cannot be applied there. It holds with
challenges as hash blocks: Run/PlanPull.lean (planPull_okg; two_trees_closed). two_trees says depthJ
= [21, 12] AND NO MORE: it has no OKG in it.
psof_local and psof_up have NO hypothesis. No law knows maxRt, nor that d.trees.length is the number
of d.items' roots: wqS_okg holds at a round of three trees, where the compiled verifier rejects
every string (takeRt), and rcL writes a query only where the two numbers agree (toRoots).
THE BLACK BOX SPARES Iop/GrindWire AND THE ROAD WITHOUT SKELETONS FOR OKG ALONE: gone with wireS_eq
| shapeS_eq are: that PSof is a InteractiveOracleProof.grind of anything (so what work does to a round's error), and
the ties of the pull (how soundness passes from sampled values to blocks).
NO STATEMENT ON SOUNDNESS. Nothing on how queries are spelled, on a parser, on the hash or on a
file.

Terms: lean/GLOSSARY.md.

-/
import Run.PlanQSLaws
import OnBytes.TypedOracleCompiler.Run.PlanQS

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Run.Twin (RS PS)

/-- uniform blocks give a uniform verifier's message, in every round -/
def ChalUnif (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) :
    Prop :=
  ∀ d ∈ ds, (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind)

/-- what was drawn holds at most the entry's number of positions -/
def DrawnFits (C : CK) (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ c, (C.dr d.entry d.kind c).poss.length ≤ d.entry.poss

namespace Spec

/-- THE PROTOCOL THAT RUNS IS THE TEST OF ITS OWN INTERFACE. -/
def psof_up : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool),
    (PSof C ds dec).up = BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline

def viewS_congr : Prop :=
  ∀ (C : CK) (ds : List RD) (τ τ' : Iop.Tr (uL C ds)), τ.rho = τ'.rho → τ.plains = τ'.plains →
    (∀ nx ∈ wanted ds (drawnSL C ds τ.rho),
      ∀ p, posAtS C ds nx.1 nx.2 = some p → τ.read p = τ'.read p) →
    viewSL C ds τ = viewSL C ds τ'

/-- THE VERIFIER IS LOCAL. -/
def psof_local : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool), (PSof C ds dec).up.loc.IsLocal

/-- THE WIRING OBEYS THE LAWS. -/
def wqS_okg : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (ds : List RD) (dec : View → Bool),
    ChalUnif C K chal ds → DrawnFits C ds →
    (∀ d ∈ ds, d.entry.work ≤ 64) → (wqS C K chal ds dec).OKG

end Spec

/-! ## The protocol is the interface's Test -/

theorem psof_up : Spec.psof_up := fun C ds dec =>
  congrArg (BatchInteractiveOracleProof.mk (PSof C ds dec).up.loc) (Twin.allLo_eq (SOf C ds))

/-! ## The verifier is local -/

theorem rhoS_eq (C : CK) : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)), rhoSL C ds τ = τ.rho
  | [], _ => rfl
  | _ :: ds, (_, c, τ) => congrArg (Prod.mk c) (rhoS_eq C ds τ)

theorem rvS_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Iop.Tr (uL C ds)),
      τ.rho = τ'.rho → τ.plains = τ'.plains → rvSL C ds τ = rvSL C ds τ'
  | [], _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), hρ, hp => by
      have e1 : c = c' := congrArg Prod.fst hρ
      have e2 : τ.rho = τ'.rho := congrArg Prod.snd hρ
      have e3 : m.2 = m'.2 := congrArg Prod.fst hp
      have e4 : τ.plains = τ'.plains := congrArg Prod.snd hp
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: rvSL C ds τ =
        ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m'.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c')⟩ :: rvSL C ds τ'
      rw [e1, e3, rvS_congr C ds τ τ' e2 e4]

theorem colAtS_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Iop.Tr (uL C ds)) (n x : Nat),
      (∀ p, posAtS C ds n x = some p → τ.read p = τ'.read p) →
      colAtS C ds τ n x = colAtS C ds τ' n x
  | [], _, _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), n, x, h => by
      unfold colAtS
      unfold posAtS at h
      by_cases hn : n < d.trees.length
      · rw [if_pos hn, if_pos hn]
        rw [if_pos hn] at h
        cases hp : posAtT d.trees n x with
        | none => rfl
        | some p =>
          rw [hp] at h
          have e : m.1 p = m'.1 p := h (.inl p) rfl
          show some (colT d.trees p (m.1 p)) = some (colT d.trees p (m'.1 p))
          rw [e]
      · rw [if_neg hn, if_neg hn]
        rw [if_neg hn] at h
        refine colAtS_congr C ds τ τ' (n - d.trees.length) x fun p hp => ?_
        exact h (.inr p) (by rw [hp]; rfl)

theorem viewS_congr : Spec.viewS_congr := by
  intro C ds τ τ' hρ hp hr
  unfold viewSL
  rw [rvS_congr C ds τ τ' hρ hp, rhoS_eq, rhoS_eq, ← hρ]
  congr 1
  refine filterMap_congr_mem _ _ _ fun nx hnx => ?_
  rw [colAtS_congr C ds τ τ' nx.1 nx.2 (hr nx hnx)]

theorem psof_local : Spec.psof_local := by
  rintro C ds dec x y y' ⟨m0, c0, τ⟩ ⟨m0', c0', τ'⟩ hρ hp _ hr
  have e1 : τ.rho = τ'.rho := congrArg Prod.snd hρ
  have e2 : τ.plains = τ'.plains := congrArg Prod.snd hp
  show (passSL C ds (rhoSL C ds τ) && dec (viewSL C ds τ)) =
    (passSL C ds (rhoSL C ds τ') && dec (viewSL C ds τ'))
  rw [rhoS_eq, rhoS_eq, ← e1, viewS_congr C ds τ τ' e1 e2 fun nx hnx p hpos => ?_]
  refine hr (Sum.inr p) ?_
  show (Sum.inr p : OPos (Twin.up (SOf C ds))) ∈
    (((wanted ds (drawnSL C ds τ.rho)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨nx, hnx, by rw [hpos]; rfl⟩

/-! ## The wiring -/

/-- TWO: a round's data without its trees, as the library's: entry, kind and items are kept -/
def d1 (d : RD) : _root_.Run.PQ.RD := ⟨d.entry, d.kind, d.items, none, []⟩

theorem wireS_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
    (hw : d.entry.work ≤ 64) : (wireS C K chal d).OKG where
  place_lt0 := fun _ h => by cases h
  place_ltJ := fun p _ => placeT_lt d.trees p
  posAt0_place := fun _ h => by cases h
  posAtJ_place := fun p _ => posAtT_place d.trees p
  place_posAt0 := fun _ _ _ h => by cases h
  place_posAtJ := fun k j p h => ⟨rfl, place_posAtT d.trees k j p h⟩
  no0 := fun _ _ _ => rfl
  noJ := fun k hk j => posAtT_none d.trees k (by simpa [wireS] using hk) j
  chal_unif := (_root_.Run.PQ.wireS_okg C K chal (d1 d) hc hw).chal_unif
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun g e => by
    obtain ⟨g', hg, rfl⟩ := Option.map_eq_some_iff.1 e
    exact Tagged.ofGr_ok ((_root_.Run.PQ.wireS_okg C K chal (d1 d) hc hw).grJ_ok g' hg)

theorem wire0S_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (wire0S C K chal).OKG :=
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ _ h => by cases h
    place_posAtJ := fun _ _ _ h => by cases h
    no0 := fun _ _ _ => rfl, noJ := fun _ _ _ => rfl, chal_unif := unif_unique _
    gr0_ok := fun _ e => by cases e
    grJ_ok := fun _ e => by cases e }

theorem wiresS_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
  | [], _, _ => trivial
  | d :: ds, hc, hw =>
    ⟨wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wiresS_okg C K chal ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

/-- one round's share -/
theorem share_len (all : List RD) (opens : List Nat) (D : _root_.Fmt.Drawn)
    (n : Nat) (h : D.poss.length ≤ n) :
    (opens.flatMap fun t => match treeSh all t with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (t, x)).length ≤ n *
          opens.length := by
  induction opens with
  | nil => simp
  | cons t ts ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ, Nat.add_comm]
      refine Nat.add_le_add ih ?_
      cases treeSh all t with
      | none => exact Nat.zero_le _
      | some s =>
          show ((_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (t, x)).length ≤ n
          rw [List.length_map]
          exact le_trans (_root_.Fmt.listOf_len _) (by rw [List.length_map]; exact h)

theorem wantedSL_len (C : CK) (all : List RD) :
    ∀ (ds : List RD),
      DrawnFits C ds → ∀ ρ : Rho (uL C ds), (wantedL all ds (drawnSL C ds ρ)).length ≤ nOpen ds
  | [], _, _ => Nat.le_refl _
  | d :: ds, h, (c, ρ) => by
      show (_ ++ wantedL all ds (drawnSL C ds ρ)).length ≤
        (d.entry.poss * d.opens.length :: ds.map fun d => d.entry.poss * d.opens.length).sum
      rw [List.length_append, List.sum_cons]
      exact Nat.add_le_add (share_len all d.opens _ _ (h d List.mem_cons_self _))
        (wantedSL_len C all ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ)

theorem foldl_max_le {α : Type} (f : α → Nat) :
    ∀ (ds : List α) (a : Nat),
      a ≤ ds.foldl (fun a d => max a (f d)) a ∧ ∀ d ∈ ds, f d ≤ ds.foldl (fun a d => max a (f d)) a
  | [], a => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: ds, a => by
      obtain ⟨h1, h2⟩ := foldl_max_le f ds (max a (f e))
      refine ⟨le_trans (le_max_left _ _) h1, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact le_trans (le_max_right _ _) h1
      · exact h2 d hd

/-- TWO: every tree of a round is at most as deep as the round's deepest -/
theorem le_depthOf (ts : List _root_.Fmt.Shape) : ∀ e ∈ ts.map (·.a), e ≤ depthOf ts := by
  intro e he
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
  exact (foldl_max_le (fun s : _root_.Fmt.Shape => s.a) ts 0).2 s hs

theorem depthSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (n : Nat) :
    ∀ ds : List RD, (∀ d ∈ ds, depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he),
        fun e he => le_trans (le_depthOf d.trees e he) (h d List.mem_cons_self)⟩,
      depthSL C K chal n ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wqS_okg : Spec.wqS_okg := fun C K chal ds dec hc hd hw =>
  { sh := ⟨wire0S_okg C K chal, wiresS_okg C K chal ds hc hw⟩
    ext := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩
    opens := fun _ ρ _ => by
      show (List.toFinset _).card + (∅ : Finset Empty).card ≤ nOpen ds
      rw [Finset.card_empty, Nat.add_zero]
      exact le_trans (List.toFinset_card_le _)
        (le_trans (List.length_filterMap_le _ _) (wantedSL_len C ds ds hd ρ.2))
    depth := ⟨⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩,
      depthSL C K chal _ ds (foldl_max_le (fun d : RD => depthOf d.trees) ds 0).2⟩ }

/-! ## TWO: the key's round in shape -/

/-- a round that sends two roots: a tree of depth 21 with columns of 36 words, then one of depth 12
with columns of 3 words (the numbers of the key's shared chain's round at the default, not checked
here) -/
def twoD (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (n : Nat) : RD :=
  ⟨e, k, [.root, .root], [⟨21, 36, false, n⟩, ⟨12, 3, false, n + 1⟩], []⟩

theorem two_trees (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (n : Nat) :
    (wireS C K chal (twoD e k n)).depthJ = [21, 12] := rfl

end TypedOracleCompiler.Run.PQ
