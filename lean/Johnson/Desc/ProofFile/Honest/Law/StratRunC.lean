-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratRunC.lean: the slot's three views of what the two strategies
of Honest/StratC.lean write are the three views of the run of `runC` (Honest/Walk.lean), wherever
that run returns, rejected by the verifier or not; and the three rounds without a challenge send the
values of the `KeyAndJoiningRoundMessages`. This is the lemma `views_of_stratC`. It is the counterpart of `views_of_requestStrategy`
(Honest/Law/StratRun.lean), which says the same of `run` and the strategies of Honest/Strat.lean,
and its proof follows that one case by case.

  1  `walkC_ok`, `startC_ok`, `sharedC_ok`, `seamAtC_ok`   where the walk returns, the speakers' own
     functions return what it returns (`startC_ok`: at whatever columns are handed; `sharedC_ok` and
     `seamAtC_ok`: at those that `runC` hands)
  2  `flat_sum`, `tables_lenC`, `depthC`   how many tables; the depth at which a tree is opened
  3  `trAtC`, `views_of_stratC`   the main lemma

Limits.
  * Where `runC` returns an error (a stop, a fault) nothing is said.
  * Further hypotheses of `views_of_stratC`: the library's executable test `FileDescription.planOk` passes
    (`hp`); the data fit the description (`DataFits`, Honest/Law/StratWords.lean; `hD`);
    `halvedAll`: in each chain a prover's side is defined at every sub-protocol one of whose rounds
    declares an item other than a root (`h4`); both `KeyAndJoiningRoundMessages`s' `keyOf` at the input is the prover's
    key at the instance (`hk₀`, `hk`); the parameter `sh` at the prover's key is the description's
    first state of the shared chain (`hsh`); and `hy`: at every stored item that a declared round
    names, and at every position below 2 ^ D.a, the prover's stored column is what the external
    string y holds there.
  * The hypothesis `hy` supplies one string y for every stored item that a declared round names, as
    the library's `colOf` reads y whatever the item. It can be met where the plan names one item;
    `FileDescription.data` returns only then (`storedFit`, OnBytes/Maker/WholeOf.lean: item 0, in the
    shared chain alone).
  * The shared chain's own sealing round is an ordinary round here, shown in the second view with
    its challenge, as in the library: `WholeD.of` drops the first chain's alone, and `runCore` puts
    a round back after the first view alone.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `seamAtC_ok`; `sealQuiet` at the first chain's end, and what `sharedChainStart` returns: `seamAtC_ok`;
    `readyShared … = .ok`, `sh ky = s₂`: `sharedC_ok`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratRun
import Johnson.Desc.ProofFile.Honest.Law.StratFormC
import Johnson.Desc.ProofFile.Honest.Law.StratWalk
import Johnson.Desc.ProofFile.Honest.Law.WalkCols
import Johnson.Desc.ProofFile.Honest.Law.RunMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD Want uLT roundT chainsOf drawnT rhoT rvT colAtST colOf viewOf wantsOf
  view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 S Cl V W Y : Type}

/-! ## 1 Where the walk returns -/

theorem walkC_ok (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' → advanceOverRounds L ss ds z = z'
  | [], [], z, z', h => (walk_nil_ok h).symm
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | s :: ss, d :: ds, z, z', h => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    show advanceOverRounds L ss ds (progressAfterChallenge L z (some s) d) = z'
    rw [hearC_ok hx hz]
    exact walkC_ok L ss ds z₁ z' hw

theorem startC_ok {L : Lay} {bs : List (Block S Cl)} {m : Option (Mid W Y)} {v : Option S}
    {a : ChainProgress S Cl W Y} {front : List OpenedColumn} (h : ChainProgress.start L bs m v front = .ok a) :
    chainStartOrHalted L bs m v front = a := by
  unfold chainStartOrHalted
  rw [h]
  rfl

theorem sharedC_ok {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {sh : Ky → F.S₂}
    {w₀ : W₀} {rc : Rc} {ky : Ky} {c₀ : Purse B.shared} {ss : List (Step (Common W₀ Rc Ky) X₀)}
    {s₂ : F.S₂} {a₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀}
    (hS : readyShared F B H w₀ rc ky c₀ = .ok ss) (hsh : sh ky = s₂)
    (ha : ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
      (some (startShared H ⟨w₀, rc, ky⟩)) (some s₂) [] = .ok a₂) :
    sharedChainStart F B H sh w₀ rc ky c₀ = (ss, a₂) := by
  unfold sharedChainStart
  rw [hS, hsh]
  show (ss, chainStartOrHalted ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
    (some (startShared H ⟨w₀, rc, ky⟩)) (some s₂) []) = _
  rw [startC_ok ha]

theorem seamAtC_ok {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3} {sh : Ky → F.S₂} {w : W₀ × Rc × Sd} {c₀ : Purse B.shared}
    {x : Xi} {c : Purse B.first × Purse B.second} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    {left : List (Step (Local W₀ Rc Xi Tr) X)} {y₁ z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {a₂ z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀} {a₃ : ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X}
    {d₂ : List Fmt.Drawn}
    (hR : ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩ = .ok R)
    (hS : sharedChainStart F B H sh w.1 w.2.1 (J.keyOf w.1 w.2.1 w.2.2) c₀ = (R.shared, a₂))
    (h1 : walk ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ left [⟨[], [], [], none⟩] y₁ = .ok z₁)
    (hq : sealQuiet z₁.laid = true)
    (h2 : walk ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩ R.shared d₂ a₂ = .ok z₂)
    (h3 : ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩
      F.second.blocksInOrder (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) = .ok a₃) :
    seamAtC F B H J sh w c₀ x c left y₁ d₂ =
      (J.seam w.1 w.2.1 w.2.2 x,
        ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩, R.second, a₃) := by
  have e1 := walkC_ok _ _ _ _ _ h1
  have e2 := walkC_ok _ _ _ _ _ h2
  unfold seamAtC
  simp only [hR, hS, e1, hq, if_true, e2]
  show (J.seam w.1 w.2.1 w.2.2 x,
    (⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩ : Lay), R.second,
    chainStartOrHalted ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
      (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) = _
  rw [startC_ok h3]

/-! ## 2 How many tables; the depth -/

theorem flat_sum : ∀ l : List (Step W Y),
    (l.flatMap (·.oracles)).length = (l.map (·.oracles.length)).sum
  | [] => rfl
  | s :: l => by
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, flat_sum l]

theorem tables_lenC (L : Lay) {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {z z' : ChainProgress S Cl W Y} (h : walk L ss ds z = .ok z') (hz : z.laid = [])
    (ho : ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) :
    (tablesOf z'.laid).length = (ss.map (·.oracles.length)).sum := by
  rw [(tables_sentC L ss ds z z' z'.laid h (by rw [hz, List.nil_append]) ho).1, flat_sum]

/-- The depth at which a tree is opened is the length that its table has. As `depth_of_table`
(Honest/Law/StratRun.lean), for rounds that a walk has produced. -/
theorem depthC {F : FileDescription Xi} (hp : F.planOk = true) {i : Nat}
    {l : List Fmt.DeclaredRound} (hi : (l, i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    {r : Fmt.DeclaredRound} (hr : r ∈ l) {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ r.opens) {j : Nat}
    {bs : List (Block S Cl)}
    (hj : (sentOf bs, j) ∈
      [(sentOf F.first.blocksInOrder, 0), (sentOf F.shared.blocksInOrder, 1), (sentOf F.second.blocksInOrder, 2)])
    (hsrc : (srcOf i o.2).1 = j) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {hs : List (Placed V W Y)}
    {ss : List (Step W Y)} (hst : chainSteps B rows look v bs hs = .ok ss) {ps : List Played}
    (hT : ∀ (n : Nat) (pt : Place × Table), ((tablesOf ps)[n]?).bind id = some pt →
      ((ss.flatMap (·.oracles)).map fun o => (o.logLength, o.words))[n]? =
        some (pt.2.logLength, pt.2.words)) {pt : Place × Table}
    (ht : ((tablesOf ps)[(srcOf i o.2).2]?).bind id = some pt) : o.1.a = pt.2.logLength := by
  have h1 := opened_fits hp hi hr ho hj hsrc
  have h2 := hT _ pt ht
  rw [steps_sent hst, h1] at h2
  exact (Prod.mk.inj (Option.some.inj h2)).1

/-! ## 3 The main lemma -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- The transcript that the two strategies of Honest/StratC.lean produce together. -/
def trAtC (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) : Iop.Tr (chainsOf C D tF tJ t3).sh :=
  ((Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
    (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1

/-- **The slot's three views of the strategies' transcript are the run's three views**, and the
three rounds without a challenge send the values of the `KeyAndJoiningRoundMessages`. Its hypotheses beside the run that
returns (`hr`): `hp`, `hD`, `h4`, `hk₀`, `hk`, `hsh`, `hy`: see Limits in the head. -/
theorem views_of_stratC (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) {r : RunC F}
    (hr : runC F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r)
    (hp : F.planOk = true) (hD : DataFits F D) (h4 : halvedAll F H = true)
    (hk₀ : J₀.keyOf w.1 w.2.1 w.2.2 = H.key x) (hk : J.keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hsh : sh (H.key x) = F.start₂ (F.pub x))
    (hy : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : Nat) (h : p < 2 ^ D.a),
      H.storedWords w.1 w.2.1 s.item p = some (y ⟨p, h⟩).2) :
    view₁ C D tF tJ t3 y (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) = r.run.views.1 ∧
    view₂ C D tF tJ t3 y (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) = r.run.views.2.1 ∧
    view₃ C D tF tJ t3 y (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) = r.run.views.2.2 ∧
    ((chainsOf C D tF tJ t3).msgF (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)).2 =
      J.front w.1 w.2.1 w.2.2 x ∧
    ((chainsOf C D tF tJ t3).msgJ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)).2 =
      J₀.join w.1 w.2.1 w.2.2 ∧
    ((chainsOf C D tF tJ t3).msg3 (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)).2 =
      J.seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hw₁, hq, ha₂, hw₂, ha₃, hw₃, rfl⟩ := runC_parts hr
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨hS, hst⟩ := readyShared_ok hR
  have hS' : readyShared F B H w.1 w.2.1 (H.key x) c₀ = .ok R.shared := hS
  have P := (F.planOk_ok).1 hp
  simp only [halvedAll, Bool.and_eq_true] at h4
  obtain ⟨⟨a1, a2⟩, a3⟩ := h4
  have o1 := steps_shaped s1 P.blocks₁
  have o2 := steps_shaped s2 P.blocks₂
  have o3 := steps_shaped s3 P.blocks₃
  have i1 := itemsFall_of_halved s1 a1
  have i2 := itemsFall_of_halved s2 a2
  have i3 := itemsFall_of_halved s3 a3
  obtain ⟨ρ₁, hρ₁⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₁ ρ = u := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₂ ρ = u := ⟨_, rfl⟩
  obtain ⟨ρ₃, hρ₃⟩ : ∃ u, (chainsOf C D tF tJ t3).rho₃ ρ = u := ⟨_, rfl⟩
  obtain ⟨L₁, hL₁⟩ : ∃ u : Lay, u = ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ := ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ u : Lay, u = ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩ := ⟨_, rfl⟩
  obtain ⟨L₃, hL₃⟩ : ∃ u : Lay, u =
      ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩ := ⟨_, rfl⟩
  have p1' : walk L₁ R.first (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩]) a₁ = .ok z₁ := by
    rw [← hρ₁, hL₁]
    exact hw₁
  have p2' : walk L₂ R.shared (drawnT C D.ds₂ ρ₂) a₂ = .ok z₂ := by
    rw [← hρ₂, hL₂]
    exact hw₂
  have p3' : walk L₃ R.second (drawnT C D.ds₃ ρ₃) a₃ = .ok z₃ := by
    rw [← hρ₃, hL₃]
    exact hw₃
  have hLo : ∀ ps, treeOwn ps =
      (envOf (H.storedWords w.1 w.2.1) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w.1 w.2.1) ps [] []).1).symm
  have f1' : fillCols (readsOf 0 0 (H.storedWords w.1 w.2.1) (treeOwn z₁.laid) F.roundsDeclaredByBlocks.1
      (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩])) [] = .ok z₁.cols := by
    rw [← hρ₁]
    exact walk_cols (L := ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩) hLo F.first.blocksInOrder _ _ ha₁ hw₁
      (steps_decl s1) o1
  have f2' : fillCols (readsOf 1 0 (H.storedWords w.1 w.2.1) (treeOwn z₂.laid) F.roundsDeclaredByBlocks.2.1
      (drawnT C D.ds₂ ρ₂)) [] = .ok z₂.cols := by
    rw [← hρ₂]
    exact walk_cols (L := ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩) hLo F.shared.blocksInOrder _ _ ha₂ hw₂
      (steps_decl s2) o2
  have f3' : fillCols (readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w.1 w.2.1)
      (treeThird z₁.laid z₂.laid z₃.laid) F.roundsDeclaredByBlocks.2.2 (drawnT C D.ds₃ ρ₃)) [] = .ok z₃.cols := by
    rw [← hρ₃]
    exact walk_cols
      (L := ⟨2, F.lastChainFirstTreeNumber, H.storedWords w.1 w.2.1, treeThird z₁.laid z₂.laid⟩)
      (fun ps => ((envOf_tree (H.storedWords w.1 w.2.1) z₁.laid z₂.laid ps).2).symm)
      F.second.blocksInOrder _ _ ha₃ hw₃ (steps_decl s3) o3
  have hal₁ : a₁.laid = [] := by
    have e := ha₁
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₁ e
    exact g
  have hal₂ : a₂.laid = [] := by
    have e := ha₂
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₂ e
    exact g
  have hal₃ : a₃.laid = [] := by
    have e := ha₃
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ a₃ e
    exact g
  have Tb1 := (tables_sentC L₁ _ _ a₁ z₁ z₁.laid p1' (by rw [hal₁, List.nil_append]) o1).2
  have Tb2 := (tables_sentC L₂ _ _ a₂ z₂ z₂.laid p2' (by rw [hal₂, List.nil_append]) o2).2
  have Tb3 := (tables_sentC L₃ _ _ a₃ z₃ z₃.laid p3' (by rw [hal₃, List.nil_append]) o3).2
  -- chain 1: the sealing round's `Step` separately
  have hne : R.first ≠ [] := by
    intro h0
    have e := walk_len L₁ _ _ a₁ z₁ p1'
    rw [h0] at e
    simp at e
  obtain ⟨A, sL, hA⟩ := exists_snoc R.first hne
  have hF1 : List.Forall₂ RoundFits D.ds₁ (A.map fun s => (s.decl, s.oracles)) := by
    have h0 := hD.first
    rw [← steps_pairs s1, hA, List.map_append, List.map_cons, List.map_nil,
      List.dropLast_concat] at h0
    exact h0
  have hAl : D.ds₁.length = A.length := by
    have h0 := hF1.length_eq
    rw [List.length_map] at h0
    exact h0
  have p1'' := p1'
  rw [hA] at p1''
  obtain ⟨y₁, q1, qz⟩ := walk_append_ok [sL] [⟨[], [], [], none⟩] A (drawnT C D.ds₁ ρ₁) a₁ z₁
    (by rw [drawnT_length, hAl]) p1''
  obtain ⟨xL, u, -, hzL, hwL⟩ := walk_cons_ok qz
  have huz : z₁ = u := walk_nil_ok hwL
  obtain ⟨pL, hr1⟩ : ∃ pL, z₁.laid = y₁.laid ++ [pL] := ⟨_, by rw [huz]; exact heard_laid hzL⟩
  have hqL : sealQuiet [pL] = true := by
    rw [hr1, sealQuiet_snoc] at hq
    exact hq
  have htz : tablesOf z₁.laid = tablesOf y₁.laid := by
    rw [hr1, tablesOf_append]
    have h1 : tablesOf [pL] = [] := by
      unfold tablesOf
      simp [sealQuiet_one hqL]
    rw [h1, List.append_nil]
  have hrd : (roundsOf z₁.laid).dropLast = roundsOf y₁.laid := by
    rw [hr1]
    simp [roundsOf]
  have iA : itemsFall A [] = true := by
    rw [hA, itemsFall_nil, List.all_append, Bool.and_eq_true] at i1
    rw [itemsFall_nil]
    exact i1.1
  have oA : ∀ s ∈ A, s.oracles.length = s.decl.entry.roots := fun s hs =>
    o1 s (by rw [hA]; exact List.mem_append_left _ hs)
  obtain ⟨ps₁, u1, t1a, t1b, t1c⟩ := trOfC_walk C L₁ [sL] D.ds₁ A a₁ ρ₁ y₁ q1 hF1 iA oA
  rw [hal₁, List.nil_append] at u1
  subst u1
  obtain ⟨ps₂, u2, t2a, -, t2c⟩ := trOfC_walk C L₂ [] D.ds₂ R.shared a₂ ρ₂ z₂ p2'
    (by rw [steps_pairs s2]; exact hD.shared) i2 o2
  rw [hal₂, List.nil_append] at u2
  subst u2
  rw [List.append_nil] at t2a t2c
  obtain ⟨ps₃, u3, t3a, -, t3c⟩ := trOfC_walk C L₃ [] D.ds₃ R.second a₃ ρ₃ z₃ p3'
    (by rw [steps_pairs s3]; exact hD.second) i3 o3
  rw [hal₃, List.nil_append] at u3
  subst u3
  rw [List.append_nil] at t3a t3c
  -- how many trees
  have n1 : (tablesOf y₁.laid).length = D.t₁ := by
    rw [tables_lenC L₁ q1 hal₁ oA]
    have h1 := sum_fits _ _ hF1
    rw [List.map_map] at h1
    exact h1.symm
  have n2 : (tablesOf z₂.laid).length = D.t₂ := by
    rw [tables_lenC L₂ p2' hal₂ o2]
    have h1 := sum_fits _ _ hD.shared
    rw [← steps_pairs s2, List.map_map] at h1
    exact h1.symm
  have e1 : F.t₁ = D.t₁ := by
    rw [← n1, ← htz, tables_lenC L₁ p1' hal₁ o1]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o1 s hs).symm)
  have e2 : F.t₂ = D.t₂ := by
    rw [← n2, tables_lenC L₂ p2' hal₂ o2]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.2.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.2.1 = R.shared.map (·.decl) from (steps_decl s2).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o2 s hs).symm)
  -- the transcript's six parts
  have hSC : sharedChainStart F B H sh w.1 w.2.1 (H.key x) c₀ = (R.shared, a₂) :=
    sharedC_ok hS' hsh (by rw [hst]; exact ha₂)
  have hs1 : chainStartOrHalted ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ F.first.blocksInOrder
      ((Except.ok R : Except Refusal (Ready W₀ Rc Xi Ky Tr X₀ X)).toOption.map
        fun R => R.start₁ H) (some (F.start₁ (F.pub x))) [] = a₁ := startC_ok ha₁
  have hτ : trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ =
      ((Iop.SStrat.zip (sharedOfC C D tF tJ t3 (J₀.join w.1 w.2.1 w.2.2) L₂ R.shared a₂)
        (slotOfC C D tF tJ t3 (J.front w.1 w.2.1 w.2.2 x) L₁ R.first a₁
          (seamAtC F B H J sh w c₀ x c))).run ρ).1 := by
    unfold trAtC
    rw [sharedPartStrategyTrackingVerifier_form, requestStrategyTrackingVerifier_form, hk₀, hSC, hR, hs1, hL₁, hL₂]
    rfl
  have hz₃ : (J.seam w.1 w.2.1 w.2.2 x, L₃, R.second, a₃) =
      seamAtC F B H J sh w c₀ x c
        (endOfC C L₁ D.ds₁ R.first a₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).1
        (endOfC C L₁ D.ds₁ R.first a₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).2
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) := by
    rw [hρ₁, hρ₂, hA, t1b, hL₃]
    refine (seamAtC_ok hR (by rw [hk]; exact hSC) ?_ hq ?_ ha₃).symm
    · rw [← hL₁]
      exact qz
    · rw [← hL₂]
      exact p2'
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := parts_of_zipC C D tF tJ t3 _ _ _ _ _ _ _ _ _ ρ _ hτ _ hz₃
  rw [hρ₁, hA] at m2
  rw [hρ₂] at m4
  rw [hρ₃] at m6
  have m6' : (chainsOf C D tF tJ t3).tr₃ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ) =
      trOfC C L₃ D.ds₃ R.second a₃ ρ₃ := m6
  -- the declared rounds of chain 1
  have hdecl : F.roundsDeclaredByBlocks.1 = A.map (·.decl) ++ [sL.decl] := by
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, hA, List.map_append]
    rfl
  have hdl : F.roundsDeclaredByBlocks.1.dropLast = A.map (·.decl) := by rw [hdecl, List.dropLast_concat]
  have f1'' : fillCols (readsOf 0 0 (H.storedWords w.1 w.2.1) (treeOwn z₁.laid) F.roundsDeclaredByBlocks.1.dropLast
      (drawnT C D.ds₁ ρ₁)) [] = .ok z₁.cols := by
    rw [hdecl, readsOf_append _ _ _ _ _ _ _ _ (by
      rw [List.length_map, drawnT_length, hAl]), reads_seal, List.append_nil] at f1'
    rw [hdl]
    exact f1'
  -- the stored table's columns
  have hsto : ∀ r ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ r.stored, ∀ k u, k < 2 ^ s.sh.a →
      H.storedWords w.1 w.2.1 s.item k = some u →
      colOf C D y (trOfC C L₁ D.ds₁ (A ++ [sL]) a₁ ρ₁)
        (trOfC C L₂ D.ds₂ R.shared a₂ ρ₂)
        (trOfC C L₃ D.ds₃ R.second a₃ ρ₃) (.table s.item k) = some u := by
    intro r hr' s hs' k u hk' hu
    have ha : s.sh.a = D.a := (P.depth r hr' s hs').trans hD.depth.symm
    rw [ha] at hk'
    show (if h : k < 2 ^ D.a then some (y ⟨k, h⟩).2 else none) = some u
    rw [dif_pos hk', ← hy r hr' s hs' k hk']
    exact hu
  -- a tree's column, by the chain that sent it
  have hc1 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf z₁.laid)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOfC C L₁ D.ds₁ (A ++ [sL]) a₁ ρ₁)
        (trOfC C L₂ D.ds₂ R.shared a₂ ρ₂)
        (trOfC C L₃ D.ds₃ R.second a₃ ρ₃) (.tree (0 + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [htz] at hn
    rw [col_first C D y _ _ _ (by rw [← n1]; exact lt_of_bind_some hn)]
    exact t1c n k pt hn hk'
  have hc2 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf z₂.laid)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOfC C L₁ D.ds₁ (A ++ [sL]) a₁ ρ₁)
        (trOfC C L₂ D.ds₂ R.shared a₂ ρ₂)
        (trOfC C L₃ D.ds₃ R.second a₃ ρ₃) (.tree (D.t₁ + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [col_shared C D y _ _ _ (by rw [← n2]; exact lt_of_bind_some hn)]
    exact t2c n k pt hn hk'
  have hc3 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf z₃.laid)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOfC C L₁ D.ds₁ (A ++ [sL]) a₁ ρ₁)
        (trOfC C L₂ D.ds₂ R.shared a₂ ρ₂)
        (trOfC C L₃ D.ds₃ R.second a₃ ρ₃) (.tree (D.t₁ + D.t₂ + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [col_second C D y _ _ _]
    exact t3c n k pt hn hk'
  refine ⟨?_, ?_, ?_, by rw [m1], by rw [m3], by rw [m5]⟩
  · refine view_eq ?_ ?_
    · show rvT C D.ds₁
        ((chainsOf C D tF tJ t3).tr₁ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)) = _
      rw [m2, t1a]
      exact hrd.symm
    · show ((wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁
        ((chainsOf C D tF tJ t3).tr₁
          (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ))))).filterMap _) = z₁.cols
      rw [m2, m4, m6', rhoT_trOfC, hD.wants.1]
      refine wants_cols (numAt F.t₁ F.t₂ 0) D.key₁ _ _ ?_ ?_ 0 0 (H.storedWords w.1 w.2.1)
        (treeOwn z₁.laid) F.roundsDeclaredByBlocks.1.dropLast _ z₁.cols
        (fun r hr' => hD.keys.1 r (List.mem_of_mem_dropLast hr'))
        (fun r hr' => hsto r (List.mem_append_left _ (List.mem_append_left _
          (List.mem_of_mem_dropLast hr')))) ?_ f1''
      · intro _ _ _
        rfl
      · intro _ _ _
        rfl
      · intro r hr' o ho k pt hk' ht
        have hr'' := List.mem_of_mem_dropLast hr'
        cases ho2 : o.2 with
        | taken ch j =>
          rw [ho2] at ht
          cases ht
        | own n =>
          have ht' : ((tablesOf z₁.laid)[(srcOf 0 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depthC hp (i := 0) (by simp) hr'' ho (j := 0) (bs := F.first.blocksInOrder)
                (by simp) (by rw [ho2]; rfl) s1 Tb1 ht'
          rw [ho2] at ht'
          exact hc1 n k pt ht' (by rw [← hd]; exact hk')
  · refine view_eq ?_ ?_
    · show rvT C D.ds₂
        ((chainsOf C D tF tJ t3).tr₂ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)) = _
      rw [m4, t2a]
    · show ((wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂
        ((chainsOf C D tF tJ t3).tr₂
          (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ))))).filterMap _) = z₂.cols
      rw [m2, m4, m6', rhoT_trOfC, hD.wants.2.1]
      refine wants_cols (numAt F.t₁ F.t₂ 1) D.key₂ _ _ ?_ ?_ 1 0 (H.storedWords w.1 w.2.1)
        (treeOwn z₂.laid) F.roundsDeclaredByBlocks.2.1 _ z₂.cols hD.keys.2.1
        (fun r hr' => hsto r (List.mem_append_left _ (List.mem_append_right _ hr'))) ?_ f2'
      · intro _ _ _
        rfl
      · intro _ _ _
        rfl
      · intro r hr' o ho k pt hk' ht
        cases ho2 : o.2 with
        | taken ch j =>
          rw [ho2] at ht
          cases ht
        | own n =>
          have ht' : ((tablesOf z₂.laid)[(srcOf 1 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depthC hp (i := 1) (by simp) hr' ho (j := 1) (bs := F.shared.blocksInOrder)
                (by simp) (by rw [ho2]; rfl) s2 Tb2 ht'
          rw [ho2] at ht'
          show colOf C D y _ _ _ (.tree (F.t₁ + n) k) = _
          rw [e1]
          exact hc2 n k pt ht' (by rw [← hd]; exact hk')
  · refine view_eq ?_ ?_
    · show rvT C D.ds₃
        ((chainsOf C D tF tJ t3).tr₃ (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ)) = _
      rw [m6', t3a]
    · show ((wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃
        ((chainsOf C D tF tJ t3).tr₃
          (trAtC C D tF tJ t3 F B H J₀ J sh w c₀ x c ρ))))).filterMap _) = z₃.cols
      rw [m2, m4, m6', rhoT_trOfC, hD.wants.2.2]
      refine wants_cols (numAt F.t₁ F.t₂ 2) D.key₃ _ _ ?_ ?_ 2 F.lastChainFirstTreeNumber
        (H.storedWords w.1 w.2.1) (treeThird z₁.laid z₂.laid z₃.laid) F.roundsDeclaredByBlocks.2.2 _ z₃.cols
        hD.keys.2.2
        (fun r hr' => hsto r (List.mem_append_right _ hr')) ?_ f3'
      · intro _ _ _
        rfl
      · intro _ _ _
        rfl
      · intro r hr' o ho k pt hk' ht
        cases ho2 : o.2 with
        | own n =>
          have ht' : ((tablesOf z₃.laid)[(srcOf 2 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depthC hp (i := 2) (by simp) hr' ho (j := 2) (bs := F.second.blocksInOrder)
                (by simp) (by rw [ho2]; rfl) s3 Tb3 ht'
          rw [ho2] at ht'
          show colOf C D y _ _ _ (.tree (F.t₁ + F.t₂ + n) k) = _
          rw [e1, e2]
          exact hc3 n k pt ht' (by rw [← hd]; exact hk')
        | taken ch j =>
          rw [ho2] at ht
          by_cases h0 : ch = 0
          · subst h0
            have ht0 : ((tablesOf z₁.laid)[j]?).bind id = some pt := ht
            have ht' : ((tablesOf z₁.laid)[(srcOf 2 o.2).2]?).bind id = some pt := by
              rw [ho2]
              exact ht0
            have hd := depthC hp (i := 2) (by simp) hr' ho (j := 0) (bs := F.first.blocksInOrder)
                (by simp) (by rw [ho2]; rfl) s1 Tb1 ht'
            exact hc1 j k pt ht0 (by rw [← hd]; exact hk')
          · by_cases h1 : ch = 1
            · subst h1
              have ht0 : ((tablesOf z₂.laid)[j]?).bind id = some pt := ht
              have ht' : ((tablesOf z₂.laid)[(srcOf 2 o.2).2]?).bind id = some pt := by
                rw [ho2]
                exact ht0
              have hd := depthC hp (i := 2) (by simp) hr' ho (j := 1) (bs := F.shared.blocksInOrder)
                (by simp) (by rw [ho2]; rfl) s2 Tb2 ht'
              show colOf C D y _ _ _ (.tree (F.t₁ + j) k) = _
              rw [e1]
              exact hc2 j k pt ht0 (by rw [← hd]; exact hk')
            · have hnone : treeThird z₁.laid z₂.laid z₃.laid (.taken ch j) = none := by
                simp [treeThird, h0, h1]
              rw [hnone] at ht
              cases ht


end

end ProofFile.Honest

#print axioms ProofFile.Honest.walkC_ok
#print axioms ProofFile.Honest.startC_ok
#print axioms ProofFile.Honest.sharedC_ok
#print axioms ProofFile.Honest.seamAtC_ok
#print axioms ProofFile.Honest.flat_sum
#print axioms ProofFile.Honest.tables_lenC
#print axioms ProofFile.Honest.depthC
#print axioms ProofFile.Honest.views_of_stratC
#print axioms ProofFile.Honest.trAtC
