-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratRun.lean: the strategies of Honest/Strat.lean compared with
`run` (Honest/Frame.lean). One main lemma, `views_of_requestStrategy`: at every verifier's message at which
`run` goes through, the three views that the library's slot reads from the strategies' transcript
(`view₁`, `view₂`, `view₃`, OnBytes/Maker/WholeViews.lean) are the run's three views, and the three
rounds without a challenge send the values of the two `KeyAndJoiningRoundMessages`s (front and seam from J, the joining
round from J₀). It is general in the description, the challenge kit, the book and the prover; the
data are any that fit the description (`DataFits`).

  1  the definitions in which it is stated, `drawsAt`, `rowsOfChain`, `DataFits`, `trAt`, are in
     Honest/Law/StratWords.lean
  2  on lists and on one chain: `map_zip_snd`, `steps_pairs`, `steps_sent`, `tables_len`,
     `sum_fits`, `drawnT_length`, `reads_seal`, `lt_of_bind_some`, `depth_of_table`, `view_eq`,
     `yields_one`
  3  `readyShared_ok`, `seamAt_ok`   where the run goes through: what the strategies' own definition
     (Honest/Law/StratForm.lean) returns
  4  `col_first`, `col_shared`, `col_second`   the slot's look-up of a tree's column
  5  `views_of_requestStrategy`

Limits.
  * The lemma starts from a run that has gone through, with no stored run to fall back on, at a
    prover with a prover's side wherever an item is declared: it does not say that there is such a
    run.
  * Further hypotheses of `views_of_requestStrategy`: the library's executable test `FileDescription.planOk` passes
    (`hp`); the data fit the description (`DataFits`, Honest/Law/StratWords.lean; `hD`);
    `halvedAll`: in each chain a prover's side is defined at every sub-protocol one of whose rounds
    declares an item other than a root (`h4`); both `KeyAndJoiningRoundMessages`s' `keyOf` at the input is the prover's
    key at the instance (`hk₀`, `hk`); and `hy`: at every stored item that a declared round names,
    and at every position below 2 ^ D.a, the prover's stored column is what the external string y
    holds there.
  * The hypothesis `hy` supplies one string y for every stored item that a declared round names, as
    the library's `colOf` reads y whatever the item. It can be met where the plan names one item;
    `FileDescription.data` returns only then (`storedFit`, OnBytes/Maker/WholeOf.lean: item 0, in the
    shared chain alone).
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `readyShared_ok`, `seamAt_ok`.
  * The lemmas prove no property of a prover or a protocol.
-/
import OnBytes.Maker.WholeViews
import Johnson.Desc.ProofFile.Honest.Law.StratWords
import Johnson.Desc.ProofFile.Honest.Law.StratCols
import Johnson.Desc.ProofFile.Honest.Law.StratForm
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD Want uLT roundT chainsOf drawnT rhoT rvT colAtST colOf viewOf wantsOf
  view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 S Cl V W Y : Type}

/-! ## 2 On lists, and on one chain -/

theorem map_zip_snd {α β γ : Type} (f : β → γ) : ∀ (l : List α) (m : List β),
    m.length ≤ l.length → (l.zip m).map (fun r => f r.2) = m.map f
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: l, b :: m, h => congrArg (f b :: ·) (map_zip_snd f l m (Nat.le_of_succ_le_succ h))

section
variable {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
  {bs : List (Block S Cl)} {hs : List (Placed V W X)} {ss : List (Step W X)}

/-- The rounds that `chainSteps` prepares, each with its oracle messages. -/
theorem steps_pairs (h : chainSteps B rows look v bs hs = .ok ss) :
    ss.map (fun s => (s.decl, s.oracles)) = rowsOfChain bs := by
  obtain ⟨-, h2⟩ := chainSteps_rows bs hs ss h
  have h3 := congrArg (List.map fun z : Fmt.DeclaredRound × List Oracle × Place × Bool =>
    (z.1, z.2.1)) h2
  rw [List.map_map, List.map_flatMap] at h3
  refine h3.trans ?_
  unfold rowsOfChain
  refine List.flatMap_congr fun b _ => ?_
  rw [List.map_map]
  exact List.map_id' _

/-- What these rounds declare of their trees is what the sub-protocols declare, concatenated. -/
theorem steps_sent (h : chainSteps B rows look v bs hs = .ok ss) :
    ((ss.flatMap (·.oracles)).map fun o => (o.logLength, o.words)) = sentOf bs := by
  have h1 := congrArg (List.map (·.2)) (steps_pairs h)
  rw [List.map_map] at h1
  have h2 : ss.flatMap (·.oracles) = (ss.map (·.oracles)).flatMap id := by
    rw [List.flatMap_map]
    rfl
  have h3 : ss.map (·.oracles) = (rowsOfChain bs).map (·.2) := h1
  have hlen := (chainSteps_rows bs hs ss h).1
  have h4 : ∀ l : List (Block S Cl), (∀ b ∈ l, b.oracles.length = b.rounds.length) →
      (((rowsOfChain l).map (·.2)).flatMap id).map (fun o : Oracle => (o.logLength, o.words)) =
        sentOf l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons b l ih =>
      intro hl
      have e1 : rowsOfChain (b :: l) = b.rounds.zip b.oracles ++ rowsOfChain l := by
        unfold rowsOfChain
        rw [List.flatMap_cons]
      have e2 : sentOf (b :: l) = (b.oracles.flatMap fun l' => l'.map fun o =>
          (o.logLength, o.words)) ++ sentOf l := by
        unfold sentOf
        rw [List.flatMap_cons]
      have e3 : (b.rounds.zip b.oracles).map (·.2) = b.oracles :=
        (map_zip_snd (fun (z : List Oracle) => z) b.rounds b.oracles
          (Nat.le_of_eq (hl b List.mem_cons_self))).trans (List.map_id' _)
      rw [e1, e2, List.map_append, List.flatMap_append, List.map_append, e3,
        ih fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'), List.map_flatMap]
      rfl
  rw [h2, h3]
  exact h4 bs hlen

end

theorem tables_len : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    (tablesOf ps).length = (ss.map (·.oracles.length)).sum := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h _
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h ho
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        rw [tablesOf_cons, List.length_append, List.length_map,
          (yields_tables h.1 (ho s List.mem_cons_self)).1,
          ih ds back.tail ps h.2 fun s' hs' => ho s' (List.mem_cons_of_mem _ hs'),
          List.map_cons, List.sum_cons]

theorem sum_fits : ∀ (ds : List RDT) (zs : List (Fmt.DeclaredRound × List Oracle)),
    List.Forall₂ RoundFits ds zs → (ds.map (·.trees.length)).sum = (zs.map (·.2.length)).sum := by
  intro ds zs h
  induction h with
  | nil => rfl
  | @cons d z ds zs h1 _ ih =>
    have h2 := congrArg List.length h1.2
    rw [List.length_map, List.length_map] at h2
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, h2]

theorem drawnT_length (C : CK) : ∀ (ds : List RDT) (ρ : Iop.Rho (uLT C ds)),
    (drawnT C ds ρ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, ρ) => congrArg (· + 1) (drawnT_length C ds ρ)

/-- At the empty challenge a round reads nothing. -/
theorem reads_seal (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (d : Fmt.DeclaredRound) :
    readsOf chain ft stored tree [d] [⟨[], [], [], none⟩] = [] := by
  simp [readsOf, Fmt.partOf, Fmt.listOf]

/-! ## 3 Where the run goes through: what the strategies' own definition returns -/

theorem readyShared_ok {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : ready F B H w₀ rc x c = .ok R) :
    readyShared F B H w₀ rc (H.key x) c.shared = .ok R.shared ∧
      startShared H ⟨w₀, rc, H.key x⟩ = R.start₂ H := by
  obtain ⟨ht, tr, -, -, hc, -, h2, -⟩ := ready_ok h
  rw [hc] at h2
  constructor
  · have e : readyShared F B H w₀ rc (H.key x) c.shared =
        (readyTests F B H w₀).bind fun _ => sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared := rfl
    rw [e, ht]
    show unfit (chainSteps B (B.rowsOf 1) (sharedLook B c.shared)
      (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder H.shared) = _
    rw [h2]
    rfl
  · unfold Ready.start₂
    rw [hc]

theorem seamAt_ok {D : WholeD} {F : FileDescription Xi} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3} {w : W₀ × Rc × Sd}
    {c₀ : Purse B.shared} {x : Xi} {c : Purse B.first × Purse B.second}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} {a₁ : Mid (Local W₀ Rc Xi Tr) X} {d₂ : List Fmt.Drawn}
    {z : List Played × Mid (Local W₀ Rc Xi Tr) X} {r₂ : List Played × Mid (Common W₀ Rc Ky) X₀}
    (hR : ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩ = .ok R)
    (hS : readyShared F B H w.1 w.2.1 (J.keyOf w.1 w.2.1 w.2.2) c₀ = .ok R.shared)
    (h1 : play (R.first.drop D.ds₁.length) [⟨[], [], [], none⟩] [] a₁ = .ok z)
    (hq : sealQuiet z.1 = true)
    (h2 : play R.shared d₂ [] (startShared H ⟨w.1, w.2.1, J.keyOf w.1 w.2.1 w.2.2⟩) = .ok r₂) :
    seamAt D F B H J w c₀ x c (some a₁) d₂ =
      (J.seam w.1 w.2.1 w.2.2 x, R.second, some (R.start₃ H z.2 r₂.2)) := by
  simp [seamAt, hR, hS, h1, h2, sealTest, hq, Except.toOption, Except.bind]

/-! ## 4 The slot's look-up of a tree's column -/

section
variable (C : CK) (D : WholeD) (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁))
  (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃))

theorem col_first {n k : Nat} (hn : n < D.t₁) :
    colOf C D y τ₁ τ₂ τ₃ (.tree (0 + n) k) = colAtST C D.ds₁ τ₁ n k := by
  show (if 0 + n < D.t₁ then colAtST C D.ds₁ τ₁ (0 + n) k else _) = _
  rw [Nat.zero_add, if_pos hn]

theorem col_shared {n k : Nat} (hn : n < D.t₂) :
    colOf C D y τ₁ τ₂ τ₃ (.tree (D.t₁ + n) k) = colAtST C D.ds₂ τ₂ n k := by
  show (if D.t₁ + n < D.t₁ then _ else if D.t₁ + n - D.t₁ < D.t₂ then
    colAtST C D.ds₂ τ₂ (D.t₁ + n - D.t₁) k else _) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hn]

theorem col_second {n k : Nat} :
    colOf C D y τ₁ τ₂ τ₃ (.tree (D.t₁ + D.t₂ + n) k) = colAtST C D.ds₃ τ₃ n k := by
  show (if D.t₁ + D.t₂ + n < D.t₁ then _ else if D.t₁ + D.t₂ + n - D.t₁ < D.t₂ then _ else
    colAtST C D.ds₃ τ₃ (D.t₁ + D.t₂ + n - D.t₁ - D.t₂) k) = _
  have e : D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n := by omega
  rw [if_neg (by omega), if_neg (by omega), e]

end

theorem lt_of_bind_some {α : Type} {l : List (Option α)} {n : Nat} {a : α}
    (h : (l[n]?).bind id = some a) : n < l.length := by
  by_cases hn : n < l.length
  · exact hn
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    cases h

/-- The depth at which a tree is opened is the logarithm of the length that its table has. `i`: the
chain of the round that opens; `j`: the chain that sent the tree. -/
theorem depth_of_table {F : FileDescription Xi} (hp : F.planOk = true) {i : Nat}
    {l : List Fmt.DeclaredRound} (hi : (l, i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    {r : Fmt.DeclaredRound} (hr : r ∈ l) {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ r.opens) {j : Nat}
    {bs : List (Block S Cl)}
    (hj : (sentOf bs, j) ∈
      [(sentOf F.first.blocksInOrder, 0), (sentOf F.shared.blocksInOrder, 1), (sentOf F.second.blocksInOrder, 2)])
    (hsrc : (srcOf i o.2).1 = j) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {hs : List (Placed V W X)}
    {ss : List (Step W X)} (hst : chainSteps B rows look v bs hs = .ok ss) {ds : List Fmt.Drawn}
    {back : List Fmt.RoundView} {ps : List Played} (hY : Yields ss ds back ps)
    (hsh : ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) {pt : Place × Table}
    (ht : ((tablesOf ps)[(srcOf i o.2).2]?).bind id = some pt) : o.1.a = pt.2.logLength := by
  have h1 := opened_fits hp hi hr ho hj hsrc
  have h2 := tables_sent ss ds back ps hY hsh _ pt ht
  rw [steps_sent hst, h1] at h2
  exact (Prod.mk.inj (Option.some.inj h2)).1

theorem view_eq {v : Fmt.View} {rs : List Fmt.RoundView} {cs : List OpenedColumn} (h1 : v.rounds = rs)
    (h2 : v.opened = cs) : v = ⟨rs, cs⟩ := by
  cases v
  cases h1
  cases h2
  rfl

theorem sealQuiet_snoc (l : List Played) (p : Played) : sealQuiet (l ++ [p]) = sealQuiet [p] := by
  simp [sealQuiet]

theorem sealQuiet_one {p : Played} (h : sealQuiet [p] = true) : p.tables = [] := by
  simp [sealQuiet] at h
  exact h.1.2

/-! ## 5 The main lemma -/

theorem yields_one {s : Step W X} {d : Fmt.Drawn} {back : List Fmt.RoundView} {ps : List Played}
    (h : Yields [s] [d] back ps) : ∃ p, ps = [p] := by
  cases ps with
  | nil => simp [Yields] at h
  | cons p ps =>
    cases ps with
    | nil => exact ⟨p, rfl⟩
    | cons q ps => simp [Yields] at h

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (w : W₀ × Rc × Sd)
  (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- **The slot's three views of the strategies' transcript are the run's three views**, and the
three rounds without a challenge send the values of the two `KeyAndJoiningRoundMessages`s (front and seam from J, the
joining round from J₀). Its hypotheses beside the run that has gone through (`hr`): `hp`, `hD`,
`h4`, `hk₀`, `hk`, `hy`: see Limits in the head. -/
theorem views_of_requestStrategy (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) {r : Run}
    (hr : run F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩ (drawsAt C D tF tJ t3 ρ) none = .ok r)
    (hp : F.planOk = true) (hD : DataFits F D) (h4 : halvedAll F H = true)
    (hk₀ : J₀.keyOf w.1 w.2.1 w.2.2 = H.key x) (hk : J.keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hy : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : Nat) (h : p < 2 ^ D.a),
      H.storedWords w.1 w.2.1 s.item p = some (y ⟨p, h⟩).2) :
    view₁ C D tF tJ t3 y (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ) = r.views.1 ∧
    view₂ C D tF tJ t3 y (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ) = r.views.2.1 ∧
    view₃ C D tF tJ t3 y (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ) = r.views.2.2 ∧
    ((chainsOf C D tF tJ t3).msgF (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)).2 =
      J.front w.1 w.2.1 w.2.2 x ∧
    ((chainsOf C D tF tJ t3).msgJ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)).2 =
      J₀.join w.1 w.2.1 w.2.2 ∧
    ((chainsOf C D tF tJ t3).msg3 (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)).2 =
      J.seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨R, r₁, r₂, r₃, c₁, c₂, c₃, hR, -, p1, hq, p2, p3, f1, f2, f3, rfl⟩ := run_parts hr
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
  have p1' : play R.first (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩]) [] (R.start₁ H) = .ok r₁ := by
    rw [← hρ₁]
    exact p1
  have p2' : play R.shared (drawnT C D.ds₂ ρ₂) [] (R.start₂ H) = .ok r₂ := by
    rw [← hρ₂]
    exact p2
  have p3' : play R.second (drawnT C D.ds₃ ρ₃) [] (R.start₃ H r₁.2 r₂.2) = .ok r₃ := by
    rw [← hρ₃]
    exact p3
  have f1' : fillCols (readsOf 0 0 (H.storedWords w.1 w.2.1) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1
      (drawnT C D.ds₁ ρ₁ ++ [⟨[], [], [], none⟩])) [] = .ok c₁ := by
    rw [← hρ₁]
    exact f1
  have f2' : fillCols (readsOf 1 0 (H.storedWords w.1 w.2.1) (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1
      (drawnT C D.ds₂ ρ₂)) [] = .ok c₂ := by
    rw [← hρ₂]
    exact f2
  have f3' : fillCols (readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w.1 w.2.1)
      (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2 (drawnT C D.ds₃ ρ₃)) [] = .ok c₃ := by
    rw [← hρ₃]
    exact f3
  have Y1 := play_yields _ _ _ _ _ p1'
  have Y2 := play_yields _ _ _ _ _ p2'
  have Y3 := play_yields _ _ _ _ _ p3'
  -- chain 1: the sealing round's `Step` separately
  have hne : R.first ≠ [] := by
    intro h0
    rw [h0] at p1'
    cases hd : drawnT C D.ds₁ ρ₁ <;> rw [hd] at p1' <;> simp [play] at p1'
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
  have htake : R.first.take D.ds₁.length = A := by
    rw [hA, hAl]
    exact List.take_left' rfl
  have hdrop : R.first.drop D.ds₁.length = [sL] := by
    rw [hA, hAl]
    exact List.drop_left' rfl
  have p1'' := p1'
  rw [hA, play_append A [sL] _ _ [] _ (by rw [drawnT_length, hAl])] at p1''
  obtain ⟨y₁, q1, h0⟩ := exBind_ok p1''
  obtain ⟨z, qz, hz⟩ := exMap_ok h0
  rw [List.drop_nil] at qz
  obtain ⟨pL, hpL⟩ := yields_one (play_yields _ _ _ _ _ qz)
  have hr1 : r₁.1 = y₁.1 ++ [pL] := by rw [← hz, ← hpL]
  have hr2 : r₁.2 = z.2 := by rw [← hz]
  have hqL : sealQuiet [pL] = true := by
    rw [hr1, sealQuiet_snoc] at hq
    exact hq
  have hqz : sealQuiet z.1 = true := by
    rw [hpL]
    exact hqL
  have htz : tablesOf r₁.1 = tablesOf y₁.1 := by
    rw [hr1, tablesOf_append]
    have h1 : tablesOf [pL] = [] := by
      unfold tablesOf
      simp [sealQuiet_one hqL]
    rw [h1, List.append_nil]
  have hrd : (roundsOf r₁.1).dropLast = roundsOf y₁.1 := by
    rw [hr1]
    simp [roundsOf]
  have iA : itemsFall A [] = true := by
    rw [hA, itemsFall_nil, List.all_append, Bool.and_eq_true] at i1
    rw [itemsFall_nil]
    exact i1.1
  have oA : ∀ s ∈ A, s.oracles.length = s.decl.entry.roots := fun s hs =>
    o1 s (by rw [hA]; exact List.mem_append_left _ hs)
  obtain ⟨t1a, t1b, t1c⟩ := trOf_play C D.ds₁ A (R.start₁ H) ρ₁ y₁ q1 hF1 iA oA
  obtain ⟨t2a, -, t2c⟩ := trOf_play C D.ds₂ R.shared (R.start₂ H) ρ₂ r₂ p2'
    (by rw [steps_pairs s2]; exact hD.shared) i2 o2
  obtain ⟨t3a, -, t3c⟩ := trOf_play C D.ds₃ R.second (R.start₃ H r₁.2 r₂.2) ρ₃ r₃ p3'
    (by rw [steps_pairs s3]; exact hD.second) i3 o3
  -- how many trees
  have n1 : (tablesOf y₁.1).length = D.t₁ := by
    rw [tables_len A _ _ _ (play_yields _ _ _ _ _ q1) oA]
    have h1 := sum_fits _ _ hF1
    rw [List.map_map] at h1
    exact h1.symm
  have n2 : (tablesOf r₂.1).length = D.t₂ := by
    rw [tables_len R.shared _ _ _ Y2 o2]
    have h1 := sum_fits _ _ hD.shared
    rw [← steps_pairs s2, List.map_map] at h1
    exact h1.symm
  have e1 : F.t₁ = D.t₁ := by
    rw [← n1, ← htz, tables_len R.first _ _ _ Y1 o1]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o1 s hs).symm)
  have e2 : F.t₂ = D.t₂ := by
    rw [← n2, tables_len R.shared _ _ _ Y2 o2]
    show Johnson.G.OfPlan.rootsOf F.roundsDeclaredByBlocks.2.1 = _
    unfold Johnson.G.OfPlan.rootsOf
    rw [show F.roundsDeclaredByBlocks.2.1 = R.shared.map (·.decl) from (steps_decl s2).symm, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun s hs => (o2 s hs).symm)
  -- the transcript's six parts
  have hτ : trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ =
      ((Iop.SStrat.zip (sharedOf C D tF tJ t3 (J₀.join w.1 w.2.1 w.2.2) R.shared
        (some (R.start₂ H))) (slotOf C D tF tJ t3 (J.front w.1 w.2.1 w.2.2 x) R.first
          (some (R.start₁ H)) (seamAt D F B H J w c₀ x c))).run ρ).1 := by
    unfold trAt
    rw [sharedPartStrategy_form, requestStrategy_form, hR, hk₀, hS', hst]
    rfl
  have hz₃ : (J.seam w.1 w.2.1 w.2.2 x, R.second, some (R.start₃ H r₁.2 r₂.2)) =
      seamAt D F B H J w c₀ x c
        (endOf C D.ds₁ R.first (some (R.start₁ H)) ((chainsOf C D tF tJ t3).rho₁ ρ))
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) := by
    rw [hρ₁, hρ₂, endOf_take, htake, t1b, hr2]
    refine (seamAt_ok hR (by rw [hk]; exact hS') (by rw [hdrop]; exact qz) hqz ?_).symm
    rw [hk, hst]
    exact p2'
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := parts_of_zip C D tF tJ t3 _ _ _ _ _ _ _ ρ _ hτ _ hz₃
  rw [hρ₁, trOf_take, htake] at m2
  rw [hρ₂] at m4
  rw [hρ₃] at m6
  have m6' : (chainsOf C D tF tJ t3).tr₃ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ) =
      trOf C D.ds₃ R.second (some (R.start₃ H r₁.2 r₂.2)) ρ₃ := m6
  -- the declared rounds of chain 1
  have hdecl : F.roundsDeclaredByBlocks.1 = A.map (·.decl) ++ [sL.decl] := by
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, hA, List.map_append]
    rfl
  have hdl : F.roundsDeclaredByBlocks.1.dropLast = A.map (·.decl) := by rw [hdecl, List.dropLast_concat]
  have f1'' : fillCols (readsOf 0 0 (H.storedWords w.1 w.2.1) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1.dropLast
      (drawnT C D.ds₁ ρ₁)) [] = .ok c₁ := by
    rw [hdecl, readsOf_append _ _ _ _ _ _ _ _ (by
      rw [List.length_map, drawnT_length, hAl]), reads_seal, List.append_nil] at f1'
    rw [hdl]
    exact f1'
  -- the stored table's columns
  have hsto : ∀ r ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ r.stored, ∀ k u, k < 2 ^ s.sh.a →
      H.storedWords w.1 w.2.1 s.item k = some u →
      colOf C D y (trOf C D.ds₁ A (some (R.start₁ H)) ρ₁)
        (trOf C D.ds₂ R.shared (some (R.start₂ H)) ρ₂)
        (trOf C D.ds₃ R.second (some (R.start₃ H r₁.2 r₂.2)) ρ₃) (.table s.item k) = some u := by
    intro r hr' s hs' k u hk' hu
    have ha : s.sh.a = D.a := (P.depth r hr' s hs').trans hD.depth.symm
    rw [ha] at hk'
    show (if h : k < 2 ^ D.a then some (y ⟨k, h⟩).2 else none) = some u
    rw [dif_pos hk', ← hy r hr' s hs' k hk']
    exact hu
  -- a tree's column, by the chain that sent it
  have hc1 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf r₁.1)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOf C D.ds₁ A (some (R.start₁ H)) ρ₁)
        (trOf C D.ds₂ R.shared (some (R.start₂ H)) ρ₂)
        (trOf C D.ds₃ R.second (some (R.start₃ H r₁.2 r₂.2)) ρ₃) (.tree (0 + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [htz] at hn
    rw [col_first C D y _ _ _ (by rw [← n1]; exact lt_of_bind_some hn)]
    exact t1c n k pt hn hk'
  have hc2 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf r₂.1)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOf C D.ds₁ A (some (R.start₁ H)) ρ₁)
        (trOf C D.ds₂ R.shared (some (R.start₂ H)) ρ₂)
        (trOf C D.ds₃ R.second (some (R.start₃ H r₁.2 r₂.2)) ρ₃) (.tree (D.t₁ + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [col_shared C D y _ _ _ (by rw [← n2]; exact lt_of_bind_some hn)]
    exact t2c n k pt hn hk'
  have hc3 : ∀ (n k : Nat) (pt : Place × Table), ((tablesOf r₃.1)[n]?).bind id = some pt →
      k < 2 ^ pt.2.logLength →
      colOf C D y (trOf C D.ds₁ A (some (R.start₁ H)) ρ₁)
        (trOf C D.ds₂ R.shared (some (R.start₂ H)) ρ₂)
        (trOf C D.ds₃ R.second (some (R.start₃ H r₁.2 r₂.2)) ρ₃) (.tree (D.t₁ + D.t₂ + n) k) =
          some (pt.2.col k) := by
    intro n k pt hn hk'
    rw [col_second C D y _ _ _]
    exact t3c n k pt hn hk'
  refine ⟨?_, ?_, ?_, by rw [m1], by rw [m3], by rw [m5]⟩
  · refine view_eq ?_ ?_
    · show rvT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)) = _
      rw [m2, t1a]
      exact hrd.symm
    · show ((wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁
        ((chainsOf C D tF tJ t3).tr₁ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ))))).filterMap _) = c₁
      rw [m2, m4, m6', rhoT_trOf, hD.wants.1]
      refine wants_cols (numAt F.t₁ F.t₂ 0) D.key₁ _ _ ?_ ?_ 0 0 (H.storedWords w.1 w.2.1)
        (treeOwn r₁.1) F.roundsDeclaredByBlocks.1.dropLast _ c₁
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
          have ht' : ((tablesOf r₁.1)[(srcOf 0 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depth_of_table hp (i := 0) (by simp) hr'' ho (j := 0) (bs := F.first.blocksInOrder)
            (by simp) (by rw [ho2]; rfl) s1 Y1 o1 ht'
          rw [ho2] at ht'
          exact hc1 n k pt ht' (by rw [← hd]; exact hk')
  · refine view_eq ?_ ?_
    · show rvT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)) = _
      rw [m4, t2a]
    · show ((wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂
        ((chainsOf C D tF tJ t3).tr₂ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ))))).filterMap _) = c₂
      rw [m2, m4, m6', rhoT_trOf, hD.wants.2.1]
      refine wants_cols (numAt F.t₁ F.t₂ 1) D.key₂ _ _ ?_ ?_ 1 0 (H.storedWords w.1 w.2.1)
        (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 _ c₂ hD.keys.2.1
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
          have ht' : ((tablesOf r₂.1)[(srcOf 1 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depth_of_table hp (i := 1) (by simp) hr' ho (j := 1) (bs := F.shared.blocksInOrder)
            (by simp) (by rw [ho2]; rfl) s2 Y2 o2 ht'
          rw [ho2] at ht'
          show colOf C D y _ _ _ (.tree (F.t₁ + n) k) = _
          rw [e1]
          exact hc2 n k pt ht' (by rw [← hd]; exact hk')
  · refine view_eq ?_ ?_
    · show rvT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ)) = _
      rw [m6', t3a]
    · show ((wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃
        ((chainsOf C D tF tJ t3).tr₃ (trAt C D tF tJ t3 F B H J₀ J w c₀ x c ρ))))).filterMap _) = c₃
      rw [m2, m4, m6', rhoT_trOf, hD.wants.2.2]
      refine wants_cols (numAt F.t₁ F.t₂ 2) D.key₃ _ _ ?_ ?_ 2 F.lastChainFirstTreeNumber
        (H.storedWords w.1 w.2.1) (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2 _ c₃ hD.keys.2.2
        (fun r hr' => hsto r (List.mem_append_right _ hr')) ?_ f3'
      · intro _ _ _
        rfl
      · intro _ _ _
        rfl
      · intro r hr' o ho k pt hk' ht
        cases ho2 : o.2 with
        | own n =>
          have ht' : ((tablesOf r₃.1)[(srcOf 2 o.2).2]?).bind id = some pt := by
            rw [ho2] at ht ⊢
            exact ht
          have hd := depth_of_table hp (i := 2) (by simp) hr' ho (j := 2) (bs := F.second.blocksInOrder)
            (by simp) (by rw [ho2]; rfl) s3 Y3 o3 ht'
          rw [ho2] at ht'
          show colOf C D y _ _ _ (.tree (F.t₁ + F.t₂ + n) k) = _
          rw [e1, e2]
          exact hc3 n k pt ht' (by rw [← hd]; exact hk')
        | taken ch j =>
          rw [ho2] at ht
          by_cases h0 : ch = 0
          · subst h0
            have ht0 : ((tablesOf r₁.1)[j]?).bind id = some pt := ht
            have ht' : ((tablesOf r₁.1)[(srcOf 2 o.2).2]?).bind id = some pt := by
              rw [ho2]
              exact ht0
            have hd := depth_of_table hp (i := 2) (by simp) hr' ho (j := 0)
              (bs := F.first.blocksInOrder) (by simp) (by rw [ho2]; rfl) s1 Y1 o1 ht'
            exact hc1 j k pt ht0 (by rw [← hd]; exact hk')
          · by_cases h1 : ch = 1
            · subst h1
              have ht0 : ((tablesOf r₂.1)[j]?).bind id = some pt := ht
              have ht' : ((tablesOf r₂.1)[(srcOf 2 o.2).2]?).bind id = some pt := by
                rw [ho2]
                exact ht0
              have hd := depth_of_table hp (i := 2) (by simp) hr' ho (j := 1)
                (bs := F.shared.blocksInOrder) (by simp) (by rw [ho2]; rfl) s2 Y2 o2 ht'
              show colOf C D y _ _ _ (.tree (F.t₁ + j) k) = _
              rw [e1]
              exact hc2 j k pt ht0 (by rw [← hd]; exact hk')
            · have hnone : treeThird r₁.1 r₂.1 r₃.1 (.taken ch j) = none := by
                simp [treeThird, h0, h1]
              rw [hnone] at ht
              cases ht

end

end ProofFile.Honest

#print axioms ProofFile.Honest.map_zip_snd
#print axioms ProofFile.Honest.steps_pairs
#print axioms ProofFile.Honest.steps_sent
#print axioms ProofFile.Honest.tables_len
#print axioms ProofFile.Honest.sum_fits
#print axioms ProofFile.Honest.drawnT_length
#print axioms ProofFile.Honest.reads_seal
#print axioms ProofFile.Honest.readyShared_ok
#print axioms ProofFile.Honest.seamAt_ok
#print axioms ProofFile.Honest.col_first
#print axioms ProofFile.Honest.col_shared
#print axioms ProofFile.Honest.col_second
#print axioms ProofFile.Honest.lt_of_bind_some
#print axioms ProofFile.Honest.depth_of_table
#print axioms ProofFile.Honest.view_eq
#print axioms ProofFile.Honest.sealQuiet_snoc
#print axioms ProofFile.Honest.sealQuiet_one
#print axioms ProofFile.Honest.yields_one
#print axioms ProofFile.Honest.views_of_requestStrategy
