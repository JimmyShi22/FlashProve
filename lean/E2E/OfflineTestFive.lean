-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineTestFive.lean: five of the eight clauses that the conditions `OnFree` and `OnFreeT`
(Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFree.lean, TreesExact.lean) ask at the entry of a proximity
test's second part, AT A RUN's OWN VALUES, in the form in which `owedAt_first_at`
(E2E/OfflineOwedChains.lean) asks On: at every carried block and every state that the frame returns at
the part's address, at the run's own front. General in the description, the book, the prover, the
lists and the job. First chain.

  `FiveAtEntry`        the five clauses le, leS, heardFit, heard, fold, in `OnFree`'s own letters
  `TestPublic`         what is asked of the job's public part
  `ThreeAtEntry`       the three that are left, door, asks, tree, in `OnFree`'s own letters
  `onFree_of_five`     `OnFree` from the five and the three, by its constructor: so the two structures'
                       clauses are `OnFree`'s to the letter
  `two_of_map`, `find_of_nodup`, `StandsAt.of_same`   three small lemmas
  `five_at_first_row`  the theorem: by `five_at_first` (…/K12/FiveAtFirst.lean)

It pays none of door, asks, tree. At a state on entry that is the job's own letter rec₀, not shown to be
the verifier's. Where the first fold's fresh table has come earlier alone. That a run returns, or calls
the part, is not shown here. Nothing on any property.
-/
import E2E.OfflineOwedFirst
import Johnson.Desc.ProofFile.Honest.K12.FiveAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFree
import Johnson.SendSim.Seat.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block FileDescription Place)
open Johnson.Prover.Link (μOf rowOf asked bodyItems)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)

/-- **The five clauses**, in `OnFree`'s own letters. mem: the stretches that the part carries. -/
structure FiveAtEntry {W X : Type} (J : TestJob W X) (mem : ℕ → K12.Stretch) (m : Mid W X)
    (front : Before) : Prop where
  le : firstLen J.p.nums.stages ≤ m.st.heard.length
  leS : firstLen J.p.nums.stages ≤ m.seen.length
  heardFit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
    (m.st.lately (firstLen J.p.nums.stages)) = true
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
    m.st.lately (firstLen J.p.nums.stages)
  fold : (lastSeen front (firstLen J.p.nums.stages)).tail =
    aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (K12.rowsAt J mem m)
      (rowOf (J.recB m.st.input (restFront J m) (heardIn J m 0))) (heardIn J m)

/-- **The three clauses that are left**, in `OnFree`'s own letters: `door`: the two jobs' letters for the
state on entry give one state · `asks`: that state's shape, and the prover's data against it, among them
that the group's open rows say true things of the members' words · `tree`: one tree in front, and what the
front lists of it is the tree's. -/
structure ThreeAtEntry {W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (pb : Pb) (mem : ℕ → K12.Stretch) (m : Mid W X)
    (front : Before) : Prop where
  door : J.rec₀ m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  asks : ∃ Dp cc R, Dp.ts.length = 1 ∧
    ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R
  tree : ∃ colR cols, J.trees₀ m.st.input (restFront J m) mem (K12.rowsAt J mem m) =
      [((sgOf J.s₀).C.a, colR)] ∧
    front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
    ∀ q ∈ cols, q.2 = colR q.1

/-- **`OnFree` from the five and the three.** -/
theorem onFree_of_five {W X Pb : Type} {J : TestJob W X} {Js : SimJob Pb} {K : OnBytes.Codes}
    {chain : ℕ} {o : Fmt.Shape × Fmt.TreeSource} {pb : Pb} {mem : ℕ → K12.Stretch} {m : Mid W X}
    {front : Before} (A : FiveAtEntry J mem m front)
    (E : ThreeAtEntry J Js K chain o pb mem m front) : OnFree J Js K chain o pb mem m front :=
  ⟨A.le, A.leS, A.heardFit, A.heard, E.door, A.fold, E.asks, E.tree⟩

/-- **What is asked of the job's public part**: two stages or more, k = h + g at the first; the place
declares enough rounds, of the text's sorts; the declared oracle messages fit the text's tables; the
first stage's rows read the members' stretches alone. -/
structure TestPublic {W X : Type} (J : TestJob W X) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) : Prop where
  stages : J.p.nums.stages = s :: next :: rest
  split : s.k = (sgOf s).h + (sgOf s).g
  enough : firstLen J.p.nums.stages ≤ (laidOf J.p).length
  sorts : (laidOf J.p).map asked = [] :: bodyItems s (next :: rest)
  tables : tablesFitB J = true
  rows : ∀ (w : W) (fr : Front X) (mem mem' : ℕ → K12.Stretch),
    (∀ t, t < J.members.length → mem t = mem' t) →
    μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem')

/-- A list of pairs whose first entries are two. -/
theorem two_of_map {α β : Type} {l : List (α × β)} {a b : α} (h : l.map (·.1) = [a, b]) :
    ∃ x y, l = [(a, x), (b, y)] := by
  rcases l with _ | ⟨⟨a', x⟩, _ | ⟨⟨b', y⟩, _ | ⟨z, t⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨x, y, rfl⟩
  · simp at h

/-- Where no two halves are at one place, the search by a half's place finds it. -/
theorem find_of_nodup {V W Y : Type} : ∀ {l : List (Placed V W Y)}, (l.map (·.place)).Nodup →
    ∀ {g : Placed V W Y}, g ∈ l → (l.find? fun h => h.place == g.place) = some g
  | [], _, _, hg => by cases hg
  | a :: l, hn, g, hg => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact List.find?_cons_of_pos (by simp)
    · have hne : ¬ (a.place == g.place) = true := by
        intro e
        exact hn.1 (by rw [beq_iff_eq.1 e]; exact List.mem_map_of_mem hg')
      rw [List.find?_cons_of_neg (p := fun h : Placed V W Y => h.place == g.place) hne]
      exact find_of_nodup hn.2 hg'

/-- `StandsAt` reads of a member its number and its rounds alone. -/
theorem StandsAt.of_same {S Cl V W Y Pb : Type} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    {σ : Side S Cl V W Y Pb} {u u' : Member V W Y Pb} {pre t : List (Block S Cl)} {i i' : Nat}
    (hn : u.number = u'.number) (hr : u.rounds = u'.rounds) (hi : i = i')
    (A : StandsAt bs ss σ u pre t i) : StandsAt bs ss σ u' pre t i' := by
  subst hi
  exact ⟨A.cut, hr ▸ A.le, hr ▸ A.pos, hr ▸ A.fits, hn ▸ hr ▸ A.str, hr ▸ A.own⟩

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {r : RunC F}

/-- **The five clauses at a run's own values, at the second part of a proximity test of the first
chain.** Js: any simulators' job: nothing is read of it. -/
theorem five_at_first_row (plan : F.planOk = true) (book : Bk.word F = none)
    (due : ρ.due F = true) (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hL : L ∈ G.first)
    {σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : L.side F.first.blocksInOrder = some σ) (J : TestJob (Local W₀ Rc Xi Tr) X) (Js : SimJob Xi)
    (f : Addr × ℕ) (hfr : J.fresh = some f) (hpl : L.place = J.p.place)
    (hparts : L.row.map (·.1) = [firstPart J, restPart J])
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (P : TestPublic J s next rest) (st : List (ℕ × ℕ × List UInt64)) :
    ∀ u ∈ σ.members, u.number = 1 → r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry J (stretches _ ca) m (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  intro u hu hn hc ca m hca hm
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  have hbp : σ.block.place = L.place := side_place hσ
  have hrowσ : σ.row = L.row := OnBytes.SendSim.Seat.row_of_seated hσ
  obtain ⟨s0, s1, hrow⟩ := two_of_map hparts
  obtain ⟨⟨hsum, hor⟩, hst⟩ := first_stands plan book hR L hL σ hσ
  have e0 : (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).moves.length =
      firstLen J.p.nums.stages := Light.first_moves_len J
  have e1 : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest P.stages]
    exact (List.length_map _).trans List.length_range
  have hlen : J.laid.length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    rw [← hlaid, List.length_zip, hor, Nat.min_self, ← hsum, hrowσ, hrow]
    simp [e0, e1]
  have ht : (J.laid.drop (firstLen J.p.nums.stages)).take (restLen J.p.nums.stages) =
      J.laid.drop (firstLen J.p.nums.stages) :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  have hmem : σ.members = [⟨0, J.laid.take (firstLen J.p.nums.stages), firstPart J, s0⟩,
      ⟨1, J.laid.drop (firstLen J.p.nums.stages), restPart J, s1⟩] := by
    unfold Side.members
    rw [hrowσ, hrow, hlaid]
    show [_, _] = _
    simp only [e0, e1, ht, Nat.zero_add]
  rw [hmem] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact absurd (show (0 : ℕ) = 1 from hn) (by decide)
  obtain ⟨⟨pre, t, A⟩, -⟩ := hst ⟨1, J.laid.drop (firstLen J.p.nums.stages), restPart J, s1⟩
    (by rw [hmem]; exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  have hto : σ.roundsTo 1 = firstLen J.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrowσ, hrow]
    simp [e0]
  have A' : StandsAt F.first.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages) :=
    StandsAt.of_same (u := ⟨1, J.laid.drop (firstLen J.p.nums.stages), restPart J, s1⟩) rfl rfl hto A
  obtain ⟨hte, -⟩ := ready_ok hR
  obtain ⟨t1, -, -⟩ := tests_twice hte
  have hgm : (proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) ∈
      (G.prover H).first :=
    List.mem_map.2 ⟨L, hL, by rw [hpl, hparts]; rfl⟩
  have hg : ((G.prover H).first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J) := by
    rw [hbp, hpl]
    exact find_of_nodup (nodup_of_twice t1) hgm
  have hd1 : drawsFit F.roundsDeclaredByBlocks.1 ρ.first = true := by
    unfold Draws.due at due
    simp only [Bool.and_eq_true] at due
    exact due.1.1.1
  have hdecl : F.roundsDeclaredByBlocks.1 =
      pre.flatMap (·.rounds) ++ (σ.block.rounds ++ t.flatMap (·.rounds)) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [A.cut, List.flatMap_append, List.flatMap_cons]
  have hfst : J.laid.map (·.1) = σ.block.rounds := by
    rw [← hlaid]
    exact List.map_fst_zip (le_of_eq hor.symm)
  have hle : firstLen J.p.nums.stages ≤ σ.block.rounds.length := by
    rw [← hfst, List.length_map, hlen]
    omega
  have hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    have h2 := (drawsFit_cut (pre.flatMap (·.rounds)).length _ _ hd1).2
    rw [hdecl, List.drop_left] at h2
    have h3 := (drawsFit_cut (firstLen J.p.nums.stages) _ _ h2).1
    rw [List.take_append_of_le_length hle] at h3
    rw [List.map_take]
    show drawsFit ((J.laid.map (·.1)).take _) _ = true
    rw [hfst]
    exact h3
  have hdl := ProofFile.Honest.drawsFit_length _ _ hfit
  have T : FirstTies J s next rest
      (fun i => ((ρ.first.drop (pre.flatMap (·.rounds)).length).take
        (firstLen J.p.nums.stages)).getD i noDraw)
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨P.stages, P.enough, P.sorts, P.tables, by
      rw [hdl, List.length_map, List.length_take]
      exact Nat.min_eq_left P.enough, fun n hn' => (List.getD_eq_getElem _ _ hn').symm⟩
  obtain ⟨c, m', hm', hca', -, a1, a2, a3, a4, a5⟩ := Light.five_at_first plan J f hfr Js hR σ pre t
    A' hg hlaid hT s next rest _ T P.split P.rows hfit h (by rw [hbp]; exact hc) st
  rw [hbp] at hm' hca' a4 a5
  have em : m' = m := by
    have e : orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩) = .ok m' := by
      rw [show midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m') from hm']
      rfl
    exact Except.ok.inj (e.symm.trans hm)
  have ec : c.2.1.2.2 = ca := Except.ok.inj (hca'.symm.trans hca)
  subst em
  subst ec
  exact ⟨a1, a2, a3, a4, a5⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.onFree_of_five
#print axioms AtPublicFiles.OfflineRows.two_of_map
#print axioms AtPublicFiles.OfflineRows.find_of_nodup
#print axioms AtPublicFiles.OfflineRows.StandsAt.of_same
#print axioms AtPublicFiles.OfflineRows.five_at_first_row
