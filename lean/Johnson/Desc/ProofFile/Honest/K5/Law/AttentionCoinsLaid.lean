-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionCoinsLaid.lean: coins laid out in rounds, and three laws
by name: what a part shows, what a simulator tells, and the uniform law laid out in rounds. General in
all types: no kind is named. Definitions, and statements with their proofs.

They stand apart from the files on the attention segments' own rounds (kind K5) because the search for
instances in those files' larger scope runs out of its budget at the uniform laws. There the laws are
named and never written out.

  laidOut, wordsOf          elements cut into rounds of the given lengths; a vector as a list
  ShownLaw, ToldLaw, UniformLaid   the three laws
  told_law_of               a simulator that tells its coins laid out has the law UniformLaid
  laidOut_wordsOf_injective  the map under UniformLaid is one to one: so that law is uniform on its
                            image
  exact_iff_laws            ExactAtOneTable is the equation of ShownLaw and ToldLaw, by definition
  shows_some_of_law, one_point_of_law   what an equation of laws gives

Limits. These are statements on laws over coins taken as uniform. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ExactAtOneTable
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExactAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Slice (ofE)
open ProofFile.Honest.SumLaw (StatedBy)

/-! ## 1 The layout -/

/-- **Elements laid out in rounds of the given lengths**, each round showing its elements in the clear
and no column. -/
def laidOut (ns : List Nat) (l : List E) : List Shown :=
  (roundsCut ns l).map fun t => ⟨t.map fun y => .e y.triple, []⟩

/-- A vector of elements of the field as the program's elements: what coinsE makes of coins. -/
def wordsOf {n : Nat} (v : Fin n → Cb.Gl.E) : List E := List.ofFn fun i => E.ofTriple (ofE (v i))

theorem roundsCut_length : ∀ (ns : List Nat) (l : List E), (roundsCut ns l).length = ns.length
  | [], _ => rfl
  | _ :: ns, _ => congrArg (· + 1) (roundsCut_length ns _)

theorem laidOut_length (ns : List Nat) (l : List E) : (laidOut ns l).length = ns.length := by
  unfold laidOut
  rw [List.length_map, roundsCut_length]

/-- Read in order, the rounds' items are the elements. Conditional: hl: they are no more than the
rounds hold. -/
theorem laidOut_vals (ns : List Nat) (l : List E) (hl : l.length ≤ ns.sum) :
    (laidOut ns l).flatMap (·.vals) = l.map fun y => Fmt.ItemValue.e y.triple := by
  unfold laidOut
  rw [List.flatMap_map]
  show (roundsCut ns l).flatMap (List.map fun y => Fmt.ItemValue.e y.triple) = _
  rw [List.flatMap_def, ← List.map_flatten, SumLaw.At.roundsCut_join, List.take_of_length_le hl]

/-- The cut by numbers has these lengths, where the list is long enough. -/
theorem roundsCut_counts : ∀ (ns : List Nat) (l : List E), ns.sum ≤ l.length →
    (roundsCut ns l).map List.length = ns
  | [], _, _ => rfl
  | n :: ns, l, h => by
    have hn : n + ns.sum ≤ l.length := by simpa using h
    have hm : min n l.length = n := by omega
    show (l.take n).length :: (roundsCut ns (l.drop n)).map List.length = n :: ns
    rw [List.length_take, hm, roundsCut_counts ns _ (by rw [List.length_drop]; omega)]

/-- Round by round, as many items as the numbers say, where the list is long enough. -/
theorem laidOut_counts (ns : List Nat) (l : List E) (hl : ns.sum ≤ l.length) :
    (laidOut ns l).map (·.vals.length) = ns := by
  unfold laidOut
  rw [List.map_map]
  refine Eq.trans (List.map_congr_left fun t _ => List.length_map _) (roundsCut_counts ns l hl)

/-- What declared rounds state, as numbers. -/
theorem stated_counts : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)),
    StatedBy ns rs → (rs.map fun x => (x.1.items.filter (· != .root)).length) = ns
  | [], [], _ => rfl
  | n :: ns, r :: rs, h => by
    show (r.1.items.filter (· != .root)).length ::
      (rs.map fun x => (x.1.items.filter (· != .root)).length) = n :: ns
    rw [h.1, List.length_replicate, stated_counts ns rs h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem laidOut_cols (ns : List Nat) (l : List E) : ∀ t ∈ laidOut ns l, t.cols = [] := by
  intro t ht
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 ht
  rfl

/-- **Laid out in rounds, a vector is told apart from every other vector.** So the law UniformLaid
below is the image of the uniform law under a map that is one to one. -/
theorem laidOut_wordsOf_injective (ns : List Nat) (v v' : Fin ns.sum → Cb.Gl.E)
    (h : laidOut ns (wordsOf v) = laidOut ns (wordsOf v')) : v = v' := by
  have hl : ∀ w : Fin ns.sum → Cb.Gl.E, (wordsOf w).length ≤ ns.sum :=
    fun w => (List.length_ofFn).le
  have h1 : (laidOut ns (wordsOf v)).flatMap (·.vals) = (laidOut ns (wordsOf v')).flatMap (·.vals) := by
    rw [h]
  rw [laidOut_vals ns _ (hl v), laidOut_vals ns _ (hl v')] at h1
  unfold wordsOf at h1
  rw [List.map_ofFn, List.map_ofFn] at h1
  have h2 := List.ofFn_injective h1
  funext i
  have h3 : (E.ofTriple (ofE (v i))).triple = (E.ofTriple (ofE (v' i))).triple :=
    Fmt.ItemValue.e.inj (congrFun h2 i)
  rw [E.triple_ofTriple, E.triple_ofTriple] at h3
  have h4 := congrArg OnBytes.Slice.toE h3
  rwa [OnBytes.Slice.toE_ofE, OnBytes.Slice.toE_ofE] at h4

/-! ## 2 Two lemmas on laws -/

/-- Coins of the extension field, through a function of coinsE, have the law of a uniform vector. -/
theorem law_of_coins {β : Type} (n : Nat) (G : List E → β) :
    (Prob.unif (Cs ⟨0, n⟩)).map (fun c => G (coinsE c)) =
      (Prob.unif (Fin n → Cb.Gl.E)).map fun v => G (wordsOf v) := by
  let f : Cs ⟨0, n⟩ → (Fin n → Cb.Gl.E) := fun c => c.e
  have hb : Function.Bijective f :=
    ⟨fun a b h => SumLaw.cs_ext a b (congrFun h), fun v => ⟨⟨fun i => i.elim0, v⟩, rfl⟩⟩
  rw [← Prob.map_unif_of_bijective hb, PMF.map_comp]
  rfl

/-- Where two laws are one and the right one is never none, the left one is never none. -/
theorem some_of_law {A B γ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    {F : A → Option γ} {G : B → Option γ} (h : (Prob.unif A).map F = (Prob.unif B).map G)
    (hG : ∀ b, (G b).isSome = true) (a : A) : (F a).isSome = true := by
  have ha : F a ∈ ((Prob.unif A).map F).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨a, PMF.mem_support_uniformOfFintype _, rfl⟩
  rw [h] at ha
  obtain ⟨b, -, hb⟩ := (PMF.mem_support_map_iff _ _ _).1 ha
  rw [← hb]
  exact hG b

/-- Where one law is over a type with at most one value, the other function has one value. -/
theorem law_one_point {A B γ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] {F : A → γ}
    {G : B → γ} (h : (Prob.unif A).map F = (Prob.unif B).map G) (hA : ∀ a a' : A, a = a') (b b' : B) :
    G b = G b' := by
  have key : ∀ b, ∃ a, F a = G b := fun b => by
    have hb : G b ∈ ((Prob.unif B).map G).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨b, PMF.mem_support_uniformOfFintype _, rfl⟩
    rw [← h] at hb
    obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).1 hb
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := key b
  obtain ⟨a', ha'⟩ := key b'
  rw [← ha, ← ha', hA a a']

/-! ## 3 The three laws by name -/

section Laws
variable {S Cl V W X Pb : Type}

/-- **What a part shows**, over the coins that it takes and the blocks that it spends, all else fixed:
the left side of the field exact of Good (Honest/Side.lean). -/
noncomputable def ShownLaw (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : Mid W X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) : PMF (Option (List Shown)) :=
  (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map fun c =>
    σ.shows φ u (c.1, c.2, ca) m ds asks

/-- **What a simulator tells**, over its own coins, all else fixed: the right side of that field, at x
the public field of the part's input. -/
noncomputable def ToldLaw (s : Sim Pb) (x : Pb) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) : PMF (Option (List Shown)) :=
  (Prob.unif (Cs s.takes)).map fun c => s.tell x front ds asks c

/-- **The uniform law on as many elements of the extension field as the numbers add up to, laid out in
rounds of these lengths.** The map is one to one: laidOut_wordsOf_injective. -/
noncomputable def UniformLaid (ns : List Nat) : PMF (Option (List Shown)) :=
  (Prob.unif (Fin ns.sum → Cb.Gl.E)).map fun v => some (laidOut ns (wordsOf v))

/-- **The law of what a simulator tells, where it tells its coins laid out in rounds.** -/
theorem told_law_of (s : Sim Pb) (ns : List Nat) (ht : s.takes = ⟨0, ns.sum⟩)
    (x : Pb) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hc : ∀ c : Cs s.takes, s.tell x front ds asks c = some (laidOut ns (coinsE c))) :
    ToldLaw s x front ds asks = UniformLaid ns := by
  obtain ⟨a, d, tell⟩ := s
  obtain rfl : d = ⟨0, ns.sum⟩ := ht
  have e : (fun c => tell x front ds asks c) = fun c => some (laidOut ns (coinsE c)) :=
    funext hc
  show (Prob.unif (Cs ⟨0, ns.sum⟩)).map (fun c => tell x front ds asks c) = _
  rw [e]
  exact law_of_coins ns.sum fun l => some (laidOut ns l)

/-- Where what a part shows has the law of what a simulator tells, and the simulator always returns,
the part shows something at every coin. -/
theorem shows_some_of_law {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {u : Member V W X Pb}
    {ca : CsAll u.part.carries} {m : Mid W X} {ds : List Fmt.Drawn}
    {asks : List (List (List Nat))} {s : Sim Pb} {x : Pb} {front : Before}
    (h : ShownLaw φ σ u ca m ds asks = ToldLaw s x front ds asks)
    (hT : ∀ c, (s.tell x front ds asks c).isSome = true)
    (c : Cs u.part.takes × CsAll u.part.spends) :
    (σ.shows φ u (c.1, c.2, ca) m ds asks).isSome = true :=
  some_of_law (F := fun c : Cs u.part.takes × CsAll u.part.spends =>
    σ.shows φ u (c.1, c.2, ca) m ds asks) h hT c

/-- Where a part's coins have at most one value and what it shows has the law of what a simulator
tells, the simulator tells one thing. -/
theorem one_point_of_law {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {u : Member V W X Pb}
    {ca : CsAll u.part.carries} {m : Mid W X} {ds : List Fmt.Drawn}
    {asks : List (List (List Nat))} {s : Sim Pb} {x : Pb} {front : Before}
    (h : ShownLaw φ σ u ca m ds asks = ToldLaw s x front ds asks)
    (hA : ∀ a a' : Cs u.part.takes × CsAll u.part.spends, a = a') (b b' : Cs s.takes) :
    s.tell x front ds asks b = s.tell x front ds asks b' :=
  law_one_point (F := fun c : Cs u.part.takes × CsAll u.part.spends =>
    σ.shows φ u (c.1, c.2, ca) m ds asks) (G := fun c => s.tell x front ds asks c) h hA b b'

end Laws

section AtOneTable
variable {S Cl W₀ Rc Xi Tr X : Type}

/-- **ExactAtOneTable is the equation of the two laws.** Definitional. -/
theorem exact_iff_laws (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) →
      CsAll u.part.carries → Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ExactAtOneTable σ On bud pre ↔
      ∀ (index : W₀) (table : Rc) (x : Xi) (trace : Tr), ∀ u ∈ σ.members,
        ∀ ca (m : Mid (Local W₀ Rc Xi Tr) X) front ds asks,
          m.st.input = ⟨index, table, x, trace⟩ → On u ca m front → m.seen = front.seen →
          m.opened = front.opened (readsBefore pre front) →
          drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
          front.holds 0 0 (u.rounds.map (·.1)) ds = true →
          u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
          ShownLaw .own σ u ca m ds asks = ToldLaw u.sim x front ds asks :=
  Iff.rfl

end AtOneTable

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.laidOut
#print axioms ProofFile.Honest.K5.wordsOf
#print axioms ProofFile.Honest.K5.laidOut_vals
#print axioms ProofFile.Honest.K5.laidOut_counts
#print axioms ProofFile.Honest.K5.stated_counts
#print axioms ProofFile.Honest.K5.law_of_coins
#print axioms ProofFile.Honest.K5.ShownLaw
#print axioms ProofFile.Honest.K5.ToldLaw
#print axioms ProofFile.Honest.K5.UniformLaid
#print axioms ProofFile.Honest.K5.told_law_of
#print axioms ProofFile.Honest.K5.shows_some_of_law
#print axioms ProofFile.Honest.K5.laidOut_wordsOf_injective
#print axioms ProofFile.Honest.K5.exact_iff_laws
#print axioms ProofFile.Honest.K5.one_point_of_law
