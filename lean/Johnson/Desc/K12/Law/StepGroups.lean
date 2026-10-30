-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StepGroups.lean: the first half of GroupsAre
(Johnson/Desc/K12/Law/FirstRead.lean: group by group the positions are the tree's own list under the
draws) from a yes of Block.step, at the first stage of the proximity test (the kind K12).

It stands over groupsOf, regroup, roundsFit and Block.step (Johnson/Desc/Block.lean), proximityTestKind and
stagesFrom (Johnson/Desc/K12/Frame.lean), nOpen, cutF, cutS and grpS
(Johnson/Desc/K12/Law/JointK.lean), laidOf, laidS and grpsS (Johnson/Desc/K12/Law/ReadsK.lean).
Statements and proofs.
Main names:
  `kpw`, `regroup_pos`: under the step's test "the columns" each dealt group stands at its declared
    list of positions.
  `nOpen_cons`, `nOpen_append`, `grp1`, `groupsOf_cons`, `groupsOf_drop`, `groupsOf_take`: groupsOf
    along a cut of the rounds.
  `groups_cut`: the dealt groups of the n rounds from number i on.
  `groupsOf_two`: two rounds of which the first opens nothing and neither reads a stored table.
  `first_half`: such groups stand at the trees' own lists (ownAt_ofDraws), under one bound: every
    draw is below 2 ^ a.
  `groupsAre_of`: the two halves make GroupsAre.
  `grpS_first`: at the place: what the frame deals to the first switch.
  `stagesFrom_rounds`, `k12_rounds`: where the block's test on the plan says yes, the block's rounds
    are the place's declared rounds.
  `roundsFit_length`: roundsFit's yes gives as many rounds as are declared.
  `first_half_of_step`: the whole.
Limits: No soundness is claimed, and nothing is said on hiding. The law of the proximity test is not
proved here.
What is left of GroupsAre is its second half: each column of group t is the written column of the
tree at the t-th opening.
No lemma of `verify-on-bytes` is called here; of the library the pure functions ownAt,
Positions.ofDraws and Fmt.listOf, through ownAt_ofDraws (Johnson/Desc/K12/Law/FirstRead.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

abbrev Want : Type := ℕ × ℕ × ℕ

/-- Key, position and width of a column: what Block.step's test "the columns" compares. -/
def kpw (c : VerifiableInference.Desc.OpenedColumn) : Want := (c.1, c.2.1, c.2.2.length)

/-- (a) Under the step's test on the columns each dealt group stands at its declared list of
positions. -/
theorem regroup_pos : ∀ (groups : List (List Want)) (got : List VerifiableInference.Desc.OpenedColumn),
    got.map kpw = groups.flatMap id →
    (regroup (groups.map (·.length)) got).map (·.map (·.1)) = groups.map (·.map (·.2.1))
  | [], _, _ => rfl
  | g :: gs, got, h => by
    rw [List.flatMap_cons] at h
    have h1 : (got.take g.length).map kpw = g := by
      rw [List.map_take, h]
      exact List.take_left' rfl
    have h2 : (got.drop g.length).map kpw = gs.flatMap id := by
      rw [List.map_drop, h]
      exact List.drop_left' rfl
    show (((got.take g.length).map fun c => (c.2.1, c.2.2)).map (·.1)) ::
      (regroup (gs.map (·.length)) (got.drop g.length)).map (·.map (·.1)) = _
    rw [regroup_pos gs _ h2, List.map_cons, List.map_map]
    congr 1
    conv_rhs => rw [← h1, List.map_map]
    rfl

theorem nOpen_cons (d : Fmt.DeclaredRound) (l : List Fmt.DeclaredRound) :
    nOpen (d :: l) = d.stored.length + d.opens.length + nOpen l := by
  unfold nOpen
  rw [List.foldl_cons]
  have : ∀ (l : List Fmt.DeclaredRound) (n : ℕ),
      l.foldl (fun n r => n + r.stored.length + r.opens.length) n =
        n + l.foldl (fun n r => n + r.stored.length + r.opens.length) 0 := by
    intro l
    induction l with
    | nil => intro n; rfl
    | cons x l ih =>
      intro n
      rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + _ + _)]
      omega
  rw [this]
  omega

theorem nOpen_append (l m : List Fmt.DeclaredRound) : nOpen (l ++ m) = nOpen l + nOpen m := by
  induction l with
  | nil => simp [nOpen]
  | cons d l ih => rw [List.cons_append, nOpen_cons, nOpen_cons, ih]; omega

/-- The groups of one round. -/
def grp1 (F : ℕ) (d : Fmt.DeclaredRound) (R : Fmt.Drawn) : List (List Want) :=
  (d.stored.map fun s =>
    (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
      (Fmt.storedKey s.item, x, s.sh.W)) ++
  (d.opens.map fun o =>
    (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x => (o.1.tree - F, x, o.1.W))

theorem groupsOf_cons (F : ℕ) (d : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound) (R : Fmt.Drawn)
    (Rs : List Fmt.Drawn) : groupsOf F (d :: ds) (R :: Rs) = grp1 F d R ++ groupsOf F ds Rs := by
  show _ ++ _ ++ _ = _
  rfl

theorem grp1_length (F : ℕ) (d : Fmt.DeclaredRound) (R : Fmt.Drawn) :
    (grp1 F d R).length = d.stored.length + d.opens.length := by
  unfold grp1
  simp

/-- (b) groupsOf along a cut: behind the groups of the first i rounds stand the groups of the rest.
-/
theorem groupsOf_drop (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (i : ℕ),
    ds.length = Rs.length →
    (groupsOf F ds Rs).drop (nOpen (ds.take i)) = groupsOf F (ds.drop i) (Rs.drop i)
  | _, _, 0, _ => rfl
  | [], [], _ + 1, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | d :: ds, R :: Rs, i + 1, h => by
    rw [List.take_succ_cons, nOpen_cons, groupsOf_cons, ← grp1_length F d R, ← List.drop_drop,
      List.drop_left]
    exact groupsOf_drop F ds Rs i (by simpa using h)

/-- … and the groups of the first n rounds come first. -/
theorem groupsOf_take (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (n : ℕ),
    ds.length = Rs.length →
    (groupsOf F ds Rs).take (nOpen (ds.take n)) = groupsOf F (ds.take n) (Rs.take n)
  | _, _, 0, _ => by simp [nOpen, groupsOf]
  | [], [], _ + 1, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | d :: ds, R :: Rs, n + 1, h => by
    rw [List.take_succ_cons, List.take_succ_cons, nOpen_cons, groupsOf_cons, groupsOf_cons,
      ← grp1_length F d R, List.take_length_add_append]
    rw [groupsOf_take F ds Rs n (by simpa using h)]

/-- (c) The dealt groups along a cut: the groups of the n rounds from number i on stand at these
rounds' declared lists. -/
theorem groups_cut (F : ℕ) (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn)
    (got : List VerifiableInference.Desc.OpenedColumn) (hlen : ds.length = Rs.length)
    (hcols : got.map kpw = (groupsOf F ds Rs).flatMap id) (i n : ℕ) :
    (((regroup ((groupsOf F ds Rs).map (·.length)) got).drop (nOpen (ds.take i))).take
      (nOpen ((ds.drop i).take n))).map (·.map (·.1)) =
      (groupsOf F ((ds.drop i).take n) ((Rs.drop i).take n)).map (·.map (·.2.1)) := by
  rw [List.map_take, List.map_drop, regroup_pos _ _ hcols, ← List.map_drop, ← List.map_take,
    groupsOf_drop F ds Rs i hlen, groupsOf_take F _ _ n (by simp [hlen])]

/-- (d) Two rounds of which the first opens nothing and neither reads a stored table: a group for
each tree that the second opens, at the list of its draws in the tree's own range. -/
theorem groupsOf_two (F : ℕ) (dS dC : Fmt.DeclaredRound) (RS RC : Fmt.Drawn) (h1 : dS.stored = [])
    (h2 : dS.opens = []) (h3 : dC.stored = []) :
    (groupsOf F [dS, dC] [RS, RC]).map (·.map (·.2.1)) =
      dC.opens.map fun o => Fmt.listOf (RC.poss.map (· % 2 ^ o.1.a)) := by
  rw [groupsOf_cons, groupsOf_cons]
  unfold grp1
  rw [h1, h2, h3]
  simp [groupsOf, Function.comp_def]

/-- (e) GroupsAre's first half. gs: the groups dealt; opens: what is declared as opened; their
depths are the book's trees' (gpOk's clause opens.a); every draw lies in the range. -/
theorem first_half (log : ℕ → ℕ) (a : ℕ) (poss : List ℕ) (hr : ∀ x ∈ poss, x < 2 ^ a) :
    ∀ (ts : List ℕ) (opens : List (Fmt.Shape × Fmt.TreeSource)) (gs : Gs),
    gs.map (·.map (·.1)) = opens.map (fun o => Fmt.listOf (poss.map (· % 2 ^ o.1.a))) →
    opens.map (·.1.a) = ts.map log →
    List.Forall₂ (fun t grp => grp.map (·.1) = (ownAt (log t) (Positions.ofDraws a poss)).toList)
      ts gs
  | [], [], [], _, _ => List.Forall₂.nil
  | [], [], _ :: _, h, _ => by simp at h
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: _, _ :: _, [], h, _ => by simp at h
  | t :: ts, o :: os, g :: gs, h1, h2 => by
    rw [List.map_cons, List.map_cons] at h1 h2
    obtain ⟨a1, a2⟩ := List.cons.inj h1
    obtain ⟨b1, b2⟩ := List.cons.inj h2
    refine List.Forall₂.cons ?_ (first_half log a poss hr ts os gs a2 b2)
    rw [a1, ownAt_ofDraws a _ poss hr, ← b1]

/-- (f) The two halves make GroupsAre. -/
theorem groupsAre_of (pos : Positions) (log : ℕ → ℕ) (g : ℕ → ℕ → Option (List UInt64)) :
    ∀ (ts : List ℕ) (gs : Gs),
    List.Forall₂ (fun t grp => grp.map (·.1) = (ownAt (log t) pos).toList) ts gs →
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ c ∈ grp, g t c.1 = some c.2) ts gs →
    GroupsAre pos log g ts gs
  | [], [], _, _ => List.Forall₂.nil
  | _ :: ts, _ :: gs, hA, hB => by
    obtain ⟨a1, a2⟩ := List.forall₂_cons.1 hA
    obtain ⟨b1, b2⟩ := List.forall₂_cons.1 hB
    exact List.Forall₂.cons ⟨a1, b1⟩ (groupsAre_of pos log g ts gs a2 b2)

/-- (g) At the place: the groups that the frame deals to the first switch stand at the declared
lists of the switch's two rounds. Rs: what the test's rounds drew. -/
theorem grpS_first (p : P12) (F : ℕ) (Rs : List Fmt.Drawn)
    (got : List VerifiableInference.Desc.OpenedColumn) (k : ℕ)
    (hlen : ((laidOf p).map (·.1)).length = Rs.length)
    (hcols : got.map kpw = (groupsOf F ((laidOf p).map (·.1)) Rs).flatMap id) :
    (grpS (laidS p) k (grpsS p
      (regroup ((groupsOf F ((laidOf p).map (·.1)) Rs).map (·.length)) got))).map (·.map (·.1)) =
      (groupsOf F (cutS (laidS p) k) ((Rs.drop (1 + (1 + k))).take 2)).map (·.map (·.2.1)) := by
  have h := groups_cut F ((laidOf p).map (·.1)) Rs got hlen hcols (1 + (1 + k)) 2
  have e1 : ((laidOf p).take 1).map (·.1) = ((laidOf p).map (·.1)).take 1 := List.map_take
  have e2 : (((laidOf p).drop 1).take (1 + k)).map (·.1) =
      (((laidOf p).map (·.1)).drop 1).take (1 + k) := by rw [List.map_take, List.map_drop]
  have e3 : ((((laidOf p).drop 1).drop (1 + k)).take 2).map (·.1) =
      (((laidOf p).map (·.1)).drop (1 + (1 + k))).take 2 := by
    rw [List.map_take, List.map_drop, List.map_drop, List.drop_drop]
  have e4 : nOpen (((laidOf p).map (·.1)).take 1) +
      nOpen ((((laidOf p).map (·.1)).drop 1).take (1 + k)) =
      nOpen (((laidOf p).map (·.1)).take (1 + (1 + k))) := by
    rw [← nOpen_append, ← List.take_add]
  unfold grpS grpsS cutF cutS laidS
  rw [e1, e2, e3, List.drop_drop, e4]
  exact h

/-! ## The block's own rounds -/

theorem stagesFrom_rounds {T Cl : Type} (X : Parts T) (p : P12) : ∀ (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid),
    (stagesFrom X p j cur rest l : Block T Cl).rounds = l.map (·.1)
  | [], _, _, _ => rfl
  | next :: rest, j, cur, l => by
    show ((((l.take (1 + cur.k)).map (·.1) ++ ((l.drop (1 + cur.k)).take 2).map (·.1)) ++ []) ++ [])
        ++
      (stagesFrom X p (j + 1) next rest (l.drop (cur.k + 3)) : Block T Cl).rounds = _
    rw [stagesFrom_rounds X p rest, List.append_nil, List.append_nil, ← List.map_append,
      ← List.map_append]
    congr 1
    have e : l.drop (cur.k + 3) = (l.drop (1 + cur.k)).drop 2 := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [e, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- Where the block's test on the plan says yes, its rounds are the place's declared rounds. -/
theorem k12_rounds {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    (proximityTestKind X p : Block T Cl).rounds = (laidOf p).map (·.1) := by
  unfold proximityTestKind at hp ⊢
  unfold laidOf
  split at hp
  · rename_i first rest rs os e1 e2 e3
    rw [e2]
    show (([] ++ ((rs.zip p.oracles).take 1).map (·.1)) ++ []) ++
      (stagesFrom X p 0 first rest ((rs.zip p.oracles).drop 1) : Block T Cl).rounds = _
    rw [stagesFrom_rounds, List.nil_append, List.append_nil, ← List.map_append,
      List.take_append_drop]
    rfl
  · cases hp

theorem roundsFit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → ds.length = rs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: ds, _ :: rs, h => by
    unfold roundsFit at h
    simp only [Bool.and_eq_true] at h
    exact congrArg (· + 1) (roundsFit_length ds rs h.2)

/-- GroupsAre's first half from Block.step's yes. The step's first two lines (the rounds fit; the
columns fit in key, position and width), the block's test on the plan, and of the first switch's
cut: it is two rounds, of which the first opens nothing and neither reads a stored table (public: a
test on the plan). P.log at the trees P.ts are the declared depths (gpOk's clause opens.a). Every
position that the second round drew lies in the range. Then the groups that the frame deals to the
first switch stand, tree by tree, at the trees' own lists under these draws. -/
theorem first_half_of_step {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : roundsFit (proximityTestKind X p : Block T Cl).rounds rs = true)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).flatMap id) = true)
    (k : ℕ) (dS dC : Fmt.DeclaredRound) (hcut : cutS (laidS p) k = [dS, dC]) (h1 : dS.stored = [])
    (h2 : dS.opens = []) (h3 : dC.stored = []) (rS rC : Fmt.RoundView)
    (hrs : (rs.drop (1 + (1 + k))).take 2 = [rS, rC]) (log : ℕ → ℕ) (ts : List ℕ) (a : ℕ)
    (hlog : dC.opens.map (·.1.a) = ts.map log) (hr : ∀ x ∈ rC.drawn.poss, x < 2 ^ a) :
    List.Forall₂ (fun t grp =>
        grp.map (·.1) = (ownAt (log t) (Positions.ofDraws a rC.drawn.poss)).toList) ts
      (grpS (laidS p) k (grpsS p (regroup ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).flatMap id).length)))) := by
  rw [k12_rounds X p hp] at hfit hcols ⊢
  have hlen := roundsFit_length _ _ hfit
  have hcols' : (cols.take ((groupsOf F ((laidOf p).map (·.1))
      (rs.map (·.drawn))).flatMap id).length).map kpw =
      (groupsOf F ((laidOf p).map (·.1)) (rs.map (·.drawn))).flatMap id := beq_iff_eq.1 hcols
  have hg := grpS_first p F (rs.map (·.drawn)) _ k (by rw [hlen, List.length_map]) hcols'
  have hd : ((rs.map (·.drawn)).drop (1 + (1 + k))).take 2 = [rS.drawn, rC.drawn] := by
    rw [← List.map_drop, ← List.map_take, hrs]
    rfl
  rw [hcut, hd, groupsOf_two F dS dC _ _ h1 h2 h3] at hg
  exact first_half log a _ hr ts dC.opens _ hg hlog

end H2K.Sw
