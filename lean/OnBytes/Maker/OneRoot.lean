-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OneRoot.lean: every opening of the tree that the plain data of a file number j walks
to the root that the tree's sender sent, from leaves hashed at the sender's run's value; so two
openings of one tree have one root, and give one value to each vertex.

Statements and proofs. OnBytes/Maker/ReadTrace.lean says of an opening as read to which root it
walks and at which start its leaves were hashed, in the letters of the description: an own tree by
its number in the chain, a tree taken over by the root and the start that the description gives.
The plain data (`Three.Whole`) number the trees over the whole file. What ties a description's
names to these numbers is a premise here, `SrcFits`.

Main names:
  `rootsOf3 r c`: the roots that chain c of the file sent, in the order of sending.
  `TreeAt W r j root start`: the tree number j over the whole file is the n-th of a chain c that
    sent `root` as its n-th root and has the run's value `start`.
  `treeAt_unique`: a number has one root and one start, if the data count the first two chains'
    roots as read.
  `SrcNames W r c s j`: the name s in a description of chain c stands for the tree number j.
  `SrcFits W r c xs ds`: so round by round, opening by opening.
  `RootedAt`, `trace_rooted`: in a trace every opening of a tree walks to the root, and was hashed
    at the start, that its name has among all the chain's roots.
  `chain_treeAt`, `own_treeAt`: `TreeAt` at the members of `ownRows` and of `ownRowsW`.
  `one_root`: two openings under one number have one root.
  `one_table`: and give one value to each vertex below the root, and at the root.
Under "there is": in `TreeAt` the chain and the tree's number in it, fixed by j (`treeAt_unique`,
given the two counts); in `OpensTree` the start, fixed inside `TreeAt`; in `RootedAt` and
`OpensTree` the field, the bytes of a salt, the file and the place of the reader's call (in
`OpensTree` also cfg), which nothing else ties, though `trace_rooted`'s proof lays the plan's field
and salt and the chain's file. Who needs them takes `OpenAt` (OnBytes/Maker/ReadTrace.lean).
Limits: `SrcFits` and the two counts of roots are premises: they are not proved here
(OnBytes/Maker/SrcFitsOf.lean proves them from a reading). The root is the one that was read in the
sender's message: nothing is said of what it commits to. Nothing on soundness (index binding
included), what a root fixes beyond the reader's record, opening-form binding, no two openings of a
commitment, correctness of extraction or whatever else names a committer or a prover.
Which hash: h is a letter in `RootedAt` and `trace_rooted` alone; `OpensTree` and all from
`round_treeAt` on stand at the format's fixed hash `Fmt.formatHash`. Nothing at a drawn function.

-/
import OnBytes.Maker.ReadTrace
import OnBytes.Maker.ReadNodes
import OnBytes.Maker.TablesFit

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-! ## Trees over the whole file -/

/-- The roots that chain c of the file sent. -/
def rootsOf3 (r : Proof.TailRead) : ℕ → List ByteArray
  | 0 => r.first.roots
  | 1 => r.shared.roots
  | _ => r.second.roots

/-- The tree number j over the whole file: its root, and its sender's run's value. -/
def TreeAt (W : Three.Whole) (r : Proof.TailRead) (j : ℕ) (root start : ByteArray) : Prop :=
  ∃ c n, j = Three.wholeNo W.t₁ W.t₂ (c, n) ∧ c ≤ 2 ∧ (rootsOf3 r c)[n]? = some root ∧
    (chainOf r c).run = some start

theorem lt_of_getElem? {α : Type} {l : List α} {n : ℕ} {a : α} (h : l[n]? = some a) :
    n < l.length := by
  by_contra hn
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
  cases h

/-- A number over the whole file comes from one chain and one number in it, for numbers below the
chains' counts. L: the counts. -/
theorem wholeNo_inj (t₁ t₂ : ℕ) (L : ℕ → ℕ) (h0 : L 0 = t₁) (h1 : L 1 = t₂) :
    ∀ (c c' n n' : ℕ), c ≤ 2 → c' ≤ 2 → n < L c → n' < L c' →
    Three.wholeNo t₁ t₂ (c, n) = Three.wholeNo t₁ t₂ (c', n') → c = c' ∧ n = n'
  | 0, 0, n, n', _, _, _, _, e => ⟨rfl, by
      have e' : 0 + n = 0 + n' := e
      omega⟩
  | 0, 1, n, n', _, _, l, _, e => by
      have e' : 0 + n = t₁ + n' := e
      omega
  | 0, 2, n, n', _, _, l, _, e => by
      have e' : 0 + n = t₁ + t₂ + n' := e
      omega
  | 1, 0, n, n', _, _, _, l', e => by
      have e' : t₁ + n = 0 + n' := e
      omega
  | 1, 1, n, n', _, _, _, _, e => ⟨rfl, by
      have e' : t₁ + n = t₁ + n' := e
      omega⟩
  | 1, 2, n, n', _, _, l, _, e => by
      have e' : t₁ + n = t₁ + t₂ + n' := e
      omega
  | 2, 0, n, n', _, _, _, l', e => by
      have e' : t₁ + t₂ + n = 0 + n' := e
      omega
  | 2, 1, n, n', _, _, _, l', e => by
      have e' : t₁ + t₂ + n = t₁ + n' := e
      omega
  | 2, 2, n, n', _, _, _, _, e => ⟨rfl, by
      have e' : t₁ + t₂ + n = t₁ + t₂ + n' := e
      omega⟩
  | _ + 3, _, _, _, h, _, _, _, _ => by omega
  | 0, _ + 3, _, _, _, h, _, _, _ => by omega
  | 1, _ + 3, _, _, _, h, _, _, _ => by omega
  | 2, _ + 3, _, _, _, h, _, _, _ => by omega

/-- **A number has one root and one start.** -/
theorem treeAt_unique {W : Three.Whole} {r : Proof.TailRead} (h₁ : W.t₁ = r.first.roots.length)
    (h₂ : W.t₂ = r.shared.roots.length) {j : ℕ} {root start root' start' : ByteArray}
    (a : TreeAt W r j root start) (b : TreeAt W r j root' start') :
    root = root' ∧ start = start' := by
  obtain ⟨c, n, e, hc, hr, hs⟩ := a
  obtain ⟨c', n', e', hc', hr', hs'⟩ := b
  have key : c = c' ∧ n = n' :=
    wholeNo_inj W.t₁ W.t₂ (fun c => (rootsOf3 r c).length) h₁.symm h₂.symm c c' n n' hc hc'
      (lt_of_getElem? hr) (lt_of_getElem? hr') (e.symm.trans e')
  obtain ⟨rfl, rfl⟩ := key
  exact ⟨Option.some.inj (hr.symm.trans hr'), Option.some.inj (hs.symm.trans hs')⟩

/-- The name s in a description of chain c stands for the tree number j. -/
def SrcNames (W : Three.Whole) (r : Proof.TailRead) (c : ℕ) : Fmt.Src → ℕ → Prop
  | .own n, j => j = Three.wholeNo W.t₁ W.t₂ (c, n)
  | .given ρ σ, j => TreeAt W r j ρ σ

/-- Round by round, opening by opening, the description's names stand for the data's numbers. -/
def SrcFits (W : Three.Whole) (r : Proof.TailRead) (c : ℕ)
    (xs : List (Fmt.Round × List Fmt.Stored)) (ds : List Three.RDL) : Prop :=
  List.Forall₂ (fun (x : Fmt.Round × List Fmt.Stored) (d : Three.RDL) =>
    x.2.length = d.stored.length ∧
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => SrcNames W r c s.2 j) x.1.opens d.opens) xs ds

/-! ## A trace, against all the chain's roots -/

theorem getElem?_append_some {α : Type} : ∀ {l : List α} {n : ℕ} {a : α} (t : List α),
    l[n]? = some a → (l ++ t)[n]? = some a
  | [], _, _, _, h => by cases h
  | _ :: _, 0, _, _, h => h
  | _ :: l, n + 1, a, t, h => by
    rw [List.cons_append, List.getElem?_cons_succ]
    rw [List.getElem?_cons_succ] at h
    exact getElem?_append_some t h

/-- The root and the start of a name, among all the chain's roots. -/
def srcFull (run : Option ByteArray) (full : List ByteArray) :
    Fmt.Src → Option (ByteArray × ByteArray)
  | .own n =>
    match full[n]?, run with
    | some r, some s => some (r, s)
    | _, _ => none
  | .given r s => some (r, s)

theorem srcFull_of {run : Option ByteArray} {roots : Array ByteArray} {t : List ByteArray}
    {s : Fmt.Src} {rs : ByteArray × ByteArray} (h : srcOf run roots s = some rs) :
    srcFull run (roots.toList ++ t) s = some rs := by
  cases s with
  | given a b => exact h
  | own n =>
    cases hr : roots[n]? with
    | none => simp [srcOf, hr] at h
    | some ρ =>
      have e : (roots.toList ++ t)[n]? = some ρ :=
        getElem?_append_some t (by rw [Array.getElem?_toList]; exact hr)
      cases run with
      | none => simp [srcOf, hr] at h
      | some σ =>
        simp only [srcOf, hr] at h
        simp only [srcFull, e]
        exact h

/-- Of a description's round and a round as read: behind the stored tables' openings each tree's
opening walks to the root, and was hashed at the start, that its name has. -/
def RootedAt (h : HId) (cfg : ByteArray) (run : Option ByteArray) (full : List ByteArray)
    (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) : Prop :=
  ∃ cs co : List OpenedY, ro.opens = cs ++ co ∧ cs.length = x.2.length ∧
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) y => ∃ rs, srcFull run full s.2 = some rs ∧
      y.2.2.root = rs.1 ∧ ∃ (f : Fmt.Fld) (salt : ℕ) (b : ByteArray) (i : ℕ),
        Fmt.readOpeningW (m := Id) h cfg f salt y.1 rs.2 y.2.1 b i = some y.2.2) x.1.opens co

/-- **A trace, against all the chain's roots.** -/
theorem trace_rooted (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) : ∀ (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut)
      (c : Fmt.Chain) (roots : Array ByteArray), TraceX h cfg st P run b xs ros c roots →
    List.Forall₂ (RootedAt h cfg run (roots.toList ++ ros.flatMap fun ro => Fmt.rootsOf ro.vals))
      xs ros
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, _, T => T.elim
  | _ :: _, [], _, _, T => T.elim
  | x :: xs, ro :: ros, c, roots, T => by
    obtain ⟨R, T'⟩ := T
    have ih := trace_rooted h cfg st P run b xs ros _ _ T'
    have e : (roots ++ (Fmt.rootsOf ro.vals).toArray).toList ++
        (ros.flatMap fun ro => Fmt.rootsOf ro.vals) =
        roots.toList ++ ((ro :: ros).flatMap fun ro => Fmt.rootsOf ro.vals) := by
      rw [Array.toList_append, List.flatMap_cons, List.append_assoc]
    rw [e] at ih
    refine .cons ?_ ih
    obtain ⟨cs, co, ho, h1, h2⟩ := R.opens
    refine ⟨cs, co, ho, h1.length_eq.symm, h2.imp fun s y hy => ?_⟩
    obtain ⟨rs, hs, O⟩ := hy
    obtain ⟨i, hi⟩ := O.read
    refine ⟨rs, ?_, O.rootIs, P.field, P.salt, b, i, by rw [O.shape, O.list]; exact hi⟩
    rw [← e]
    exact srcFull_of hs

/-! ## One chain -/

/-- What is said of an opening under the number j. -/
def OpensTree (W : Three.Whole) (r : Proof.TailRead) (x : ℕ × Opened) : Prop :=
  ∃ start, TreeAt W r x.1 x.2.2.2.root start ∧ ∃ (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ)
    (b : ByteArray) (i : ℕ),
    Fmt.readOpeningW (m := Id) Fmt.formatHash cfg f salt x.2.1 start x.2.2.1 b i = some x.2.2.2

theorem round_treeAt (W : Three.Whole) (r : Proof.TailRead) (c : ℕ) (hc : c ≤ 2) (cfg : ByteArray)
    (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) (d : Three.RDL)
    (H : RootedAt Fmt.formatHash cfg (chainOf r c).run (rootsOf3 r c) x ro)
    (hl : x.2.length = d.stored.length)
    (F : List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => SrcNames W r c s.2 j) x.1.opens d.opens) :
    ∀ z ∈ d.opens.zip (ro.opens.drop d.stored.length), OpensTree W r z := by
  obtain ⟨cs, co, ho, l1, h2⟩ := H
  rintro ⟨j, y⟩ hz
  rw [ho, List.drop_left' (l1.trans hl)] at hz
  obtain ⟨s, hn, rs, hs, hroot, f, salt, b, i, hi⟩ :=
    (List.forall₂_iff_zip.1 (forall₂_join h2 F)).2 hz
  refine ⟨rs.2, ?_, cfg, f, salt, b, i, hi⟩
  show TreeAt W r j y.2.2.root rs.2
  rw [hroot]
  obtain ⟨sh, src⟩ := s
  cases src with
  | given ρ σ =>
    obtain rfl : (ρ, σ) = rs := Option.some.inj hs
    exact hn
  | own n =>
    have hn' : j = Three.wholeNo W.t₁ W.t₂ (c, n) := hn
    unfold srcFull at hs
    cases hr : (rootsOf3 r c)[n]? with
    | none => simp only [hr] at hs; cases hs
    | some ρ =>
      cases hu : (chainOf r c).run with
      | none => simp only [hr, hu] at hs; cases hs
      | some σ =>
        simp only [hr, hu] at hs
        obtain rfl : (ρ, σ) = rs := Option.some.inj hs
        exact ⟨c, n, hn', hc, hr, hu⟩

/-- **One chain.** full: that the roots of the chain as read are `rootsOf3 r c`. -/
theorem chain_treeAt (W : Three.Whole) (r : Proof.TailRead) (c : ℕ) (hc : c ≤ 2) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (ds : List Three.RDL)
    (e : readChain S seen b i = some (chainOf r c, j))
    (full : rootsOf3 r c = (chainOf r c).rounds.toList.flatMap fun ro => Fmt.rootsOf ro.vals)
    (F : SrcFits W r c (S.base.rounds.zip S.stored) ds) :
    ∀ z ∈ ownRows ds (chainOf r c), OpensTree W r z := by
  obtain ⟨-, -, -, -, T⟩ := readChain_trace S seen b i _ j e
  have R := trace_rooted Fmt.formatHash _ _ _ _ b _ _ _ _ T
  rw [show (#[] : Array ByteArray).toList ++
    ((chainOf r c).rounds.toList.flatMap fun ro => Fmt.rootsOf ro.vals) = rootsOf3 r c from by
      rw [full]; rfl] at R
  intro z hz
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hz
  obtain ⟨x, ⟨hl, hF⟩, hR⟩ := (List.forall₂_iff_zip.1 (forall₂_join R F)).2 hp
  exact round_treeAt W r c hc _ x ro d hR hl hF z hin

/-- The roots of a chain as read, in the letters of the format. -/
theorem roots_eq (c : ChainRead) :
    c.roots = c.out.rounds.toList.flatMap fun ro => Fmt.rootsOf ro.vals :=
  List.flatMap_congr fun x _ => rootsT_eq x.vals

/-! ## The three chains of a file -/

/-- **Every opening of a tree, at the three chains of a file as the program's reader has read
them.** -/
theorem own_treeAt (W : Three.Whole) (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead) (b : ByteArray)
    (n₁ n₂ n₃ : Fmt.Seen) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃))
    (F₁ : SrcFits W r 0 (S₁.base.rounds.zip S₁.stored) W.ds₁)
    (F₂ : SrcFits W r 1 (S₂.base.rounds.zip S₂.stored) W.ds₂)
    (F₃ : SrcFits W r 2 (S₃.base.rounds.zip S₃.stored) W.ds₃) :
    ∀ z ∈ ownRowsW W r, OpensTree W r z := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact chain_treeAt W r 0 (by omega) S₁ n₁ b i₁ j₁ W.ds₁ e₁ (roots_eq r.first) F₁ z hz
  · rcases List.mem_append.1 hz with hz | hz
    · exact chain_treeAt W r 1 (by omega) S₂ n₂ b i₂ j₂ W.ds₂ e₂ (roots_eq r.shared) F₂ z hz
    · exact chain_treeAt W r 2 (by omega) S₃ n₃ b i₃ j₃ W.ds₃ e₃ (roots_eq r.second) F₃ z hz

/-- **Two openings under one number have one root.** (They were also hashed at one start:
`treeAt_unique` gives it; it is not stated here, since `OpensTree` holds the start under "there
is".) -/
theorem one_root {W : Three.Whole} {r : Proof.TailRead} (h₁ : W.t₁ = r.first.roots.length)
    (h₂ : W.t₂ = r.shared.roots.length) {z z' : ℕ × Opened} (a : OpensTree W r z)
    (a' : OpensTree W r z') (e : z.1 = z'.1) : z.2.2.2.root = z'.2.2.2.root := by
  obtain ⟨s, t, -⟩ := a
  obtain ⟨s', t', -⟩ := a'
  rw [e] at t
  exact (treeAt_unique h₁ h₂ t t').1

/-- A member of `ownRowsW` is an opening of one of the three chains. -/
theorem ownW_mem {W : Three.Whole} {r : Proof.TailRead} {z : ℕ × Opened} (hz : z ∈ ownRowsW W r) :
    z.2 ∈ opensIn r.first.out ++ (opensIn r.shared.out ++ opensIn r.second.out) := by
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨ro, hro, hy⟩ := own_mem hz
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨ro, hro, hy⟩)
  · rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨ro, hro, hy⟩))
    · obtain ⟨ro, hro, hy⟩ := own_mem hz
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨ro, hro, hy⟩))

/-- **One table of vertices a tree**: at three chains read one after the other, two openings under
one number give one value to each vertex below the root, and at the root. -/
theorem one_table (W : Three.Whole) (S₁ S₂ S₃ : Fmt.SpecX) (r : Proof.TailRead) (b : ByteArray)
    (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ) (e₁ : readChain S₁ [] b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ r.first.out.seen b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ r.shared.out.seen b i₃ = some (r.second.out, j₃))
    (F₁ : SrcFits W r 0 (S₁.base.rounds.zip S₁.stored) W.ds₁)
    (F₂ : SrcFits W r 1 (S₂.base.rounds.zip S₂.stored) W.ds₂)
    (F₃ : SrcFits W r 2 (S₃.base.rounds.zip S₃.stored) W.ds₃)
    (h₁ : W.t₁ = r.first.roots.length) (h₂ : W.t₂ = r.shared.roots.length) :
    ∀ z ∈ ownRowsW W r, ∀ z' ∈ ownRowsW W r, z.1 = z'.1 → ∀ (d p : ℕ) (a a' : ByteArray),
      (d ≠ 0 ∨ p = 0) → seenAt z.2.2.2.seen d p = some a → seenAt z'.2.2.2.seen d p = some a' →
      a = a' := by
  intro z hz z' hz' e d p a a' hd ha ha'
  have T := own_treeAt W S₁ S₂ S₃ r b _ _ _ i₁ i₂ i₃ j₁ j₂ j₃ e₁ e₂ e₃ F₁ F₂ F₃
  have hr := one_root h₁ h₂ (T z hz) (T z' hz') e
  by_cases h0 : d = 0
  · have hp : p = 0 := by
      rcases hd with hd | hd
      · exact absurd h0 hd
      · exact hd
    subst h0 hp
    obtain ⟨s, -, cfg, f, salt, b1, k, q⟩ := T z hz
    obtain ⟨s', -, cfg', f', salt', b2, k', q'⟩ := T z' hz'
    have w := (walked_nodes Fmt.formatHash cfg (y := z.2) ⟨f, salt, s, b1, k, q⟩).2
    have w' := (walked_nodes Fmt.formatHash cfg' (y := z'.2) ⟨f', salt', s', b2, k', q'⟩).2
    rw [w] at ha
    rw [w'] at ha'
    rw [← Option.some.inj ha, ← Option.some.inj ha']
    exact hr
  · exact (three_walks S₁ S₂ S₃ b i₁ i₂ i₃ j₁ j₂ j₃ _ _ _ e₁ e₂ e₃).2 z.2 (ownW_mem hz) z'.2
      (ownW_mem hz') hr (d, p, a) (seenAt_mem ha) (d, p, a') (seenAt_mem ha') h0 rfl rfl

end OnBytes.Maker
