-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/ShapesOmega.lean: THE BOOK-KEEPING ON THE SHARED CHAIN's OWN RECORD BEHIND
o_omega's SENDING, AS A TEST WITH CODE; THAT THE JOININGS, "LIN zeta" AND "SPLIT" EARN IT; AND THE
LAW OF "SPLIT" WITH ONLY ITS OWN TWO ROWS BEHIND. The second half of
Johnson/Desc/K14/Law/Shapes.lean.

  RowsO i n d m   the constraints number i, …, i + n - 1 on G_omega, as they lie in the record.
  shapedOB        o_omega's entry in the statement has the public shape.
  shapeO p nU nO cU cO s   **the test**: shapeU at nU and cU; shapedOB; the number that the record
                  notes for o_omega is nO (the plan's), another than nU; G_omega has just cO open
                  rows; the shape has two codes.
  seated_of_shapeO   it gives: the two messages of (fold) are seated; the shape's conditions hold at
                  the record's codes; two codes: what "SPLIT" spends of the promise.
  joins_rows      the joinings leave every group's list of rows.
  shapeO_joins, shapeO_zeta, shapeO_split   **it is earned**: the joinings and "LIN zeta" leave the
                  counts; "SPLIT" lays one row on each group.
  foldSaysOwn     what the two rows that "SPLIT" itself has laid mean: foldSays
                  (Johnson/Desc/K14/Law/Joint.lean) without the groups' other rows.
  split_core      **"SPLIT"**, for certain, general in the record and the two promises. In front:
                  PinA, and (fold)'s equation at the point noted (FoldAt). Behind: PinB, the row cU
                  on G_u and the row cO on G_omega.

What is not claimed. That any record passes the test. That o_omega's sending earns it. PinA, PinB,
on, on' are letters: no member is shown. A block that refuses all has GoodIn too. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.Shapes
import Johnson.Desc.K14.Law.GoodFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Run.PQ (CK)

/-- o_omega's entry in the statement has the public shape. -/
def shapedOB (p : Par) (s : St) : Bool :=
  match s.st.oracles[s.loc.oOmega]? with
  | some x => decide (x.shape = p.S.omega)
  | none => false

theorem shapedOB_iff (p : Par) (s : St) : shapedOB p s = true ↔
    ∃ x, s.st.oracles[s.loc.oOmega]? = some x ∧ x.shape = p.S.omega := by
  unfold shapedOB
  constructor
  · intro h1
    cases hx : s.st.oracles[s.loc.oOmega]? with
    | none =>
      rw [hx] at h1
      cases h1
    | some x =>
      rw [hx] at h1
      exact ⟨x, rfl, of_decide_eq_true h1⟩
  · rintro ⟨x, hx, hs⟩
    rw [hx]
    exact decide_eq_true hs

/-- **The book-keeping behind o_omega's sending, as a test.** nU, nO: the two messages' numbers in
the chain's statement, by the plan; cU, cO: the numbers of open rows on G_u and on G_omega. -/
def shapeO (p : Par) (nU nO cU cO : Nat) (s : St) : Bool :=
  shapeU p nU cU s && shapedOB p s && decide (s.loc.oOmega = nO) && decide (nO ≠ nU) &&
    decide ((rowsOn s s.loc.gOmega).length = cO) && p.S.sharedSplitNeeded

/-- What the test says. -/
theorem shapeO_iff (p : Par) (nU nO cU cO : Nat) (s : St) : shapeO p nU nO cU cO s = true ↔
    shapeU p nU cU s = true ∧ shapedOB p s = true ∧ s.loc.oOmega = nO ∧ nO ≠ nU ∧
      (rowsOn s s.loc.gOmega).length = cO ∧ p.S.sharedSplitNeeded = true := by
  unfold shapeO
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **What "SPLIT" spends of the promise.** -/
theorem seated_of_shapeO (p : Par) (nU nO cU cO : Nat) (s : St)
    (h : shapeO p nU nO cU cO s = true) :
    Seated s.st s.st.codes p.S s.loc ∧ linOk s.st.codes p.S = true ∧
      p.S.sharedSplitNeeded = true := by
  obtain ⟨hU, hO, eO, hne, _, hS⟩ := (shapeO_iff p nU nO cU cO s).1 h
  obtain ⟨_, hsU, eU, _⟩ := (shapeU_iff p nU cU s).1 hU
  obtain ⟨hx, hlay, hok⟩ := (seatedUB_iff p s).1 hsU
  exact ⟨⟨rfl, by rw [eO, eU]; exact hne, (shapedOB_iff p s).1 hO, hx, hlay⟩, hok, hS⟩

/-- A step onward that leaves the small record keeps o_omega's entry. -/
theorem shapedOB_onward (p : Par) (a b : St) (o : Onward a b) (l : b.loc = a.loc)
    (h : shapedOB p a = true) : shapedOB p b = true := by
  obtain ⟨x, hx, hs⟩ := (shapedOB_iff p a).1 h
  obtain ⟨x', hx', gx⟩ := o.grows.2.2 _ x hx
  refine (shapedOB_iff p b).2 ⟨x', ?_, gx.1.trans hs⟩
  rw [l]
  exact hx'

/-- The test goes on past a step onward that leaves the small record and lays n rows on G_u and m on
G_omega. -/
theorem shapeO_step (p : Par) (nU nO cU cO n m : Nat) (a b : St) (o : Onward a b)
    (l : b.loc = a.loc)
    (hrU : ∃ rows, rowsOn b a.loc.gU = rowsOn a a.loc.gU ++ rows ∧ rows.length = n)
    (hrO : ∃ rows, rowsOn b a.loc.gOmega = rowsOn a a.loc.gOmega ++ rows ∧ rows.length = m)
    (h : shapeO p nU nO cU cO a = true) : shapeO p nU nO (cU + n) (cO + m) b = true := by
  obtain ⟨hU, hO, eO, hne, hc, hS⟩ := (shapeO_iff p nU nO cU cO a).1 h
  obtain ⟨rows, hR, hm⟩ := hrO
  refine (shapeO_iff p nU nO (cU + n) (cO + m) b).2
    ⟨shapeU_step p nU cU n a b o l hrU hU, shapedOB_onward p a b o l hO, ?_, hne, ?_, hS⟩
  · rw [l]
    exact eO
  · rw [l, hR, List.length_append, hc, hm]

/-- The joinings leave every group's list of rows. -/
theorem joins_rows (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d') :
    ∀ g, rowsOn d' g = rowsOn d g := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have r1 := (rowsOn_joinP d d1 _ _ _ h1).1
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    intro g
    rw [(rowsOn_joinP d2 d' _ _ _ h4).1 g, (rowsOn_joinP d1 d2 _ _ _ h3).1 g, r1 g]
  · obtain rfl := Option.some.inj h2
    exact r1

/-- **At a yes of the joinings.** -/
theorem shapeO_joins (p : Par) (nU nO cU cO : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : joins p a rs = some b) (h : shapeO p nU nO cU cO a = true) :
    shapeO p nU nO cU cO b = true :=
  shapeO_step p nU nO cU cO 0 0 a b (onward_joins p a b rs k).1 (onward_joins p a b rs k).2
    ⟨[], by rw [joins_rows p a b rs k, List.append_nil], rfl⟩
    ⟨[], by rw [joins_rows p a b rs k, List.append_nil], rfl⟩ h

/-- **At a yes of "LIN zeta".** -/
theorem shapeO_zeta (p : Par) (nU nO cU cO : Nat) (a b : St) (r : Fmt.RoundView)
    (k : linZeta a [r] = some b) (h : shapeO p nU nO cU cO a = true) :
    shapeO p nU nO cU cO b = true := by
  rw [linZeta_inv a b r k]
  exact h

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- **At a yes of "SPLIT".** -/
theorem shapeO_split (p : Par) (nU nO cU cO : Nat) (a b : St) (r : Fmt.RoundView)
    (k : split p a [r] = some b) (h : shapeO p nU nO cU cO a = true) :
    shapeO p nU nO (cU + 1) (cO + 1) b = true := by
  have hS := ((shapeO_iff p nU nO cU cO a).1 h).2.2.2.2.2
  obtain ⟨_, x, y, _, h1, h2, _⟩ := laysW OnBytes.Model.Reading.gl p a b r hS k
  exact shapeO_step p nU nO cU cO 1 1 a b (onward_split p a b r hS k).1
    (onward_split p a b r hS k).2 ⟨[y], h2, rfl⟩ ⟨[x], h1, rfl⟩ h

/-- The constraints number i, …, i + n - 1 on G_omega, as they lie in the record, hold of the
words. -/
def RowsO (i n : Nat) (d : St) (m : Words K) : Prop :=
  Means.AllSay ρ d.st (((rowsOn d d.loc.gOmega).drop i).take n) m

/-- **What the two constraints that "SPLIT" itself has laid mean.** -/
theorem foldSaysOwn (p : Par) (d d' : St) (r : Fmt.RoundView) (T : Statement) (m : Words K)
    (hS : p.S.sharedSplitNeeded = true) (h : split p d [r] = some d')
    (hsO : ∀ x, rowsOn d' d.loc.gOmega = rowsOn d d.loc.gOmega ++ [x] → Means.Says ρ T x m)
    (hsU : ∀ y, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ [y] → Means.Says ρ T y m)
    (hP : Placed T p.S d.loc (linLayOmega d.st.codes p.S)) :
    FoldEq p.S ((d.loc.psiSh.take p.S.kLo).map ρ.val) (d.loc.zFd.map ρ.val)
      (omegaOf d.loc (linLayOmega d.st.codes p.S) m) (uOf d.loc m) := by
  obtain ⟨row, x, y, hf, h1, h2, h3⟩ := laysW ρ p d d' r hS h
  exact (foldMeansW ρ T p.S d.loc _ row hf hP m).1 (h3 T m (hsO x h1) (hsU y h2))

variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K)

/-- **"SPLIT": the core.** -/
theorem split_core {T Cl : Type} (get : T → St) (pc : Piece C F T Cl W) (p : Par)
    (hb : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → split p (get d) rs = some (get d'))
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (PinA PinB : T × F.E.Str → W → Prop)
    (hst : ∀ a, on a → p.S.sharedSplitNeeded = true ∧ ∀ T', Grows (get a.1).st T' →
      Placed T' p.S (get a.1).loc (linLayOmega (get a.1).st.codes p.S))
    (cU cO : Nat) (hcU : ∀ a, on a → (rowsOn (get a.1) (get a.1).loc.gU).length = cU)
    (hcO : ∀ a, on a → (rowsOn (get a.1) (get a.1).loc.gOmega).length = cO)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → PinB b w → PinA a w) :
    pc.GoodIn on on' (fun a w => PinA a w ∧ FoldAt ρ p.S (get a.1) (rw w))
      (fun b w => PinB b w ∧ RowsU ρ cU 1 (get b.1) (rw w) ∧ RowsO ρ cO 1 (get b.1) (rw w)) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  have k8 := hb _ _ gs _ hd
  obtain ⟨hS, hP⟩ := hst a ha
  obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k8
  rw [hr] at k8
  obtain ⟨o8, l8⟩ := onward_split p (get a.1) (get b.1) r8 hS k8
  refine ⟨hon a τ b ha hout, fun w hw => ?_⟩
  obtain ⟨hpin, hU, hO⟩ := hw
  rw [hext]
  refine ⟨hback a τ b w ha hout hpin, ?_⟩
  refine foldSaysOwn ρ p (get a.1) (get b.1) r8 (get b.1).st (rw w) hS k8 (fun x hx => ?_)
    (fun y hy => ?_) (hP _ o8.grows)
  · unfold RowsO at hO
    rw [l8, hx, slice_new _ [x] cO 1 (hcO a ha) rfl] at hO
    exact hO x (List.mem_singleton.2 rfl)
  · unfold RowsU at hU
    rw [l8, hy, slice_new _ [y] cU 1 (hcU a ha) rfl] at hU
    exact hU y (List.mem_singleton.2 rfl)

end Desc.K14.Law
