-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PointOfTheSharedChain.lean: TWO LAWS BEHIND THE ROW (Dot) AT
THE DOOR BETWEEN THE CHAINS. (Dot) says that W at the shared point psi is the row weights g applied
to Omega. No item of the three threads says it at the last chain's start, so it is paid from what
the prover makes and from what the verifier's folds read.

  pointHeard      the first challenges heard on the shared chain, as a list of field elements
  PointKept       a block leaves psi in the chain's state
  point_of_fold   a fold that goes front block, point block, blocks that keep psi: the last state
    holds as psi what the point block's round drew
  point_kept_inside, point_kept_tests, point_kept_last   that chain's proximity tests and last block
    keep psi
  point_of_chain  the same at the shared chain as a file's description lays it
  point_at_made   the law: at a thread's clause (X), psi in the state is pointHeard of what was heard

What these are. Lemmas on our own definitions and the library's. None is one of the library's
goals. They say nothing of soundness, completeness or hiding of the protocol.

Limits.
  * point_of_chain asks that the shape splits the row (the hypothesis of the library's psi_blocks).
  * Nothing here says that a run reaches a stand where clause (X) holds.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.K14.Law.LedgerRidesOwn
import Johnson.Desc.K14.Law.FlatRetype
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.Sound.Gather

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Door
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks noDigest)
open VerifiableInference.Desc.Keeps (Decides foldBlocks_keeps)
open Desc.K14 (St P14 blocks chainOf drawn frontBlock)
open Desc.K14.Law (bareOf)

/-! ## The point, in the fold -/

/-- **The first challenges heard on the shared chain.** -/
def pointHeard (h : List Fmt.Drawn) : List OnBytes.E :=
  (h.head?.map fun d => d.elems.map OnBytes.E.ofTriple).getD []

variable {Cl : Type}

/-- A block leaves psi in the chain's state. -/
def PointKept (b : Block St Cl) : Prop :=
  Decides (fun a c : St => c.loc.psiSh = a.loc.psiSh) b

/-- A step that says yes rests on a yes of the block's decide at its rounds without the digest. -/
theorem step_decides {S : Type} {ft : Nat} {b : Block S Cl} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {n : Nat} (h : b.step ft s rs cols = .ok (s', n)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i _ _ _ _ t ht
        injection h with h
        injection h with h1 _
        subst h1
        exact ⟨_, ht⟩

/-- **A fold that goes through a block without a round, the point's block and blocks that keep the
point.** r: the first round shown. -/
theorem point_of_fold {ft : Nat} {b₀ b₁ : Block St Cl} {l : List (Block St Cl)} {s₀ : St}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {z : St × List Fmt.RoundView × List OpenedColumn}
    (h₀ : b₀.rounds = [])
    (d₁ : ∀ d rs gs d', b₁.decide d rs gs = .ok d' → ∃ r, rs = [r] ∧ d'.loc.psiSh = drawn r)
    (hk : ∀ b ∈ l, PointKept b)
    (hf : foldBlocks ft (b₀ :: b₁ :: l) s₀ rs cols = .ok z) :
    ∃ r t, rs = r :: t ∧ z.1.loc.psiSh = drawn r := by
  obtain ⟨s₁, n₁, -, -, f₁⟩ :=
    VerifiableInference.Desc.Sound.foldBlocks_cons_ok ft b₀ _ s₀ rs cols z hf
  rw [h₀] at f₁
  simp only [List.length_nil, List.drop_zero] at f₁
  obtain ⟨s₂, n₂, -, st₂, f₂⟩ :=
    VerifiableInference.Desc.Sound.foldBlocks_cons_ok ft b₁ _ s₁ rs _ z f₁
  obtain ⟨gs, hd⟩ := step_decides st₂
  obtain ⟨r', hr, e₂⟩ := d₁ _ _ gs _ hd
  have e := foldBlocks_keeps (fun a c : St => c.loc.psiSh = a.loc.psiSh) (fun _ => rfl)
    (fun _ _ _ x y => y.trans x) ft l hk _ _ _ _ f₂
  cases rs with
  | nil => simp at hr
  | cons r t =>
    cases hn : b₁.rounds.length with
    | zero => simp [hn] at hr
    | succ n =>
      rw [hn] at hr
      simp only [List.take_succ_cons, List.map_cons, List.cons.injEq] at hr
      refine ⟨r, t, rfl, e.trans (e₂.trans ?_)⟩
      rw [← hr.1]
      rfl

/-- The point's block of the kind's eight. -/
theorem point_block (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ d rs gs d', b1.decide d rs gs = .ok d' → ∃ r, rs = [r] ∧ d'.loc.psiSh = drawn r := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  intro d rs gs d' h
  obtain ⟨r, hr, hp, -⟩ := Desc.K14.Law.linPoint_inv _ d d' rs (Desc.K14.Law.why_some h)
  exact ⟨r, hr, hp⟩

/-- A test seated on the shared chain hands back the chain's state but for statement, book, roots. -/
theorem point_kept_inside (g : Desc.K14.Lin → Nat) (mask : Desc.K14.Lin → Option Nat)
    (b : Block VerifiableInference.Desc.K12.T12 Unit) :
    PointKept (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask) b
      VerifiableInference.Desc.K12.Seat.leave) := by
  intro d rs gs d' h
  have h' : (b.decide _ rs gs).bind (VerifiableInference.Desc.K12.Seat.leave d) = .ok d' := h
  cases hb : b.decide _ rs gs with
  | error e => rw [hb] at h'; cases h'
  | ok t =>
    rw [hb] at h'
    have e : ({ d with st := t.st, book := t.book, roots := t.roots } : St) = d' :=
      Except.ok.inj h'
    rw [← e]

/-- **The chain's own tests keep the point.** -/
theorem point_kept_tests (N : H2U.Places4) :
    ∀ b ∈ VerifiableInference.Desc.K12.Seat.tests N, PointKept b := by
  intro b hb
  simp only [VerifiableInference.Desc.K12.Seat.tests, List.mem_append, List.mem_singleton,
    List.mem_map] at hb
  rcases hb with rfl | ⟨n, -, rfl⟩
  · exact point_kept_inside _ _ _
  · exact point_kept_inside _ _ _

/-- **The chain's last block keeps the point.** -/
theorem point_kept_last (front : List (Block St Unit)) :
    PointKept (VerifiableInference.Desc.K12.Seat.last front) := by
  intro d rs gs d' h
  have h' : (VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL d.st)).map (fun _ => d) = .ok d' := h
  cases hb : VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL d.st) with
  | error e => rw [hb] at h'; cases h'
  | ok t =>
    rw [hb] at h'
    rw [← (Except.ok.inj h' : d = d')]

/-- **The law at the shared chain as a file's description holds it.** hS: the shape splits the row,
as the library's psi_blocks asks. -/
theorem point_of_chain {Cl' : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) (hT : ∀ b ∈ tests, PointKept b)
    (hL : PointKept (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)))
    {ft : Nat} {s₀ : St} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {z : St × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft ((chainOf c Q tests last).retype (Cl' := Cl')).blocksInOrder s₀ rs cols = .ok z) :
    ∃ r t, rs = r :: t ∧ z.1.loc.psiSh = drawn r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := Desc.K14.Law.own_bare Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  have hc : chainOf c Q tests last =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ tests
        last := last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests) } := by
    simp [chainOf, Desc.K14.blocksOr, hbl]
  rw [hc] at hf
  have pb := Desc.K14.Law.psi_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hS
  refine point_of_fold (b₀ := _) (b₁ := bareOf b1.retype) (l := _) rfl
    (fun d rs gs d' h => point_block Q b1 b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' h) ?_ hf
  intro b hb
  have hb' : b ∈ (([b2, b3, b4, b5, b6, b7, b8] ++ tests).map Block.retype).map bareOf ++
      [bareOf (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)).retype] := hb
  rcases List.mem_append.1 hb' with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rcases List.mem_append.1 hy with h' | h'
    · exact fun d rs gs d' hd => pb y h' d rs gs d' hd
    · exact fun d rs gs d' hd => hT y h' d rs gs d' hd
  · obtain rfl := List.mem_singleton.1 h
    exact fun d rs gs d' hd => hL d rs gs d' hd

/-- **The law at a thread's clause (X).** The thread's list is the shared chain's, it has no round in
front of it, and it stands at the chain's end: psi in the state is what was heard first. -/
theorem point_at_made {Bk : ProverCoinCounts} {V W X Pb Cl' : Type} (T : Thread Bk St Cl' V W X Pb)
    (c : OnBytes.Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) (hT : ∀ b ∈ tests, PointKept b)
    (hL : PointKept (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)))
    (hbs : T.bs = ((chainOf c Q tests last).retype (Cl' := Cl')).blocksInOrder) (hah : T.ahead = [])
    {k : Coins Bk} {s : St} {m : Mid W X} {E : Env} (hM : T.Made T.bs.length k s m E) :
    s.loc.psiSh = pointHeard m.st.heard := by
  obtain ⟨hseen, -, -, -, s₀, cols, -, -, hf⟩ := hM
  have hfr : T.front = 0 := by simp [Thread.front, hah]
  rw [List.take_length, hfr, List.drop_zero, hbs] at hf
  obtain ⟨r, t, hrs, hp⟩ := point_of_chain c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl hS hT hL hf
  rw [hrs] at hseen
  have e : m.st.heard = r.drawn :: t.map (·.drawn) := hseen.symm
  rw [e]
  exact hp

end ProofFile.Honest.Door

#print axioms ProofFile.Honest.Door.step_decides
#print axioms ProofFile.Honest.Door.point_of_fold
#print axioms ProofFile.Honest.Door.point_block
#print axioms ProofFile.Honest.Door.point_kept_inside
#print axioms ProofFile.Honest.Door.point_kept_tests
#print axioms ProofFile.Honest.Door.point_kept_last
#print axioms ProofFile.Honest.Door.point_of_chain
#print axioms ProofFile.Honest.Door.point_at_made
