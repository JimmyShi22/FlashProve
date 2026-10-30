-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/BatchAdds.lean
(kind K9's soundness lemma): THEOREM: the premise "batch" of the law of a whole
segment (Johnson/Desc/LinkLaw2.lean: LinkSem.BatchAdds), AT THE REAL BLOCK K9.batch X p f, for every
function f of claims and at any state T with K9's lens.
  Others   the letters of that law which are the other kinds' to fill: what is fixed before the
           draw; their parts of ready, good, behind, later ("more"), full; the runs' counts,
           equations and exponents.
  semOf    the meaning laid beside a segment, K9's own letters filled: a drawn element and chi by
           the reading; wv: a claim's value with its weight (wvK); one: the ledger's value in one
           state, read at another (oneK); good: the ledger is empty, no claim is counted, one
           coefficient for each slot (three tests of the draw); later: the plan's number of claims
           stays.
  Fits     THE HYPOTHESES, BY NAME, on the lens and on the others' letters alone.
  batchAdds   **(semOf ρ X O).BatchAdds ft (K9.batch X p f) f.**

-/
import Johnson.Desc.LinkLaw2
import Johnson.Desc.First.Batch.Law.ForLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where batch drawnClean ledgerEmpty)

variable {T P K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The letters that are the other kinds' to fill. -/
structure Others (T P K : Type) where
  fixed : T → P
  ready : T → Prop
  good : T → Prop
  behind : T → Prop
  more : T → T → Prop
  full : T → Prop
  cnt : ℕ × String → P → ℕ
  eqs : ℕ × String → P → Bound K → List K
  exps : ℕ × String → ℕ → P → List ℕ

/-- The plan's number of claims in a state's ledger; nothing where no segment is open. -/
def planOf (X : Lens T) (t : T) : Option Nat := (X.get? t).map (·.F.planClaimsF)

/-- The ledger of a state is as the draw lays it, as far as the sums go. -/
def CleanAt (X : Lens T) (s : T) : Prop :=
  ∃ b, X.get? s = some b ∧ ledgerEmpty b.F = true ∧ b.F.nClaim = 0 ∧ b.F.LS.size = b.F.ns

/-- **The meaning laid beside a segment**, K9's letters filled. -/
def semOf (ρ : Reading K) (X : Lens T) (O : Others T P K) : LinkSem K T Claim P (Bound K) where
  rd := fun x => ρ.val (E.ofTriple x)
  fixed := O.fixed
  chi := fun t =>
    match X.get? t with
    | some a => ρ.val a.F.theta
    | none => 0
  ready := O.ready
  good := fun s => CleanAt X s ∧ O.good s
  behind := O.behind
  later := fun s t => planOf X s = planOf X t ∧ O.more s t
  full := O.full
  wv := wvK X ρ
  one := oneK X ρ
  cnt := O.cnt
  eqs := O.eqs
  exps := O.exps

omit [Fintype K] [DecidableEq K] in
theorem wsum_semOf (ρ : Reading K) (X : Lens T) (O : Others T P K) (t : T) (y : Bound K) (c : K) :
    ∀ (l : List Claim) (n : ℕ), (semOf ρ X O).wsum t y c n l = wsumK X ρ t y c n l
  | [], _ => rfl
  | cl :: l, n => by
    rw [LinkSem.wsum, wsumK, wsum_semOf ρ X O t y c l (n + 1)]
    rfl

omit [Fintype K] [DecidableEq K] in
theorem wsumK_none (ρ : Reading K) (X : Lens T) (t : T) (h : X.get? t = none) (y : Bound K)
    (c : K) : ∀ (l : List Claim) (n : ℕ), wsumK X ρ t y c n l = 0
  | [], _ => rfl
  | cl :: l, n => by
    rw [wsumK, wsumK_none ρ X t h y c l (n + 1)]
    simp [wvK, h]

/-- The hypotheses, by name. -/
structure Fits (X : Lens T) (O : Others T P K) (p : Where) : Prop where
  /-- the lens: behind a writing, the ledger read is the ledger written -/
  lens : ∀ s a, (X.get? s).isSome = true → ∃ a', X.get? (X.set s a) = some a' ∧ a'.F = a.F
  /-- the draw's writing leaves alone what is fixed before the draw, and lays a state that is good
  in the other kinds' eyes -/
  atDraw : ∀ s a o x, O.ready s → X.get? s = some a →
    drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o →
    O.fixed (X.set s { a with owed := o.owed, L := o.L, F := o.F }) = O.fixed s ∧
      O.good (X.set s { a with owed := o.owed, L := o.L, F := o.F })
  /-- the adding's writing gives a state that is behind, and later in the other kinds' eyes -/
  atAdding : ∀ s₂ b G cls, O.good s₂ → X.get? s₂ = some b → addAll b.F cls = some G →
    O.behind (X.set s₂ { b with F := G }) ∧ O.more s₂ (X.set s₂ { b with F := G })

omit [Fintype K] [DecidableEq K] in
/-- **What the segment's law asks of the batching's block, at the real block.** -/
theorem batchAdds (ρ : Reading K) (X : Lens T) (O : Others T P K) (p : Where)
    (f : T → Except String (List Claim × T)) (ft : ℕ) (H : Fits X O p) :
    (semOf ρ X O).BatchAdds ft (batch X p f) f := by
  refine batchAdds_shape X p f ft (semOf ρ X O).rd (semOf ρ X O).fixed (semOf ρ X O).chi
    (semOf ρ X O).ready (semOf ρ X O).good
    (fun s₂ s' x cls => (semOf ρ X O).behind s' ∧ (semOf ρ X O).later s₂ s' ∧
      ∀ t y, (semOf ρ X O).later s' t →
        (semOf ρ X O).one t s' y = (semOf ρ X O).wsum t y ((semOf ρ X O).rd x) 0 cls) ?_ ?_
  · intro s a o x hr ha ho
    obtain ⟨d1, d2, d3, _, _, _, _, _, _, _, _, d12⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
    obtain ⟨a', ha', hF⟩ := H.lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
    obtain ⟨g1, g2⟩ := H.atDraw s a o x hr ha ho
    have hF' : a'.F = o.F := hF
    refine ⟨⟨⟨a', ha', by rw [hF']; exact d1, by rw [hF']; exact d3, ?_⟩, g2⟩, g1, ?_⟩
    · rw [hF']
      exact d12
    · show (match X.get? _ with
        | some a => ρ.val a.F.theta
        | none => 0) = ρ.val (E.ofTriple x)
      rw [ha']
      show ρ.val a'.F.theta = _
      rw [hF', d2]
  · intro s₂ b G cls x hg hc hb hG
    obtain ⟨⟨b0, hb0, e1, e2, e3⟩, og⟩ := hg
    have eb : b0 = b := Option.some.inj (hb0.symm.trans hb)
    subst eb
    obtain ⟨b', hb', hF⟩ := H.lens s₂ { b0 with F := G } (by simp [hb])
    have hF' : b'.F = G := hF
    obtain ⟨k1, k2⟩ := H.atAdding s₂ b0 G cls og hb hG
    have hplan : G.planClaimsF = b0.F.planClaimsF := by
      rw [(addAll_total ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ cls b0.F G e3 hG).2.1]
    have hθ : ρ.val b0.F.theta = ρ.val (E.ofTriple x) := by
      have h := hc
      simp only [semOf, hb] at h
      exact h
    refine ⟨k1, ⟨?_, k2⟩, fun t y ht => ?_⟩
    · simp only [planOf, hb, hb', Option.map_some, hF', hplan]
    · rw [wsum_semOf]
      show oneK X ρ t _ y = wsumK X ρ t y (ρ.val (E.ofTriple x)) 0 cls
      cases hta : X.get? t with
      | none =>
        rw [wsumK_none ρ X t hta]
        simp [oneK, hta]
      | some a =>
        have hp : a.F.planClaimsF = b0.F.planClaimsF := by
          have h := ht.1
          simp only [planOf, hb', hta, Option.map_some, Option.some.injEq, hF', hplan] at h
          exact h.symm
        rw [← hθ]
        exact oneK_wsumK X ρ t _ a b' b0.F cls y hta hb' e1 e2 e3 hp (by rw [hF']; exact hG)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.batchAdds
