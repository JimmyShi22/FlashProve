-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AtBlock.lean
(kind K9's soundness lemma): THEOREMS: what a yes of K9's blocks says, at any state
T with a lens (Batch/Kind.lean), through the general step function Block.step.
  fill_empty      t2FillL keeps an empty ledger empty.
  drawnClean_ok   what the draw lays: an empty ledger that holds chi and has counted no claim; what
                  it leaves alone.
  batch_step      THE INVERSION of (K9.batch X p f).step: one round; one element x drawn; the draw's
                  tests passed at the part of the state in front; f was called at the state that the
                  draw laid, and returned; the claims were added to the ledger of the state that f
                  returned (the block calls K9's own addList, Batch/Add.lean; said here of the older
                  addAll, by Law/AddAgrees.lean: addList_older); the state behind is that state
                  with the new ledger.
  batch_adds      so the new ledger's value is the value of the ledger that f returned plus the sum
                  of the claims under their weights, in every world under every reading.
  Clean, addAll_clean   if the ledger that f returned is still empty, holds chi, has counted no
                  claim and has one coefficient for each slot, the new ledger's value IS that sum,
                  the claims numbered from 0.
  equation_step   THE INVERSION of (K9.oneEquation X p).step, as far as K9.equation.
f RUNS BETWEEN THE DRAW AND THE ADDING AND MAY BY TYPE TURN THE LEDGER: that it does not is Clean,
owed by the kinds whose runs f calls. Nothing where a block refuses. No count here.

-/
import Johnson.Desc.First.Batch.Law.AddAgrees
import Johnson.Desc.First.Batch.Law.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9

theorem there_ok {α : Type} {n : String} {x : Option α} {a : α} (h : there n x = .ok a) :
    x = some a := by
  cases x with
  | none => exact absurd h (by simp [there])
  | some b => simpa [there] using h

/-! ## The draw -/

/-- No weight on an entry of the arrays. -/
def NoWeight (X : HTree) : Prop := ∀ r ∈ X.rows, ∀ v ∈ r.L, isZeroE v = true

/-- t2FillL's step on one array, under a name. -/
def fillOne (X : HTree) : HTree :=
  { X with rows := X.rows.map fun r =>
      if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r }

theorem fillOne_keeps (X : HTree) (h : NoWeight X) : NoWeight (fillOne X) := by
  intro r hr v hv
  simp only [fillOne, Array.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  split at hv
  · simp only [Array.mem_replicate] at hv
    rw [hv.2]
    rfl
  · exact h r0 hr0 v hv

theorem fold_keeps : ∀ (l : List Nat) (tr : Array HTree), (∀ X ∈ tr, NoWeight X) →
    ∀ X ∈ l.foldl (fun trees ti => trees.modify ti fillOne) tr, NoWeight X
  | [], _, h => h
  | ti :: l, tr, h => by
    rw [List.foldl_cons]
    apply fold_keeps l
    intro X hX
    rw [← Array.mem_toList_iff, Array.toList_modify] at hX
    exact OnBytes.all_modify NoWeight fillOne fillOne_keeps tr.toList ti
      (fun a ha => h a (Array.mem_toList_iff.mp ha)) X hX

/-- t2FillL keeps an empty ledger empty. -/
theorem fill_empty (F : Fork) (T : Tail2) (h : ledgerEmpty F = true) :
    ledgerEmpty (t2FillL F T) = true := by
  simp only [ledgerEmpty, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h ⊢
  obtain ⟨⟨hT, hL⟩, hc⟩ := h
  exact ⟨⟨fold_keeps (List.range T.nt.size) F.trees hT, hL⟩, hc⟩

/-- **What the draw lays.** -/
theorem drawnClean_ok (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    ledgerEmpty o.F = true ∧ o.F.theta = chi ∧ o.F.nClaim = 0 ∧
      o.F.planClaimsF = F.planClaimsF ∧ o.F.ns = F.ns ∧ o.F.LS = F.LS ∧ o.F.vp = F.vp ∧
      o.F.mf = F.mf ∧ o.L.arrayOf = L.arrayOf ∧ o.L.check = L.check ∧ o.L.handed = true ∧
      o.F.LS.size = o.F.ns := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, he, h⟩ := ok_bind h
  obtain ⟨_, hn, h⟩ := ok_bind h
  obtain ⟨_, hz, h⟩ := ok_bind h
  have hn' : F.nClaim = 0 := by simpa using need_ok hn
  have hz' : F.LS.size = F.ns := by simpa using need_ok hz
  have e : o' = o := Except.ok.inj h
  subst e
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  have e := Except.ok.inj ho
  rw [← e]
  exact ⟨fill_empty F L.list (need_ok he), rfl, hn', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hz'⟩

/-! ## The batching's block -/

variable {T : Type}

/-- **The inversion of the batching's step.** -/
theorem batch_step (X : Lens T) (p : Where) (f : T → Except String (List Claim × T)) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat)
    (h : (batch X p f).step ft s rs cols = .ok (s', k)) :
    ∃ r x a o cls s₂ b G, rs = [r] ∧ r.drawn.elems = [x] ∧ X.get? s = some a ∧
      drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o ∧
      f (X.set s { a with owed := o.owed, L := o.L, F := o.F }) = .ok (cls, s₂) ∧
      X.get? s₂ = some b ∧ addAll b.F cls = some G ∧ s' = X.set s₂ { b with F := G } := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t', hdec, h⟩ := ok_bind h
  have e : t' = s' := congrArg Prod.fst (Except.ok.inj h)
  subst e
  simp only [batch] at hdec
  obtain ⟨t₁, h1, h2⟩ := ok_bind hdec
  simp only [adds] at h2
  obtain ⟨_, _, h2⟩ := ok_bind h2
  obtain ⟨_, _, h2⟩ := ok_bind h2
  obtain ⟨y, hy, h2⟩ := ok_bind h2
  obtain ⟨b, hb, h2⟩ := ok_bind h2
  obtain ⟨G, hG, h2⟩ := ok_bind h2
  have e2 := Except.ok.inj h2
  simp only [drawAlone] at h1
  match rs, h1 with
  | [r], h1 =>
    simp only [List.map_cons, List.map_nil] at h1
    obtain ⟨a, ha, h1⟩ := ok_bind h1
    obtain ⟨chi, hchi, h1⟩ := ok_bind h1
    obtain ⟨o, ho, h1⟩ := ok_bind h1
    have e1 := Except.ok.inj h1
    have hc := there_ok hchi
    have hel : (noDigest r).drawn.elems = r.drawn.elems := rfl
    rw [hel] at hc
    match hq : r.drawn.elems, hc with
    | [x], hc =>
      have ec : E.ofTriple x = chi := Option.some.inj hc
      subst ec
      refine ⟨r, x, a, o, y.1, y.2, b, G, rfl, hq, there_ok ha, ho, ?_, there_ok hb,
        addList_older _ _ _ hG, e2.symm⟩
      rw [e1]
      exact hy

/-- **What the batching adds.** -/
theorem batch_adds (X : Lens T) (p : Where) (f : T → Except String (List Claim × T)) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat)
    (h : (batch X p f).step ft s rs cols = .ok (s', k)) :
    ∃ x a, ∃ o : Drawn, ∃ cls s₂ b G, rs.flatMap (·.drawn.elems) = [x] ∧ X.get? s = some a ∧
      ledgerEmpty a.F = true ∧ ledgerEmpty o.F = true ∧ o.F.theta = E.ofTriple x ∧
      o.F.nClaim = 0 ∧
      f (X.set s { a with owed := o.owed, L := o.L, F := o.F }) = .ok (cls, s₂) ∧
      X.get? s₂ = some b ∧ s' = X.set s₂ { b with F := G } ∧
      (b.F.LS.size = b.F.ns → ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K),
        G.total ρ W = b.F.total ρ W +
          claimsSum ρ W (ρ.val b.F.theta) b.F.planClaimsF b.F.nClaim cls) := by
  obtain ⟨r, x, a, o, cls, s₂, b, G, rfl, hx, ha, ho, hf, hb, hG, hs'⟩ :=
    batch_step X p f ft s rs cols s' k h
  have hd := drawnClean_ok _ _ _ _ _ _ _ ho
  have hea : ledgerEmpty a.F = true := by
    unfold drawnClean at ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨_, he, _⟩ := ok_bind ho
    exact need_ok he
  exact ⟨x, a, o, cls, s₂, b, G, by simp [hx], ha, hea, hd.1, hd.2.1, hd.2.2.1, hf, hb, hs',
    fun hsz K _ ρ W => (addAll_total ρ W cls b.F G hsz hG).1⟩

/-- The ledger at which the claims are added is as the draw laid it, as far as the sums go: empty;
it holds chi; no claim is counted; one coefficient for each slot. -/
structure Clean (chi : E) (F : Fork) : Prop where
  empty : ledgerEmpty F = true
  holdsChi : F.theta = chi
  noClaim : F.nClaim = 0
  sized : F.LS.size = F.ns

/-- **At a clean ledger the new ledger's value is the sum of the claims, numbered from 0.** -/
theorem addAll_clean {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (chi : E) (F G : Fork)
    (cls : List Claim) (hc : Clean chi F) (h : addAll F cls = some G) :
    G.total ρ W = claimsSum ρ W (ρ.val chi) F.planClaimsF 0 cls := by
  rw [(addAll_total ρ W cls F G hc.sized h).1, total_of_empty ρ W F hc.empty, zero_add,
    hc.holdsChi, hc.noClaim]

/-! ## The equation's block -/

/-- **The inversion of the equation's step**, as far as K9.equation. -/
theorem equation_step {Cl : Type} (X : Lens T) (p : Where) (ft : Nat) (s : T) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : T) (k : Nat)
    (h : (oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k)) :
    ∃ a q G, X.get? s = some a ∧ equation a.L a.F = .ok (q, G) := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t', hdec, h⟩ := ok_bind h
  simp only [oneEquation] at hdec
  obtain ⟨a, ha, hdec⟩ := ok_bind hdec
  obtain ⟨o, ho, hdec⟩ := ok_bind hdec
  unfold door at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨y, hy, ho⟩ := ok_bind ho
  exact ⟨a, y.1, y.2, there_ok ha, hy⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.fill_empty
#print axioms VerifiableInference.Desc.K9L.drawnClean_ok
#print axioms VerifiableInference.Desc.K9L.batch_step
#print axioms VerifiableInference.Desc.K9L.batch_adds
#print axioms VerifiableInference.Desc.K9L.addAll_clean
#print axioms VerifiableInference.Desc.K9L.equation_step
