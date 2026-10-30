-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqBack.lean: TWO STEPS BACK FROM A STATE THAT IS REACHED IN FRONT OF THE SUB-PROTOCOL "THE ONE
EQUATION", WITH THE TWO STATES IN FRONT AND THE TWO YESES NAMED. At each of the 25 segments of the first chain, under the
library's hypothesis `AtMgA`; whoever plays; general in the first states (`start`) and in the number of the first tree (`ft`).

Honest/K9/EqTrace.lean draws its facts off these two yeses and does not hand them on. Whoever needs a law "from a yes of the
step behind the batching" (such as the library's `termsV_scope`, Johnson/AtFull/Shape/RowFormSeat.lean) wants the yes itself.

  **`eq_two_back`**       l < 25, s reached at 14 l + `IM.nAt l` + 4: there are the seated segment's letters Lk, p, w, a state s₂ reached
      two borders in front, a state s₁ reached one border in front, and χ, y, G with: `BatBehind` from s₂ to s₁ (what a yes of
      the batching leaves: Honest/K9/YesAtSeat.lean); s₁ bears no mark of failure; `Lk.runBehind s₁ = .ok s`
  `open_of_back`      behind the two yeses a segment's book-keeping and a ledger are open, and the slots in use are told
  `NoForm F`           no virtual row of the ledger F has a product form or lists of factors (the premise of the library's
      `rowClean_of_fresh`, Johnson/AtFull/Shape/RowFormLedger.lean)
  `noForm_of_frame`    it is read off the arrays' frame (`treesFrame`)
  `noForm_fill`        the draw's filling of the weights on columns (`t2FillL`) keeps it
  **`noForm_behind`**  so, at a yes of the batching from s₂ to s₁: if it holds of the ledger that is read at s₂, it holds of the
      ledger at s₁

Limits. Of a reached state: that anything is reached is not proved here. That a ledger in front of a batching is fresh is not
proved here. The full size and the hash function `secondHashFunction` alone: the hypothesis's. This file proves no property of a prover or
a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqTrace
import Johnson.AtFull.Shape.RowFormLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Fo (rowAt HasRow)
open Johnson.AtFull.Shape (NoLists)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Two steps back, with the states and the yeses named.** -/
theorem eq_two_back (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {Q : Type} {start : Q → TS}
    {ft : ℕ} {pub : Q} {s : TS} (hr : Reach ft cF.blocksInOrder start (14 * l + IM.nAt l + 4) (pub, s)) :
    ∃ Lk p w s₂ s₁ χ y G, SeatedFree cF Zp l (IM.nAt l) Lk p w ∧
      Reach ft cF.blocksInOrder start (14 * l + IM.nAt l + 2) (pub, s₂) ∧
      Reach ft cF.blocksInOrder start (14 * l + IM.nAt l + 3) (pub, s₁) ∧
      BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s₂ χ y G s₁ ∧ s₁.failed = none ∧
      Lk.runBehind s₁ = .ok s := by
  obtain ⟨Lk, p, w, Sd₀⟩ := seated_at_head h l hl
  have Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w := Sd₀
  obtain ⟨z1, s₁, s', b1, e1, hr1, hb1, hy1⟩ := reach_pred (k := 14 * l + IM.nAt l + 3) hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain ⟨z2, s₂, s'', b2, e2, hr2, hb2, hy2⟩ := reach_pred (k := 14 * l + IM.nAt l + 2) hr1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
  obtain ⟨bb, hbb, -, hdec⟩ := Sd.behind
  obtain rfl : bb = b1 := Option.some.inj (hbb.symm.trans hb1)
  obtain rfl : Lk.batch (claimsInBy Lk.each Lk.hear Lk.order) = b2 := Option.some.inj (Sd.batching.symm.trans hb2)
  obtain ⟨rs1, gs1, hd1⟩ := stepYes_decide hy1
  rw [hdec] at hd1
  obtain ⟨R, c, -, hstep⟩ := hy2
  obtain ⟨r0, tr, -, -, -, y, G, hB, hf, -⟩ := behind_of_step Sd ft s₂ s₁ R c c.length hstep
  exact ⟨Lk, p, w, s₂, s₁, E.ofTriple tr, y, G, Sd, hr2, hr1, hB, hf, hd1⟩

/-- **What is open behind the two yeses**: a segment's book-keeping, a ledger; and the slots in use are told. -/
theorem open_of_back (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) {Lk : Link S ProofFile.Cl}
    (hLk : cF.links[l]? = some Lk) {p : Desc.K9.Where} {g : S → Except String (List Claim × S)} {s₂ s₁ s : TS} {χ : E}
    {y : S × Desc.K9.Part × List Claim} {G : Fork} (hB : BatBehind p g s₂ χ y G s₁)
    (hrun : Lk.runBehind s₁ = .ok s) :
    (∃ L, s.link? = some L) ∧ (∃ F, s.fork? = some F) ∧ (Desc.K9.usedOf s).isSome = true := by
  obtain ⟨t₁, -, -, he⟩ := gathered_split p g s₂ _ y hB.gathered
  obtain ⟨e1, F1, tl1, g1, -, -, -, -, hF⟩ := behind_at_head h l hl Lk hLk S.link? rests_link s₁ s hrun
  refine ⟨⟨y.2.1.L, ?_⟩, ⟨_, hF⟩, ?_⟩
  · rw [e1, hB.state]
    exact set_link y.1 y.2.1 _ he
  · have e2 := (behind_at_head h l hl Lk hLk LinkJoin.usedSome LinkJoin.rests_usedSome s₁ s hrun).1
    have e3 : LinkJoin.usedSome s = true := by
      rw [e2, hB.state, LinkJoin.usedSome_set]
      exact used_of_part he
    exact e3

/-- No virtual row of the ledger has a product form or lists of factors. -/
def NoForm (F : Fork) : Prop := ∀ t e, HasRow F t e → (rowAt F t e).rowForm = false ∧ NoLists (rowAt F t e)

/-- Of each virtual row of each array: the mark "it has a product form" and the two lists of factors. -/
def flagsOf (A : Array HTree) : Array (Array (Bool × Array E × Array E)) :=
  A.map fun X => X.rows.map fun r => (r.rowForm, r.rowLo, r.rowHi)

/-- Two arrays with one image under f: their members of one number have one image. -/
theorem getD_of_map {α β : Type} (f : α → β) (d : α) (A B : Array α) (h : A.map f = B.map f) (i : ℕ) :
    f (A.getD i d) = f (B.getD i d) := by
  have h1 := congrArg (fun X => X[i]?) h
  simp only [Array.getElem?_map] at h1
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases hA : A[i]? with
  | none =>
    cases hB : B[i]? with
    | none => rfl
    | some Y => rw [hA, hB] at h1; simp at h1
  | some X =>
    cases hB : B[i]? with
    | none => rw [hA, hB] at h1; simp at h1
    | some Y =>
      rw [hA, hB] at h1
      exact Option.some.inj h1

/-- A row's three, read off `flagsOf`. -/
theorem row_of_flags {A B : Array HTree} (h : flagsOf A = flagsOf B) (t e : ℕ) :
    A.size = B.size ∧ (A.getD t {}).rows.size = (B.getD t {}).rows.size ∧
      ((A.getD t {}).rows.getD e {}).rowForm = ((B.getD t {}).rows.getD e {}).rowForm ∧
      ((A.getD t {}).rows.getD e {}).rowLo = ((B.getD t {}).rows.getD e {}).rowLo ∧
      ((A.getD t {}).rows.getD e {}).rowHi = ((B.getD t {}).rows.getD e {}).rowHi := by
  have hs : A.size = B.size := by
    have := congrArg Array.size h
    simpa [flagsOf] using this
  have ht : ((A.getD t {}).rows.map fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) =
      (B.getD t {}).rows.map fun r : HRow => (r.rowForm, r.rowLo, r.rowHi) :=
    getD_of_map (fun X : HTree => X.rows.map fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) {} A B h t
  have hz : (A.getD t {}).rows.size = (B.getD t {}).rows.size := by
    have := congrArg Array.size ht
    simpa using this
  have he := getD_of_map (fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) {} _ _ ht e
  obtain ⟨k1, k23⟩ := Prod.mk.inj he
  obtain ⟨k2, k3⟩ := Prod.mk.inj k23
  exact ⟨hs, hz, k1, k2, k3⟩

theorem noForm_of_flags {F G : Fork} (h : flagsOf G.trees = flagsOf F.trees) (hF : NoForm F) : NoForm G := by
  intro t e hr
  obtain ⟨h1, h2, k1, k2, k3⟩ := row_of_flags h t e
  have hr' : HasRow F t e := ⟨h1 ▸ hr.1, h2 ▸ hr.2⟩
  obtain ⟨a, b, c⟩ := hF t e hr'
  exact ⟨k1.trans a, k2.trans b, k3.trans c⟩

/-- The arrays' frame holds them. -/
theorem flags_of_frame {A B : Array HTree} (h : treesFrame A = treesFrame B) : flagsOf A = flagsOf B := by
  have e : ∀ C : Array HTree, flagsOf C =
      (treesFrame C).map fun q => q.2.map fun u => (u.1.rowForm, u.1.rowLo, u.1.rowHi) := by
    intro C
    unfold flagsOf treesFrame
    rw [Array.map_map]
    congr 1
    funext X
    show _ = (X.rows.map HRow.frame).map _
    rw [Array.map_map]
    rfl
  rw [e A, e B, h]

/-- It is read off the arrays' frame. -/
theorem noForm_of_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) (hF : NoForm F) : NoForm G :=
  noForm_of_flags (flags_of_frame h) hF

/-- The draw's filling of the weights on columns leaves them. -/
theorem flags_fill (F : Fork) (T : Tail2) : flagsOf (t2FillL F T).trees = flagsOf F.trees := by
  have key : ∀ (f : HTree → HTree),
      (∀ X, ((f X).rows.map fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) =
        X.rows.map fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) →
      ∀ (l : List ℕ) (A : Array HTree), flagsOf (l.foldl (fun trees ti => trees.modify ti f) A) = flagsOf A := by
    intro f hf l
    induction l with
    | nil => intro A; rfl
    | cons i l ih =>
      intro A
      rw [List.foldl_cons, ih]
      exact map_modify_same _ f hf A i
  unfold t2FillL
  refine key _ (fun X => ?_) _ _
  show (X.rows.map _).map _ = _
  rw [Array.map_map]
  congr 1
  funext r
  show (fun r : HRow => (r.rowForm, r.rowLo, r.rowHi)) (if r.L.size != X.K then _ else r) = _
  split <;> rfl

theorem noForm_fill (F : Fork) (T : Tail2) (hF : NoForm F) : NoForm (t2FillL F T) := noForm_of_flags (flags_fill F T) hF

/-- **Over a yes of the batching.** -/
theorem noForm_behind {c : Chain S Claim} {Z₀ : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z₀ l k Lk p w) {s₂ s₁ : S} {χ : E}
    {y : S × Desc.K9.Part × List Claim} {G : Fork}
    (hB : BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s₂ χ y G s₁)
    (hF : ∀ F, s₂.fork? = some F → NoForm F) : NoForm G := by
  obtain ⟨t₁, hdraw, hg, he⟩ := gathered_split p _ s₂ _ y hB.gathered
  obtain ⟨a, ha⟩ := draw_open p s₂ t₁ _ hdraw
  obtain ⟨a₁, h1, hl1⟩ := draw_facts p s₂ t₁ _ a ha hdraw
  obtain ⟨a', ha', hcore⟩ := Sd.keeps t₁ y.1 y.2.2 a₁ hg h1
  obtain rfl : a' = y.2.1 := Option.some.inj (ha'.symm.trans he)
  have f0 : NoForm a.F := hF a.F (Desc.K9.Shape.part_reads ha).2
  have f1 : NoForm a₁.F := noForm_of_flags (by rw [hl1.trees]) (noForm_fill a.F a.L.list f0)
  exact noForm_of_frame hB.all.frame (noForm_of_frame hcore.frame f1)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_two_back
#print axioms ProofFile.Honest.K9.open_of_back
#print axioms ProofFile.Honest.K9.getD_of_map
#print axioms ProofFile.Honest.K9.row_of_flags
#print axioms ProofFile.Honest.K9.noForm_of_flags
#print axioms ProofFile.Honest.K9.flags_of_frame
#print axioms ProofFile.Honest.K9.noForm_of_frame
#print axioms ProofFile.Honest.K9.flags_fill
#print axioms ProofFile.Honest.K9.noForm_fill
#print axioms ProofFile.Honest.K9.noForm_behind
