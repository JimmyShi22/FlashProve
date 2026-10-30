-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Law.FirstBelow
import Johnson.Desc.K12.Law.OwnMaskStep
import Johnson.Desc.K12.Law.AccKOwn
/-
Johnson/Desc/K12/Coin/GameLabelsOwn.lean: THE GAME OF THE PROXIMITY TEST, SECOND ARM (the first fold sends its own mask), WITH NOTHING PROMISED OF THE RECORD: the book's places are numbered by the labels of the trees that stand there. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHOSE PATTERN: the first arm's (Coin/GameLabels.lean: nuOf · firstOpens_of_labels · leads_at · k12_gameV and its seat | alike forms): here its texts again at the second arm. NO NEW MATHEMATICS: an assembly.
  yes_own: a yes of the piece at a place with ownMask = true: at whatever the record fixes: D.ts ENDS IN THE MASK's PLACE, and NO MEMBER STANDS THERE (lastOk_of_step · last_of_ok · hmask_of_step · aloneAt_of_step_own · alone_at, carried from the step to «what the record fixes» as Coin/Labels.lean's yes_labels carries the labels' equation).
  numO: num with 0 at the taken sources: a device: under ownLabelsB no declared opening is taken, so the pin n3 of our FirstBelow.lean is asked of nobody.
  firstOpensOwn_of_labels: ownLabelsB π · firstNe π · 0 < free · the labels' equation · the two facts of yes_own ⇒ FirstOpensOwn π (numAt t₁ t₂ ch) (nuOf π (nlAt π lo) t) (lo + free) t, lo := numAt t₁ t₂ ch (.own 0): clause 1 as in the first arm · clause 3 by freshBase · clause 2 by membersBelowOwn.
  k12_gameVO: THE GAME AT THE BLOCK's OWN RECORD: Leads (fun _ => True), AND THE CONCLUSION HOLDS FirstOpensOwn BESIDE QN (it reads the record alone; whoever wants the members' trees below base behind the game has it there).
  k12_gameSeatVO · k12_game_alikeVO: at every seat · at any piece, at any type of claims, whose block is alike to the held seat.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.Pin (NTuple)
open H2K.Pub (PayPub)
open H2K.First (gpOf Plain opensOf made_of aloneOk last_of_ok)

/-- **What a yes gives at the second arm, at whatever the record fixes.** -/
theorem yes_own {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = true) (base : ℕ)
    (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π x.1 a rest G0 Ly D) :
    D.ts.getLast? = some D.fresh.t ∧ aloneOk D = true := by
  obtain ⟨m, c, τ'⟩ := τ
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x (m, c, τ') b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1
      (r0Of dB m c :: (rvT (ckP .two) (dB :: dt) (m, c, τ')).tail)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 (m, c, τ')).opened =
      .ok (b.1, k) := hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨_, _, e, r, row, L, S', hr, hbat, _⟩ := k12_guards π he x.1 b.1 _ _ hp hdec
  have hr0 : r = noDigest (r0Of dB m c) := (List.cons.inj hr).1.symm
  subst hr0
  obtain ⟨G1, g1, g2, rfl⟩ := bat_front _ _ _ _ _ _ _ hbat
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain rfl := Option.some.inj (g1.symm.trans f2)
  obtain rfl := Option.some.inj (g2.symm.trans f3)
  have hm := hmask_of_step π he x.1 b.1 F.ft k _ _ _ hp hst' ho
  exact ⟨last_of_ok π _ a rest row L D f1 rfl (f4 row) hm
      (lastOk_of_step π he x.1 b.1 F.ft k _ _ _ hp hst' e row L _ hbat),
    alone_at π _ a rest row L D f1 rfl (f4 row)
      (aloneAt_of_step_own π he x.1 b.1 F.ft k _ _ _ hp hst' e row L _ hbat ho)⟩

/-- num, with 0 at the taken sources. -/
def numO (num : Fmt.TreeSource → ℕ) : Fmt.TreeSource → ℕ
  | .own n => num (.own n)
  | .taken _ _ => 0

/-- What ownLabelsB says. -/
theorem ownLabels_at {π : P12} (h : ownLabelsB π = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: rest) :
    ∀ o ∈ opensOf π a.k, ∃ n, o.2 = .own n ∧ o.1.tree = π.nums.firstTree + n := by
  intro o ho
  unfold ownLabelsB at h
  rw [hs] at h
  have h1 := List.all_eq_true.1 h o ho
  obtain ⟨sh, src⟩ := o
  cases src with
  | taken c s => simp at h1
  | own n => exact ⟨n, rfl, of_decide_eq_true h1⟩

/-- **The labels' equation, two facts of a yes and three tests on the plan give the promise of the
second arm, at the numbering off the record.** -/
theorem firstOpensOwn_of_labels (π : P12) (t₁ t₂ ch : ℕ) (t : T12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = true)
    (hP : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free)
    (hl : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D →
      D.opens.map (·.1.tree) = D.ts.map (H2K.First.numAt D.book))
    (hy : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D →
      D.ts.getLast? = some D.fresh.t ∧ aloneOk D = true) :
    FirstOpensOwn π (numAt t₁ t₂ ch) (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t)
      (numAt t₁ t₂ ch (.own π.nums.free)) t := by
  intro a rest G0 Ly D hf
  have heq := hl a rest G0 Ly D hf
  obtain ⟨hlast, hal⟩ := hy a rest G0 Ly D hf
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  have hop : D.opens = opensOf π a.k := hmd.opens
  have hO : ∀ o ∈ D.opens, ∃ n, o.2 = .own n ∧ o.1.tree = π.nums.firstTree + n := by
    rw [hop]
    exact ownLabels_at hP a rest hf.1
  have hnum : ∀ n, numAt t₁ t₂ ch (.own n) = numAt t₁ t₂ ch (.own 0) + n := fun n => by
    show _ + n = _ + 0 + n
    omega
  have e0 : ∀ o ∈ D.opens, numAt t₁ t₂ ch o.2 =
      nlAt π (numAt t₁ t₂ ch (.own 0)) o.1.tree := by
    intro o hoo
    obtain ⟨n, e1, e2⟩ := hO o hoo
    rw [e1, e2, hnum n]
    unfold nlAt
    omega
  have e1 : D.opens.map (fun o => numAt t₁ t₂ ch o.2) =
      (D.opens.map (·.1.tree)).map (nlAt π (numAt t₁ t₂ ch (.own 0))) := by
    rw [List.map_map]
    exact List.map_congr_left e0
  have e2 : D.ts.map (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t) =
      (D.ts.map (H2K.First.numAt D.book)).map (nlAt π (numAt t₁ t₂ ch (.own 0))) := by
    rw [List.map_map]
    exact List.map_congr_left fun z _ => nuOf_of_fixes hf _ z
  have h1 : D.opens.map (fun o => numAt t₁ t₂ ch o.2) =
      D.ts.map (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t) := by rw [e1, e2, heq]
  have h1' : D.opens.map (fun o => numO (numAt t₁ t₂ ch) o.2) =
      D.ts.map (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t) := by
    rw [← h1]
    refine List.map_congr_left fun o hoo => ?_
    obtain ⟨n, e, _⟩ := hO o hoo
    rw [e]
    rfl
  have M := H2K.Made.masksFixed_of_planOk π hp
  have n1 : ∀ n, numAt t₁ t₂ ch (.own (π.nums.free + n)) =
      numAt t₁ t₂ ch (.own π.nums.free) + n := fun n => by
    rw [hnum (π.nums.free + n), hnum π.nums.free]
    omega
  refine ⟨h1, ?_, M.freshBase ho a rest hf.1 _ _ n1 D _ hop h1 hlast⟩
  exact M.membersBelowOwn ho hne a rest hf.1 (numO (numAt t₁ t₂ ch)) _
    (fun n hn => by
      show numAt t₁ t₂ ch (.own n) < _
      rw [hnum n, hnum π.nums.free]
      omega)
    (fun _ _ _ => by
      show 0 < _
      rw [hnum π.nums.free]
      omega)
    D _ hop h1' hlast hmd.ts hal

/-- Of a book's place the written round reads neither the strings nor the numbering: so of the mask's
place, of which «one tuple for all rows» (NTuple) takes the written round alone, it reads no string.
-/
theorem W0_fst (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y : F.E.Str) (z : ℕ) :
    (W0 F no book y z).1 = rdOf (H2K.First.logAt book z) (H2K.First.widthAt book z) := rfl

/-- What the game concludes at the second arm, at a record and strings: the promise itself, which
reads the record alone, and one tuple for all rows. -/
def QO (F : Frame) (π : P12) (t₁ t₂ ch : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (x : T12 × F.E.Str) :
    Prop :=
  FirstOpensOwn π (numAt t₁ t₂ ch) (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) x.1)
      (numAt t₁ t₂ ch (.own π.nums.free)) x.1 ∧
    QN π (NTuple F π (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) x.1) rad rd) x

/-- **THE GAME AT THE BLOCK's OWN RECORD, SECOND ARM: NOTHING IS PROMISED.** -/
theorem k12_gameVO (F : Frame) (W : Type) (π : P12) (t₁ t₂ ch : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π (numAt t₁ t₂ ch) L mC mS mW rad (numAt t₁ t₂ ch (.own π.nums.free)) dB dt
      εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free) :
    (pieceOf (C := ckP .two) (F := F) (proximityTestKind guardedProximityTestParts π : Block T12 Unit)
        (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun _ => True) (fun x _ => QO F π t₁ t₂ ch rad rd x) (e, εt) := by
  refine leads_drop_yes (on := fun _ => True)
    (P := fun x => FirstOpensOwn π (numAt t₁ t₂ ch)
      (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) x.1) (numAt t₁ t₂ ch (.own π.nums.free)) x.1)
    ?_ ?_
  · exact Reduction.Leads.conseq
      (leads_at (fun no => k12_gameZO F W π (numAt t₁ t₂ ch) no L mC mS mW rad rd _ dB dt ext e v₀
        εt hA hP h1 hlog hle) fun x => nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) x.1)
      (fun _ hx => hx.2) (fun _ _ _ hx _ q => ⟨hx.2, q⟩)
  · intro x τ b _ hy
    exact firstOpensOwn_of_labels π t₁ t₂ ch x.1 hA.planOk ho hPl hne hfr
      (fun a rest G0 Ly D hf =>
        yes_labels (W := W) F π hA.early hA.planOk _ dB dt e εt x τ b hy a rest G0 Ly D hf)
      (fun a rest G0 Ly D hf =>
        yes_own (W := W) F π hA.early hA.planOk ho _ dB dt e εt x τ b hy a rest G0 Ly D hf)

/-- **At every seat.** -/
theorem k12_gameSeatVO (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (t₁ t₂ ch : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π (numAt t₁ t₂ ch) L mC mS mW rad (numAt t₁ t₂ ch (.own π.nums.free)) dB dt
      εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free) :
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)
        (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun _ => True)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QO F π t₁ t₂ ch rad rd (t, a.2))
      (e, εt) := by
  intro a _
  exact leads_seated (pieceT F W π (numAt t₁ t₂ ch (.own π.nums.free)) dB dt e εt) enter leave
    (fun _ => True) (fun x _ => QO F π t₁ t₂ ch rad rd x)
    (k12_gameVO F W π t₁ t₂ ch L mC mS mW rad rd dB dt (fun _ _ w => w) e v₀ εt hA hP h1 hlog hle
      ho hPl hne hfr) a (fun _ _ => trivial)

/-- **At any piece, at any type of claims, whose block is alike to the held seat.** -/
theorem k12_game_alikeVO (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (t₁ t₂ ch : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = numAt t₁ t₂ ch (.own π.nums.free))
    (hds : p.ds = dB :: dt) (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π (numAt t₁ t₂ ch) L mC mS mW rad (numAt t₁ t₂ ch (.own π.nums.free)) dB dt
      εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QO F π t₁ t₂ ch rad rd (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_alike
    (pieceOf (C := ckP .two) (F := F) (W := W)
      (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave))
      (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] ⟨fun _ _ w => w, (e, εt)⟩) p hb hbase hds
    h0 herr _ _
    (leads_lift (S := P × S) Prod.snd (fun t s => (t.1, s))
      (pieceOf (C := ckP .two) (F := F) (W := W)
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)
        (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] ⟨fun _ _ w => w, (e, εt)⟩).under
      (fun _ => True)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QO F π t₁ t₂ ch rad rd (t, a.2))
      (fun _ _ => rfl) (fun _ _ _ => rfl)
      (leads_under _ rfl _ _
        (k12_gameSeatVO S enter leave F W π t₁ t₂ ch L mC mS mW rad rd dB dt (fun _ _ w => w)
          e v₀ εt hA hP h1 hlog hle ho hPl hne hfr)))

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_own
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_of_labels
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameVO
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameSeatVO
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_alikeVO
