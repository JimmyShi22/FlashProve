-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/Walk.lean: THE RECORD'S
HALF OF THE SEVEN ROWS OF A LOOKUP'S LINK IS KEPT BY THE LINK'S SIX BLOCKS, EACH BY ITS OWN YES, at
a plan that passes the public tests on the lookup. The condition of each of the seven rows (rows7,
LinkSeats.lean) is the decoder's condition at the riding part AND a clause on the record that reads
no oracle and no letter of the rows (RecL). Whoever holds that a record was reached by the blocks'
yeses holds the second half for nothing.

Main names:
  RecL i j s: the record's half of row j of the link of lookup number i.
  rows7_on: the row's condition is the decoder's condition and RecL.
  heardOk_of_yes: behind the kind's own block the record holds what HeardOk says: from the block's
    yes at ANY rounds: no test on the rounds' words is asked.
  link_walk: THE SIX STEPS: RecL i j s, block j's yes from s to s' ⊢ RecL i (j + 1) s'.
  recL_next: row 6 of a link is row 0 of the next.

Object: the six blocks of Key.lookupLink's flat list (Johnson/Desc/Key/Link.lean).
User: fk_walk (WalkAtFK.lean).
Letters: one, set, id, m, L, oL, kL, idxN, n, Prom (under Promise). Public premises on lookup number
i, as link_seats has them: Adm · d ≤ 64 · lookupOk · fitsMatrix · lookups[i]? · the layout's first
block fits · i < n.

Limits. Nothing on the decoder's condition. Nothing on the rows' relations. Nothing on soundness.

-/
import Johnson.RunOne.Law.LinkSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.Walk
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block claimsIn afterIn)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim lookupSeat lookupLink lookupPlace caller layer)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.LinkKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LinkSeats

variable (one : OneTime) (set : Setting) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup)
  (oL kL : ℕ → List ℕ) (idxN : ℕ) (Prom : ℕ → FirstState → Prop)

/-- **The record's half of row j of the link of lookup number i.** -/
def RecL (i : ℕ) : ℕ → FirstState → Prop
  | 0 => fun s => s.base.rows.length = i ∧ s.base.keys.length = i ∧ Prom i s
  | 1 => fun s => (Hands one id m (L i) (oL i) (kL i) idxN s ∧
      Fits one id m (L i) (oL i) (kL i) idxN s.d.st ∧ s.base.rows.length = i) ∧ Prom i s
  | 2 => fun s => ((∀ F0, lookupSeat.fork s = some F0 → PscRun.Sized F0) ∧
      Inv one i id m (L i) (oL i) (kL i) idxN s) ∧ Prom (i + 1) s
  | 3 => fun s => (Inv one i id m (L i) (oL i) (kL i) idxN s ∧
      HeardOk lookupSeat (lookupPlace set i (Wf.lookupOf id m (L i))) s) ∧ Prom (i + 1) s
  | 4 => fun s => (Fits one id m (L i) (oL i) (kL i) idxN s.d.st ∧ s.base.rows.length = i + 1 ∧
      s.base.keys.length = i + 1) ∧ Prom (i + 1) s
  | 5 => fun s => (Fits one id m (L i) (oL i) (kL i) idxN s.d.st ∧ s.base.rows.length = i + 1 ∧
      s.base.keys.length = i + 1) ∧ Prom (i + 1) s
  | _ => fun s => s.base.rows.length = i + 1 ∧ s.base.keys.length = i + 1 ∧ Prom (i + 1) s

/-- Row 6 of a link is row 0 of the next. -/
theorem recL_next (i : ℕ) (s : FirstState) :
    RecL one set id m L oL kL idxN Prom i 6 s ↔ RecL one set id m L oL kL idxN Prom (i + 1) 0 s :=
  Iff.rfl

variable {Fr : Frame} {P M Wp : Type} (p₀ : P) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
  (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (n : ℕ)
  (Oth : TK P → M × Wp → Prop)

/-- **A row's condition is the decoder's condition at the riding part, and the record's half.** -/
theorem rows7_on (i j : ℕ) (hj : j ≤ 6) (s : FirstState) (y : Fr.E.Str) :
    (rows7 p₀ one set id m L oL kL idxN wd mx dec cond n Prom i Wp Oth j).on (s, y) ↔
      cond (stK p₀ (if j = 6 then i + 1 else i) s, y) ∧
        RecL one set id m L oL kL idxN Prom i j s := by
  have c7 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases c7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ofBorder_on _ _ _
  · exact Iff.rfl
  · exact Iff.rfl
  · exact ⟨fun h => ⟨h.1.1, ⟨h.1.2.1, h.1.2.2⟩, h.2.2⟩,
      fun h => ⟨⟨h.1, h.2.1.1, h.2.1.2⟩, trivial, h.2.2⟩⟩
  · exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, trivial, h.2.2⟩⟩
  · exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, trivial, h.2.2⟩⟩
  · exact ofBorder_on _ _ _

variable {one set id m L oL kL idxN Prom}

/-- **Behind the kind's own block the record holds what HeardOk says**: from the block's yes at any
rounds. -/
theorem heardOk_of_yes {S Cl : Type} {σ : SeatG S Cl} {p : PG} {A : Lk6.Dat GE} {st : A.St}
    {o k home : ℕ → Slot} (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)) (hf : FaceIs A st p.face)
    (hadm : A.toPub.Adm Cb.Gl.p) (hh : HomeIs p.face p.first o k home)
    (h1 : ∀ s g G, σ.fork (σ.put s g G) = some G) (h2 : ∀ s g G, σ.heard (σ.put s g G) = some g)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hS : ∀ F0, σ.fork s = some F0 → PscRun.Sized F0)
    (hd : (lookupKind σ before bits guests p).decide s rs gs = .ok s') :
    HeardOk σ p s' ∧ ∃ g G, s' = σ.put s g G := by
  obtain ⟨F0, g, G, es, e1, e2, -, -, e5, rfl⟩ := block_law σ before bits guests p hd
  obtain ⟨hok, t, -, hm⟩ := hearE_inv e5
  have hal : Al home o k (fromKeys p.face) F0.next 0 0 := by
    rw [e2]
    exact al_of_homeIs hh
  obtain ⟨-, c2, -, -, c5, c6, -, -⟩ := hear_course ⟨fun _ => 0⟩ hf hadm hok hm (hS F0 e1) hal
  obtain ⟨k1, k2⟩ := heard_keys hf.noShift e5
  exact ⟨⟨G, g, h1 s g G, h2 s g G, c5, by rw [c6, e2], c2, k1, k2⟩, g, G, rfl⟩

/-- The step of the kind's own block. -/
theorem k3_walk (hP : Promise one id m L oL kL idxN n Prom) (i : ℕ)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p) (hd : (L i).d ≤ 64)
    (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hr : RecL one set id m L oL kL idxN Prom i 2 s)
    (hy : (lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (lookupPlace set i (Wf.lookupOf id m (L i)))).decide s rs gs = .ok s') :
    RecL one set id m L oL kL idxN Prom i 3 s' := by
  obtain ⟨⟨hS, hI⟩, hq⟩ := hr
  obtain ⟨hH, g, G, rfl⟩ := heardOk_of_yes (σ := lookupSeat)
    (p := lookupPlace set i (Wf.lookupOf id m (L i)))
    (A := AK one id m (L i) (oL i) (kL i) idxN Unit) (st := ()) [(1, 0), (1, 1)] 0 []
    (faceIsK Unit id m (L i) _ () hadm hd) hadm (homeIs_of_size _ _ _ hI.2.2.2.2)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hS hy
  exact ⟨⟨hI, hH⟩, hP.blind (i + 1) s _ _ s.base.home hq⟩

set_option maxHeartbeats 1600000 in
/-- **THE SIX STEPS.** -/
theorem link_walk (y : Fr.E.Str) (hP : Promise one id m L oL kL idxN n Prom) (i : ℕ) (hi : i < n)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p) (hd : (L i).d ≤ 64)
    (hlo : Wf.lookupOk Wf.fBits (L i) = true) (hfm : Wf.fitsMatrix m (L i) = true)
    (hli : one.ranges.lookups[i]? = some (L i))
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true)
    (j : ℕ) (hj : j < 6) (c : Block FirstState Claim)
    (hc : (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]? = some c) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hr : RecL one set id m L oL kL idxN Prom i j s) (hy : c.decide s rs gs = .ok s') :
    RecL one set id m L oL kL idxN Prom i (j + 1) s' := by
  obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat one set i (Wf.lookupOf id m (L i))
  rw [hF] at hc
  -- the rows at letters that say nothing
  let wd0 : Unit → Means.Words GE := fun _ _ _ _ => 0
  let mx0 : Unit → ℕ → ℕ → GE := fun _ _ _ => 0
  let dec0 : TK Unit × Fr.E.Str → Option Unit := fun _ => none
  let cond0 : TK Unit × Fr.E.Str → Prop := fun _ => True
  let Oth0 : TK Unit → Unit × Unit → Prop := fun _ _ => True
  have up : ∀ j', j' ≤ 6 → ∀ t, RecL one set id m L oL kL idxN Prom i j' t ↔
      (rows7 () one set id m L oL kL idxN wd0 mx0 dec0 cond0 n Prom i Unit Oth0 j').on (t, y) :=
    fun j' hj' t => ((rows7_on one set id m L oL kL idxN Prom () wd0 mx0 dec0 cond0 n Oth0 i j' hj'
      t y).trans ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩).symm
  have tie : ∀ {b : Block FirstState Claim} (j' : ℕ), j' < 6 →
      QuietTie b (rows7 () one set id m L oL kL idxN wd0 mx0 dec0 cond0 n Prom i Unit Oth0 j')
        (rows7 () one set id m L oL kL idxN wd0 mx0 dec0 cond0 n Prom i Unit Oth0 (j' + 1)) →
      ∀ t t', RecL one set id m L oL kL idxN Prom i j' t → b.decide t rs gs = .ok t' →
        RecL one set id m L oL kL idxN Prom i (j' + 1) t' :=
    fun j' hj' h t t' ht hb =>
      (up (j' + 1) hj' t').2 (h t t' y rs gs ((up j' (Nat.le_of_lt hj') t).1 ht) hb).1
  have c6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases c6 with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj hc
    exact tie 0 hj (laid_tie (fun s s' rs gs h => lay_same ((d0 s rs gs) ▸ h)) (Prom i) i
      fun s => hP.gives i s hi) s s' hr hy
  · obtain rfl := Option.some.inj hc
    exact tie 1 hj (callerJ_tie hP i) s s' hr hy
  · obtain rfl := Option.some.inj hc
    exact k3_walk n hP i hadm hd s s' rs gs hr hy
  · obtain rfl := Option.some.inj hc
    exact tie 3 hj (layerJ_tie hP i hadm hlo hfm hli hla) s s' hr hy
  · obtain rfl := Option.some.inj hc
    exact tie 4 hj (same_tie _ fun s s' rs gs h => after_same ((d4 s rs gs) ▸ h)) s s' hr hy
  · obtain rfl := Option.some.inj hc
    exact tie 5 hj (cleared_tie (fun s s' rs gs h => clear_eq ((d5 s rs gs) ▸ h))
      (fun _ _ _ _ _ _ => ⟨rfl, Iff.rfl, fun _ => Iff.rfl⟩) (Prom (i + 1)) (Prom (i + 1)) i
      fun s => hP.blind (i + 1) s none none #[]) s s' hr hy

end Johnson.RunOne.Law.Walk

#print axioms Johnson.RunOne.Law.Walk.rows7_on
#print axioms Johnson.RunOne.Law.Walk.heardOk_of_yes
#print axioms Johnson.RunOne.Law.Walk.k3_walk
#print axioms Johnson.RunOne.Law.Walk.link_walk
