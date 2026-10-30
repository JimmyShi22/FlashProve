-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Pays210.lean: The key file's
tables, row 2.10 (the proximity test on Omega's group G_omega; the test's second arm): `Pays`
(Johnson/RunOne/Law/K12AtField.lean) WITH THE «law» OF THE WAY BACK PAID: one definition and one
statement; its proof is one call of `pays_of_law` (K12PaysOfLaw210.lean) at `back_210`
(K12Back210.lean). In the form of K12Pays29.lean (row 2.9).
What it is not, first.
  (0) NO EXAMPLE IS SHOWN: that the premises hold together at any state or list of rounds is not
    said.
  (1) A JOIN: it pays no debt on the verifier's state and none on the list of rounds. The debts on
    the state that `back_210` owes are one proposition, `Debts210`, asked under «on 10 a» AND the
    piece's own accepting run (hE: else a payer cannot spend that run).
  (2) The invariant behind (fwd), the letter «on» with its two ties, and the row's look-up: as in
    K12PaysOfLaw210.lean's head. THIS ROW's «on» IS ITS OWN: at row 2.9 the caller fills another:
    nobody may chain the two rows' `Pays` at one «on».
  (3) It fills no field of the tables. No soundness is claimed. Nothing on hiding.
The debts, each with its owner and state (by report, not shown here).
  hal (and that the piece holds Bb): other files', at the table's own sub-protocol. hp · hft · hj ·
    k12_gameVO's nine · the cap: on the list of rounds: K12's files': conditionals by Lake. hi ·
    hSm · hlog · told: in scope (hi_at · hSm_at · seats_six_scope, KeyAt2932Scope.lean), over the
    tables' files' layIdem_famLay · smOnlyK. hmem3 · hmem2: the filler's letters. `Debts210`:
    `CoreLeft`: the seam's core_at | coreFacts_all at the seat, by `coreLeft_of_members`; the OOD
    seeds' tie and «shown»: the bridge's; OpenKinds: openKinds_at_reached₂ off the history; the
    group and message 3: off the history (aSide₂_made; omega_shape_scope | split_shape_scope). hm2:
    a clause of the invariant's test on the state's shape. hnum₁ · heval: at the name
    (evalIn_of_free₂). hpins: four closed comparisons: K12's files'.
BESIDE THEM (`Debts210` · `pays_210`): `shape210_facts`: four clauses of the
invariant's test on the state's shape at border 10. `Debts210S`: a Lean structure, a field a debt:
what `back_210W` (K12Members210.lean) still owes of the state and the strings. `pays_210S`:
`Pays` over `back_210W`. GONE AGAINST `pays_210`: smp (↦ oNo) · `Debts210` with `CoreLeft`, the
group and message 3 · hm2. NEW: hoff · ho2 | ho3 · hf2 | hf3 · hF · hd · hE at `Debts210S` (seed2 ·
seed3 · dep · tree · sm · shown · kinds). STILL A JOIN: NO EXAMPLE; it fills no field.

-/
import Johnson.RunOne.Law.K12PaysOfLaw210
import Johnson.RunOne.Law.K12Back210
import Johnson.RunOne.Law.K12Members210
import Johnson.RunOne.Law.K12Law32Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Pays210
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held pieceOf Rest smpSt)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP)
open H2K.Pub (johOk PayPub sgOf)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.K12Back210 (i4 i5)

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a₀ : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **What `back_210` (K12Back210.lean) owes of the verifier's state in front**, in one proposition:
`CoreLeft` behind the door in · the OOD seeds' tie and «every leaf is shown» at the group's two
members · no open row is marked as a sample row · the group's members and the count of its open
rows · message 3 is sampled and has sample rows. -/
def Debts210 (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem) (a : (P₂ × St₂) × Fr₂.E.Str) : Prop :=
  (∀ t, Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t →
    CoreLeft csKey F Fr₂ π (noAt t₁ t₂ 1) (fun s => r s.st) smp mem
      (fun z => z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩) t a.2 a.1 (strsOf Fr₂ a.2)) ∧
  (∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
    smp a.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a.1 ρ σ.2) ∧
  (∀ i : Fin six.length, i = i5 ∨ i = i4 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ a.2) i) ∧
  Means.OpenKinds a.1.2.st ∧
  (∀ G0, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G0 →
    (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size) ∧
  ∃ x0 : OnBytes.Oracle, a.1.2.st.oracles[3]? = some x0 ∧ x0.sampled = true ∧
    x0.sampleRows.size ≠ 0

/-- **`Pays` at row 2.10.** The debts on the verifier's state stand under the piece's accepting
run. The law's errors (e, εt) and its counts are letters: that they are small is hle's matter alone.
-/
theorem pays_210 {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 10 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 b →
      on 11 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 10) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hft : π.nums.firstTree = 0)
    (hj : johOk π r = true)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hE : ∀ a τ b, on 10 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts210 F Fr₂ orc₁ π t₁ t₂ r smp mem a)
    (hm2 : ∀ a, on 10 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (heval : ∀ a, on 10 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (hbase : base = numAt t₁ t₂ 1 (.own π.nums.free))
    (Lc mC mS mW : Sg → ℕ → ℕ) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn Fr₂ π (numAt t₁ t₂ 1) Lc mC mS mW (fun s => r s.st)
      (numAt t₁ t₂ 1 (.own π.nums.free)) dB dt εt)
    (hP : PayPub π (fun s => r s.st) dB.entry.rows v₀)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog64 : dB.entry.logN ≤ 64)
    (hv : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free)
    (hle : Err.le ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 10 base (dB :: dt) []
      x' := by
  refine K12PaysOfLaw210.pays_of_law F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π t₁
    t₂ r rdN on hin hbk Bb fwd hal hp hSm base hpins dB dt x' (fun a τ b ha hout hq => ?_) hm2
    hnum₁ heval hbase Lc mC mS mW e v₀ εt hA hP h1 hlog64 hv ho hPl hne hfr hle
  have hon := hin a ha
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨left, hsm, hsh, hK, hgrp, x0, hx, hsmd, hss⟩ := hE a τ b ha hout
  obtain ⟨z2, hz2, _⟩ := hm2 a ha
  exact K12Back210.back_210 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π t₁ t₂ r rdN
    smp mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal hp a b τ hout hq hft hon hj
    left hi hlog told hsm hsh hmem3 hmem2 hK hgrp x0 hx hsmd hss hSm
    (fun o ho => by
      have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix 4).1
          (atSix 4).2 = 4 := hfree.arr 4 (by decide)
      rw [earr] at ho
      have e2 : o = 2 := by simpa [orc₂] using ho.symm
      subst e2
      exact (Array.getElem?_eq_some_iff.1 hz2).1)
    (hpins 4 (by rw [K12PaysOfLaw210.pinned_10]; decide))

/-! ## ADDED: `Pays` over `back_210W`: «left» member by member, the word laid in -/

/-- **What the invariant's test on the state's shape says at border 10** (the tables' files'
shape₂, Johnson/RunOne/BorderShapes/LKFU/Shape23.lean), the four clauses that this row reads: G_omega is
group 1 · messages 2 and 3 are sampled, with a sample rows each · G_omega's members are [2, 3], with
one open row, its test not begun. Opened in those files' own way (`bookStep_of_shape₂`). -/
theorem shape210_facts (S : LinShape) (a : ℕ) (d : St₂)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 10 d) = true) :
    d.loc.gOmega = 1 ∧ LKFU.Shape23.msgIs d.st 2 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 3 (some a) false = true ∧
      LKFU.Shape23.grpIs d.st 1 [2, 3] 1 0 false = true := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.and_true] at h
  obtain ⟨-, -, -, -, -, -, h7, -, -, -, h11, -, -, h14, -⟩ := h
  have g1 : d.loc.gOmega = 1 := by
    rw [if_neg (by decide)] at h7
    simpa using (Bool.and_eq_true_iff.1 h7).2
  have m23 : LKFU.Shape23.msgIs d.st 2 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 3 (some a) false = true := by simpa using h11
  exact ⟨g1, m23.1, m23.2, by simpa using h14⟩

/-- **What `back_210W` (K12Members210.lean) still owes of the verifier's state and the strings in
front**, a field a debt: what speaks of a; the public debts are `pays_210S`'s own binders. -/
structure Debts210S (π : P12) (oNo : Sound.Mem → ℕ) (a : (P₂ × St₂) × Fr₂.E.Str) : Prop where
  /-- the sendings' invariant at Omega (the statement's message 2; the six's member 4) -/
  seed2 : ∃ ρ yv, K1.SeedIs csKey (six.get i4).1 a.1.2.st 2 ρ yv
  /-- … and at the shared split's masks (message 3; member 5) -/
  seed3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 a.1.2.st 3 ρ yv
  /-- the split's masks' tree is no deeper than the first stage's mask code -/
  dep : ∀ t, Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
    (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
    (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a
  /-- where the book places a member's message, the tree there stands and has the told shape -/
  tree : ∀ (i : Fin six.length) (o : ℕ), (i = i5 ∧ o = 3) ∨ (i = i4 ∧ o = 2) → ∀ q : ℕ × ℕ,
    a.1.2.book.place[o]? = some q → atSix i.val = (off₂ q.1, q.2) →
    ∀ u, F.oracleAt (seatAt six numSix atSix i).1 = some u →
    ∃ T, a.1.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape u
  /-- the OOD seeds' tie of the bridge, at the reading smpSt -/
  sm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
    (smpSt csKey oNo fun z : P₂ × St₂ => z.2.st) a.1 sixS i = some σ →
    ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a.1 ρ σ.2
  /-- every leaf of the two members' seats shows its symbol -/
  shown : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ a.2) i
  /-- no open row of the statement is marked as a sample row -/
  kinds : Means.OpenKinds a.1.2.st

/-- **`Pays` at row 2.10, over `back_210W`.** Against `pays_210`: `CoreLeft` is gone; what the
invariant's test on the state's shape says is read off the invariant; the rest of the debts on the
state are `Debts210S`, under the piece's accepting run. -/
theorem pays_210S {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 10 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 b →
      on 11 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 10) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hft : π.nums.firstTree = 0)
    (hj : johOk π r = true)
    (hoff : ∀ q, off₂ q = numAt t₁ t₂ 1 (.own 0) + q)
    (ho2 : oNo ⟨sixS, i4⟩ = 2) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hf2 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i4).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i4).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (hF : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.SeatFits F csKey [six.get i] (fun _ => seatAt six numSix atSix i))
    (hd : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ u,
      F.oracleAt (seatAt six numSix atSix i).1 = some u →
      ∀ e ∈ Fr₂.all, e.no = (seatAt six numSix atSix i).1 → e.a ≤ u.logLength)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hE : ∀ a τ b, on 10 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts210S F Fr₂ orc₁ off₂ π oNo a)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (heval : ∀ a, on 10 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (hbase : base = numAt t₁ t₂ 1 (.own π.nums.free))
    (Lc mC mS mW : Sg → ℕ → ℕ) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn Fr₂ π (numAt t₁ t₂ 1) Lc mC mS mW (fun s => r s.st)
      (numAt t₁ t₂ 1 (.own π.nums.free)) dB dt εt)
    (hP : PayPub π (fun s => r s.st) dB.entry.rows v₀)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog64 : dB.entry.logN ≤ 64)
    (hv : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free)
    (hle : Err.le ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 10 base (dB :: dt) []
      x' := by
  have shp : ∀ a, on 10 a → a.1.2.loc.gOmega = 1 ∧
      LKFU.Shape23.msgIs a.1.2.st 2 (some a₀) false = true ∧
      LKFU.Shape23.msgIs a.1.2.st 3 (some a₀) false = true ∧
      LKFU.Shape23.grpIs a.1.2.st 1 [2, 3] 1 0 false = true := fun a ha => by
    obtain ⟨hshape, _, _, _⟩ := id ((hin a ha).resolve_left (fun h => h trivial))
    exact shape210_facts S a₀ a.1.2 hshape
  refine K12PaysOfLaw210.pays_of_law F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π t₁
    t₂ r rdN on hin hbk Bb fwd hal hp hSm base hpins dB dt x' (fun a τ b ha hout hq => ?_)
    (fun a ha => by
      obtain ⟨z, hz, hzs, _⟩ := K12Law32Core.msgIs_facts _ _ _ (shp a ha).2.1
      exact ⟨z, hz, hzs⟩)
    hnum₁ heval hbase Lc mC mS mW e v₀ εt hA hP h1 hlog64 hv ho hPl hne hfr hle
  obtain ⟨g1, _, _, hg⟩ := shp a ha
  obtain ⟨G1, hG1, hm1, hr1⟩ := K12Law32Core.grpIs_facts _ _ _ _ _ _ hg
  have hE' := hE a τ b ha hout
  have one : ∀ G0, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G0 → G0 = G1 := fun G0 hG0 => by
    rw [g1, hG1] at hG0
    exact (Option.some.inj hG0).symm
  exact K12Members210.back_210W F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π t₁ t₂ r
    rdN oNo mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal hp a b τ hout hq
    (hin a ha) hj hft hoff (fun G0 hG0 => by rw [one G0 hG0]; exact hm1)
    (fun G0 hG0 => by rw [one G0 hG0]; omega) hE'.seed2 hE'.seed3 ho2 ho3 hE'.dep hf2 hf3 hF
    hE'.tree hd hi hlog told hE'.sm hE'.shown hmem3 hmem2 hE'.kinds hSm
    (hpins 4 (by rw [K12PaysOfLaw210.pinned_10]; decide))

end Johnson.RunOne.Law.K12Pays210

#print axioms Johnson.RunOne.Law.K12Pays210.pays_210
#print axioms Johnson.RunOne.Law.K12Pays210.shape210_facts
#print axioms Johnson.RunOne.Law.K12Pays210.pays_210S
