-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLookupOwned.lean: the laws of a lookup's row of parts, carried over to the row at a letter for
the owners (proverSideOfLookupInChain, K3/RowOwned.lean), which is what keyProver lays. The two rows differ in
the names of what their parts spend and in nothing else: so a row at owners plays as the row of
K3/Row.lean plays, at the same coins.

  SameBut p q, RowSame ps qs   two parts, two rows, that are one but for the names: with the map of
                coins, and their moves, stops and counts the same
  sameSum, sameOwned, rowOwned   that holds of the masked sumcheck's part at any names; of a stage's
                part; of the seated row
  seat_steps    the seated rows' steps are the same, at the coins that the map gives
  seat_rounds   they have as many rounds
  K3PlaysAtO, plays_k3O   the seven of K3PlaysAt at a row at owners; it plays
  fitsAt_k3O, accepted_k3O   the twins of fitsAt_k3, accepted_k3_shape (E2E/KeyLookupAccepted.lean)

Every law here is a conditional; what it is conditional on at the key file is other files'. Of
what the played values are worth nothing is said: Accepted says that the step returns.

Limits. E2E/KeyLookupAccepted.lean and the K3 laws beneath it were read at reading copies, not at a
built tree; the text of plays_k3O follows plays_k3S line for line. That the names of a row at
keyOwners are those of keyBook's entries is in no theorem here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PlaysAnyState
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import E2E.KeyLookupAccepted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block Place)

section Same
variable {V W X : Type}

/-- **Two parts that are one but for the names of what they spend.** -/
structure SameBut (p q : Part V W X) where
  /-- the coins of the one as the coins of the other -/
  back : p.Coins → q.Coins
  bad : p.bad = q.bad
  hid : p.hid = q.hid
  moves : p.moves = q.moves.map (Move.recoin back)

/-- A part is so with itself. -/
def SameBut.refl (p : Part V W X) : SameBut p p where
  back := fun c => c
  bad := rfl
  hid := rfl
  moves := by
    have e : ∀ l : List (Move p.Coins W X), l = l.map (Move.recoin fun c => c) := by
      intro l
      induction l with
      | nil => rfl
      | cons m l ih => exact congrArg₂ List.cons rfl ih
    exact e _

/-- The two have as many moves. -/
theorem SameBut.len {p q : Part V W X} (h : SameBut p q) : p.moves.length = q.moves.length := by
  rw [h.moves, List.length_map]

/-- Their steps are one, at the coins that the map gives. -/
theorem SameBut.steps {p q : Part V W X} (h : SameBut p q) (n : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V)
    (c : p.Coins) : p.steps n a rs v c = q.steps n a rs v (h.back c) := by
  have hl := h.len
  unfold Part.steps
  rw [h.bad, h.hid, hl, h.moves, List.zip_map_right, List.zipIdx_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  rfl

/-- **Two rows that are one but for the names.** -/
def RowSame : List (Part V W X) → List (Part V W X) → Type
  | [], [] => Unit
  | p :: ps, q :: qs => SameBut p q × RowSame ps qs
  | _, _ => Empty

/-- The row's coins as the other's. -/
def RowSame.back : {ps qs : List (Part V W X)} → RowSame ps qs → RowCoins ps → RowCoins qs
  | [], [], _, _ => ()
  | _ :: _, _ :: _, h, c => (h.1.back c.1, RowSame.back h.2 c.2)
  | [], _ :: _, h, _ => (h : Empty).elim
  | _ :: _, [], h, _ => (h : Empty).elim

/-- The steps of two such rows are one. -/
theorem RowSame.steps (name : String) (pl : Place) (v : Option V) :
    {ps qs : List (Part V W X)} → (h : RowSame ps qs) → (j : Nat) →
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) → (c : RowCoins ps) →
    rowSteps name pl v ps j rs c = rowSteps name pl v qs j rs (h.back c)
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, h, j, rs, c => by
    show _ ++ _ = _ ++ _
    rw [h.1.steps, h.1.len, RowSame.steps name pl v h.2]
    rfl
  | [], _ :: _, h, _, _, _ => (h : Empty).elim
  | _ :: _, [], h, _, _, _ => (h : Empty).elim

/-- Two such rows have as many rounds. -/
theorem RowSame.rounds : {ps qs : List (Part V W X)} → RowSame ps qs → (n : Nat) →
    ps.foldl (fun n p => n + p.moves.length) n = qs.foldl (fun n p => n + p.moves.length) n
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, h, n => by
    show List.foldl _ (n + _) _ = List.foldl _ (n + _) _
    rw [h.1.len, RowSame.rounds h.2]
  | [], _ :: _, h, _ => (h : Empty).elim
  | _ :: _, [], h, _ => (h : Empty).elim

/-- Parts made of one list by two functions, part by part so. -/
def RowSame.ofList {α : Type} (F G : α → Part V W X) (e : ∀ x, SameBut (F x) (G x)) :
    (L : List α) → RowSame (L.map F) (L.map G)
  | [] => ()
  | x :: L => (e x, RowSame.ofList F G e L)

end Same

section Lift
variable {V V' W W' X Y : Type}

/-- Placing two such parts keeps them so. -/
def SameBut.lift {p q : Part V' W' Y} (h : SameBut p q) (see : V → V') (wit : W → W') (get : X → Y)
    (set : X → Y → X) : SameBut (p.lift see wit get set) (q.lift see wit get set) where
  back := h.back
  bad := h.bad
  hid := by
    show (fun v => p.hid (see v)) = fun v => q.hid (see v)
    rw [h.hid]
  moves := by
    show p.moves.map (Move.lift wit get set) =
      (q.moves.map (Move.lift wit get set)).map (Move.recoin h.back)
    rw [h.moves, List.map_map, List.map_map]
    rfl

/-- Two such rows, placed. -/
def RowSame.lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X) :
    {ps qs : List (Part V' W' Y)} → RowSame ps qs →
    RowSame (ps.map (Part.lift see wit get set)) (qs.map (Part.lift see wit get set))
  | [], [], _ => ()
  | _ :: _, _ :: _, h => (h.1.lift see wit get set, RowSame.lift see wit get set h.2)
  | [], _ :: _, h => (h : Empty).elim
  | _ :: _, [], h => (h : Empty).elim

end Lift

section Rows
variable {V W X V₁ W₁ X₁ : Type}

/-- **The masked sumcheck's part at two pairs of names.** Nothing of its moves reads a name. -/
def sameSum (n₁ e₁ n₂ e₂ : String) (J : SumJob W X) :
    SameBut (sumPart (V := V) n₁ e₁ J) (sumPart n₂ e₂ J) := by
  obtain ⟨⟨lead, vs, ends⟩, pts, ld, rd, iy, en⟩ := J
  cases ends with
  | none =>
    exact ⟨fun c => c, rfl, rfl, (SameBut.refl (sumPart (V := V) n₂ e₂ _)).moves⟩
  | some e =>
    exact ⟨fun c => c, rfl, rfl, (SameBut.refl (sumPart (V := V) n₂ e₂ _)).moves⟩

/-- **A stage's part at owners and the same part of K3/Row.lean.** -/
def sameOwned (o : Owners) (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    SameBut (partOfOwned (V := V) o R J a s i) (partOf R J a s i) := by
  unfold partOfOwned partOf
  cases s.call a.face with
  | none => exact SameBut.refl _
  | some k => exact sameSum _ _ _ _ _

/-- **The seated row at owners and the seated row.** -/
def rowOwned (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    RowSame (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts :=
  RowSame.lift (fun _ => ()) wit (fun _ => ()) (fun x _ => x)
    (by
      show RowSame (((stages a.face).zipIdx).map fun x => partOfOwned (V := Unit) o R J a x.1 x.2)
        (((stages a.face).zipIdx).map fun x => partOf (V := Unit) R J a x.1 x.2)
      exact RowSame.ofList _ _ (fun x : Stage × Nat => sameOwned o R J a x.1 x.2) _)

/-- **Their steps are one.** -/
theorem seat_steps {S Cl : Type} (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (b : Block S Cl) (v : Option V₁)
    (c : RowCoins (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts) :
    (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).steps b v c =
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).steps b v
        ((rowOwned (V₁ := V₁) (X₁ := X₁) o R J wit a).back c) :=
  RowSame.steps b.name b.place v (rowOwned (V₁ := V₁) (X₁ := X₁) o R J wit a) 0 _ c

/-- **They have as many rounds.** -/
theorem seat_rounds (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).rounds =
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).rounds :=
  RowSame.rounds (rowOwned (V₁ := V₁) (X₁ := X₁) o R J wit a) 0

end Rows

end ProofFile.Honest.K3

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)
open VerifiableInference.Desc.K3 (entriesFit)
open AtPublicFiles.KeyShape (ExactAt)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb Wj : Type} (T : Thread Bk S Cl V W X Pb)

/-- **The seven of K3PlaysAt, at a row at owners.** -/
structure K3PlaysAtO (o : Owners) (b : Nat) (a : At) (J : LookJobs Wj) (wit : W → Wj)
    (es : List Fmt.Entry) : Prop where
  half : ∀ blk, T.bs[b]? = some blk → T.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChain o ⟨ptsOf, pointsAt⟩ J wit a)
  place : ∀ blk, T.bs[b]? = some blk → blk.place = a.place
  rounds : ∀ blk, T.bs[b]? = some blk → blk.rounds = es.map declOf
  oracles : ∀ blk, T.bs[b]? = some blk → blk.oracles = es.map fun _ => []
  ok : a.face.ok = true
  entries : entriesFit a.face es = true
  base : a.base = T.front + roundsTo T.bs b

variable {T}
variable {o : Owners} {b : Nat} {a : At} {J : LookJobs Wj} {wit : W → Wj} {es : List Fmt.Entry}

/-- **It plays** (Plays T b): plays_k3S's text, at the coins that rowOwned gives. Conditional on
K3PlaysAtO. -/
theorem plays_k3O (hS : K3PlaysAtO T o b a J wit es) : Plays T b := by
  intro blk hb k s m E ds l hA hd _ hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.half blk hb) l hl
  have hSt : Stands a es m ds :=
    ⟨hS.ok, (Thread.heard_length T hA.2.1).trans hS.base.symm, hS.entries,
      by rw [← hS.rounds blk hb]; exact hd⟩
  obtain ⟨y, hy, _, _, _⟩ := movedInner _ _ _ _ a J wit blk.name
    (T.φ.sees m.st.input) es m ds
    ((rowOwned (V₁ := V) (X₁ := X) o ⟨ptsOf, pointsAt⟩ J wit a).back c) 0 0
    (fun _ _ => none) (fun _ => none) hSt
  have hy' : play ((proverSideOfLookupInChain o ⟨ptsOf, pointsAt⟩ J wit a).steps blk (T.φ.sees m.st.input) c)
      ds [] m = .ok y := by
    rw [seat_steps, steps_eqS a J wit _ es blk (hS.place blk hb) (hS.rounds blk hb)
      (hS.oracles blk hb) _]
    exact hy
  refine ⟨y, [], ⟨⟨_, hl, hy'⟩, ?_⟩, ?_⟩
  · rw [hS.rounds blk hb, readsOf_plain]
    rfl
  · rw [fresh_nil T hb (by rw [hS.oracles blk hb]; simp)]
    intro σ hσ
    exact absurd hσ (List.not_mem_nil)

/-- What was played passes the step's own tests: fitsAt_k3's text at owners. -/
theorem fitsAt_k3O (hS : K3PlaysAtO T o b a J wit es) : FitsAt T b := by
  intro blk hblk
  exact fitsAt_half T hblk (hS.half blk hblk)
    (by rw [seat_rounds, lookSeat_rounds _ J wit a (two_le_planes_of_ok _ hS.ok),
      hS.rounds blk hblk, List.length_map, fit_length _ _ hS.entries])
    (by rw [hS.oracles blk hblk, hS.rounds blk hblk, List.length_map, List.length_map]) blk hblk

/-- **The lookup's sub-protocol is accepted**, by the cut of E2E/KeyLookupAccepted.lean, at a row at
owners. Conditional on the seven, the shape's run, (B1) and ExactAt at this member. -/
theorem accepted_k3O (hS : K3PlaysAtO T o b a J wit es) (Z : Shape S) {a₀ : Z.Sh}
    {n : Nat} {fall : Nat → S → List Fmt.Drawn → Option String} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true) (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j)
    (hE : ∀ blk, T.bs[b]? = some blk → ExactAt T.ft Z.sh blk (Z.g b)) : Accepted T fall b :=
  AtPublicFiles.KeyShape.accepted_of_exact T Z hn hb hyes hfirst hC hE (fitsAt_k3O hS)

end ProofFile.Honest.K3.Law.AtThr
