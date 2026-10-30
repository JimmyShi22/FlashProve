-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/OffWalk.lean: THE ROWS THAT
RIDE IN THE RECORD READ 0 ON EVERY TABLE THAT THE STATEMENT HAS NOT, AT EVERY BORDER OF THE TWO
LOOKUPS' LINKS: the one premise (OffTables, Johnson/Desc/Key/RowHoldsSays.lean)
under which "a row holds" in machine elements is Means.Says: carried along the history: where the
layer makes a lookup's rows they have it (TieRows.lean); no later block of the links turns a row, or
which tables the statement has.

Main names:
  RowsOff s: every row of every list of rows in the record has OffTables at the record's statement.
  off_same: OffTables reads of a statement which tables it has.
  off_rowsInOrder: the rows that the layer makes have it.
  link_off: the step across each of a link's six blocks, beside the record's half in front.
  off_of_hist: Hist₁ (Key.descriptionFromSource X N P) D k a ⊢ RowsOff a.2, 2 ≤ k ≤ 2 + 6 · the number of lookups.
  KeysLow s: every mask entry that a claim on keys in the record names lies in a message of the
    record's statement. low_keyClaims, link_low, low_of_hist: the like walk for it.

Object: the blocks of Key.descriptionFromSource X N P's first chain up to the end of the lookups' links.
User: FieldsLayer.lean and FieldR110.lean call off_of_hist and low_of_hist.
Letters: X, N, P, D. Premises: those of rec_of_hist (RecOfHist.lean).

Limits. Up to the end of the links. Nothing on soundness.

-/
import Johnson.RunOne.Law.RecOfHist
import Johnson.RunOne.Law.TieRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.OffWalk
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source OffTables lookupSeat lookupLink
  lookupPlace rowsInOrder rowOfClaim)
open Johnson.RunOne.Sound (FK fk_link_at)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.TieRows
open LPFD (Hist₁ Reached)

/-- Every row that rides in the record reads 0 on every table that the record's statement has not.
-/
def RowsOff (s : FirstState) : Prop :=
  ∀ rows ∈ s.base.rows, ∀ r ∈ rows, OffTables Reading.gl s.d.st r

/-- OffTables reads of a statement which tables it has. -/
theorem off_same {S S' : Statement} (h : SameTables S S') {r : Row}
    (hr : OffTables Reading.gl S r) : OffTables Reading.gl S' r := by
  intro o pt i hh
  refine hr o pt i ?_
  have e := h.2 o pt
  unfold Means.tableSize at e
  rw [hh, if_neg (by simp)] at e
  cases hs : S.has o pt with
  | false => rfl
  | true =>
    rw [hs, if_pos rfl] at e
    have : 0 < 2 ^ S.tableBits o pt := Nat.pow_pos (by omega)
    omega

/-- The rows that the layer makes have OffTables. -/
theorem off_rowsInOrder {St : Statement} {F : Fork} {homeA : Array Slot}
    (hIn : ∀ s ∈ homeA.toList, s.index < Means.tableSize St s.oracle .mask) (x : WfPublic)
    (codes : Codes) (i : ℕ) (hx : St.has x.messageId .main = true)
    (tab : List (Bool × ℕ × Bool)) (cls : List Claim) (rows : List Row)
    (h : rowsInOrder (Wf.planesAt x codes i) tab F homeA cls = some rows) :
    ∀ R ∈ rows, OffTables Reading.gl St R := by
  unfold rowsInOrder at h
  simp only at h
  split at h
  · cases h
  · intro R hR
    obtain ⟨t, -, ht⟩ := TieRows.mapM_mem _ _ _ h R hR
    obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.1 ht
    cases c with
    | inl a => exact off_rowOfAff hIn hc
    | inr c => exact off_rowOfPlane hIn x codes i hx _ hc

section
variable {one : OneTime} {set : Setting} {id : ℕ} {m : Wf.Matrix} {L : ℕ → WfLookup}
  {oL kL : ℕ → List ℕ} {idxN : ℕ} {Prom : ℕ → FirstState → Prop}

/-- **The step across each of a link's six blocks.** -/
theorem link_off (i j : ℕ) (hj : j < 6) (c : Block FirstState Claim)
    (hc : (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]? = some c) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hr : RecL one set id m L oL kL idxN Prom i j s) (ho : RowsOff s)
    (hy : c.decide s rs gs = .ok s') : RowsOff s' := by
  obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat one set i (Wf.lookupOf id m (L i))
  rw [hF] at hc
  have c6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases c6 with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i (Wf.lookupOf id m (L i))).lay s = .ok s' := (d0 s rs gs) ▸ hy
    obtain rfl := lay_same hy'
    exact ho
  · obtain rfl := Option.some.inj hc
    obtain ⟨-, -, o, k, t1, t2, -, rfl⟩ := callerD_law hy
    exact fun rows hrows r hrr =>
      off_same ((takeMasksP_same t1).trans (takeMasksP_same t2)) (ho rows hrows r hrr)
  · obtain rfl := Option.some.inj hc
    obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ hy
    exact ho
  · obtain rfl := Option.some.inj hc
    obtain ⟨⟨hI, G, g, hG, hg, -⟩, -⟩ := hr
    obtain ⟨cls, s1, F, g', rows, keys, e1, -, -, e4, -, rfl⟩ := layerD_law hy
    obtain ⟨pl, H', u, -, -, rfl⟩ := claimsD_law hG hg e1
    intro rws hrws r hrr
    rcases List.mem_append.1 hrws with h1 | h1
    · exact ho rws h1 r hrr
    · obtain rfl := List.mem_singleton.1 h1
      have e4' : rowsInOrder (Wf.planesAt one.ranges one.codes i) _ F s.base.home cls =
          some rws := e4
      rw [hI.1] at e4'
      refine off_rowsInOrder (St := s.d.st) (fun z hz => (hI.2.1.2 z hz).2) one.ranges one.codes i
        ?_ _ cls rws e4' r hrr
      refine has_of_lt (i := 0) ?_
      rw [hI.2.1.1.size]
      exact Nat.pow_pos (by omega)
  · obtain rfl := Option.some.inj hc
    have hy' := hy
    rw [d4 s rs gs] at hy'
    obtain rfl := after_same hy'
    exact ho
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i (Wf.lookupOf id m (L i))).clear s = .ok s' := (d5 s rs gs) ▸ hy
    obtain rfl := clear_eq hy'
    exact ho

end

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- At the borders in front of the first layer the record holds no rows. -/
theorem no_rows (k : ℕ) (h2 : 2 ≤ k) (h5 : k ≤ 5) (s : FirstState) (hr : RecAt X k s) :
    s.base.rows = [] := by
  have c : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  have len : s.base.rows.length = 0 := by
    rcases c with rfl | rfl | rfl | rfl
    · exact ((recAt_link X 0 0 (by omega) s).1 hr).1
    · exact ((recAt_link X 0 1 (by omega) s).1 hr).1.2.2
    · exact ((recAt_link X 0 2 (by omega) s).1 hr).1.2.2.2.1
    · exact ((recAt_link X 0 3 (by omega) s).1 hr).1.1.2.2.1
  exact List.length_eq_zero_iff.1 len

/-- **A RECORD THAT WAS REACHED HOLDS ROWS WITH OffTables ALONE.** -/
theorem off_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) :
    ∀ (k : ℕ), 2 ≤ k → k ≤ 2 + 6 * X.Y.k.oneTime.ranges.lookups.length →
      ∀ a, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D k a → RowsOff a.2
  | 0, h2, _, _, _ => absurd h2 (by omega)
  | k + 1, h2, hk, a, h => by
    rcases Nat.lt_or_ge (k + 1) 6 with h6 | h6
    · intro rows hrows
      rw [no_rows (k + 1) h2 (by omega) a.2 (rec_of_hist D y hp hR ha (k + 1) hk a h)] at hrows
      cases hrows
    · obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
      rw [List.getElem?_map] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨l, j, hj, rfl⟩ : ∃ l j, j < 6 ∧ k = 2 + (6 * l + j) :=
        ⟨(k - 2) / 6, (k - 2) % 6, Nat.mod_lt _ (by omega), by omega⟩
      have hl : l < X.Y.k.oneTime.ranges.lookups.length := by omega
      have hc := (fk_link_at X N P l j hj _ (look_at X.Y.k.oneTime l hl)).symm.trans hb₀
      exact link_off l j hj b₀ hc a'.2 a.2 _ _
        ((recAt_link X l j hj a'.2).1 (rec_of_hist D y hp hR ha _ (by omega) a' hr))
        (off_of_hist D y hp hR ha _ (by omega) (by omega) a' hr)
        (VerifiableInference.Desc.Plain.held_decide b₀ a' _ _ a hd).2

/-! ## The claims on keys in the record name mask entries of the statement's messages -/

/-- Every mask entry that a claim on keys in the record names lies in a message of the record's
statement. -/
def KeysLow (s : FirstState) : Prop :=
  ∀ keys ∈ s.base.keys, ∀ c ∈ keys, ∀ q ∈ c.masks, q.1.oracle < s.d.st.oracles.size

/-- The claims on the keys that the layer makes name entries at the table of homes alone. -/
theorem low_keyClaims {S : Lkp.Public} {F : Fork} {homeA : Array Slot} {g : HeardG}
    {keys : List Lkp.Keys} {n : ℕ} (hIn : ∀ z ∈ homeA.toList, z.oracle < n)
    (h : keyClaims S F homeA g = some keys) : ∀ c ∈ keys, ∀ q ∈ c.masks, q.1.oracle < n := by
  intro c hc q hq
  unfold keyClaims at h
  obtain ⟨k, -, hk⟩ := TieRows.mapM_mem _ _ _ h c hc
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hk
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show q ∈ Psc.scaleForm (negE oneE) y.1 from hq)
  exact hIn _ (maskSide_slots hy t ht)

section
variable {one : OneTime} {set : Setting} {id : ℕ} {m : Wf.Matrix} {L : ℕ → WfLookup}
  {oL kL : ℕ → List ℕ} {idxN : ℕ} {Prom : ℕ → FirstState → Prop}

/-- The step across each of a link's six blocks. -/
theorem link_low (i j : ℕ) (hj : j < 6) (c : Block FirstState Claim)
    (hc : (lookupLink one set i (Wf.lookupOf id m (L i))).blocksInOrder[j]? = some c) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hr : RecL one set id m L oL kL idxN Prom i j s) (ho : KeysLow s)
    (hy : c.decide s rs gs = .ok s') : KeysLow s' := by
  obtain ⟨c0, c4, c5, hF, d0, d4, d5⟩ := link_flat one set i (Wf.lookupOf id m (L i))
  rw [hF] at hc
  have c6 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases c6 with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i (Wf.lookupOf id m (L i))).lay s = .ok s' := (d0 s rs gs) ▸ hy
    obtain rfl := lay_same hy'
    exact ho
  · obtain rfl := Option.some.inj hc
    obtain ⟨-, -, o, k, t1, t2, -, rfl⟩ := callerD_law hy
    intro keys hk c hcc q hq
    show q.1.oracle < k.2.st.oracles.size
    rw [((takeMasksP_same t1).trans (takeMasksP_same t2)).1]
    exact ho keys hk c hcc q hq
  · obtain rfl := Option.some.inj hc
    obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ hy
    exact ho
  · obtain rfl := Option.some.inj hc
    obtain ⟨⟨hI, G, g, hG, hg, -⟩, -⟩ := hr
    obtain ⟨cls, s1, F, g', rows, keys, e1, -, -, -, e5, rfl⟩ := layerD_law hy
    obtain ⟨pl, H', u, -, -, rfl⟩ := claimsD_law hG hg e1
    intro ks hks c hcc q hq
    rcases List.mem_append.1 hks with h1 | h1
    · exact ho ks h1 c hcc q hq
    · obtain rfl := List.mem_singleton.1 h1
      have e5' : keyClaims (Wf.lookupOf id m (L i)) F s.base.home g' = some ks := e5
      rw [hI.1] at e5'
      exact low_keyClaims (n := s.d.st.oracles.size) (fun z hz => (hI.2.1.2 z hz).1) e5' c hcc q hq
  · obtain rfl := Option.some.inj hc
    have hy' := hy
    rw [d4 s rs gs] at hy'
    obtain rfl := after_same hy'
    exact ho
  · obtain rfl := Option.some.inj hc
    have hy' : (lookupLink one set i (Wf.lookupOf id m (L i))).clear s = .ok s' := (d5 s rs gs) ▸ hy
    obtain rfl := clear_eq hy'
    exact ho

end

/-- **A RECORD THAT WAS REACHED HOLDS CLAIMS ON KEYS THAT NAME THE STATEMENT'S MESSAGES ALONE.** -/
theorem low_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) :
    ∀ (k : ℕ), 2 ≤ k → k ≤ 2 + 6 * X.Y.k.oneTime.ranges.lookups.length →
      ∀ a, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D k a → KeysLow a.2
  | 0, h2, _, _, _ => absurd h2 (by omega)
  | k + 1, h2, hk, a, h => by
    rcases Nat.lt_or_ge k 2 with h6 | h6
    · obtain rfl : k = 1 := by omega
      have hr := (recAt_link X 0 0 (by omega) a.2).1 (rec_of_hist D y hp hR ha 2 hk a h)
      intro keys hkeys
      rw [List.length_eq_zero_iff.1 hr.2.1] at hkeys
      cases hkeys
    · obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
      rw [List.getElem?_map] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨l, j, hj, rfl⟩ : ∃ l j, j < 6 ∧ k = 2 + (6 * l + j) :=
        ⟨(k - 2) / 6, (k - 2) % 6, Nat.mod_lt _ (by omega), by omega⟩
      have hl : l < X.Y.k.oneTime.ranges.lookups.length := by omega
      have hc := (fk_link_at X N P l j hj _ (look_at X.Y.k.oneTime l hl)).symm.trans hb₀
      exact link_low l j hj b₀ hc a'.2 a.2 _ _
        ((recAt_link X l j hj a'.2).1 (rec_of_hist D y hp hR ha _ (by omega) a' hr))
        (low_of_hist D y hp hR ha _ (by omega) (by omega) a' hr)
        (VerifiableInference.Desc.Plain.held_decide b₀ a' _ _ a hd).2

end Johnson.RunOne.Law.OffWalk

#print axioms Johnson.RunOne.Law.OffWalk.off_same
#print axioms Johnson.RunOne.Law.OffWalk.off_rowsInOrder
#print axioms Johnson.RunOne.Law.OffWalk.link_off
#print axioms Johnson.RunOne.Law.OffWalk.off_of_hist
#print axioms Johnson.RunOne.Law.OffWalk.link_low
#print axioms Johnson.RunOne.Law.OffWalk.low_of_hist
