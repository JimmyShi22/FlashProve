-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeLinkClosed.lean: A LOOKUP's HEARING AND THE SUB-PROTOCOL BEHIND ITS ROUNDS ("layer"), ON
THE FIRST CHAIN's SHAPE, AS CLOSED FORMS: what their guards (`gHear`, E2E/KeyShapeHear.lean;
`gLayer`, E2E/KeyShapeLayer.lean) return, written so that no long list is walked. Statements on
guards on shapes and their proofs: NOTHING IS SHOWN OF ANY PROVER, and nothing of the verifier's
sub-protocols themselves: that is `hear_exact`'s and `layer_exact`'s.

What for. At the full size a lookup has some 17,800 hidden values. The hearing's guard asks that as
many marks are free; the layer's guard asks of every hidden value's home that it lies inside its
table and in front of the pad. Lean's kernel does not walk such lists. Here these clauses are paid
by laws.

  `freeB_fresh`: in the fresh ledger's shape all slots are there and free.
  **`hear_closed`**: the hearing's guard at a shape whose open ledger is the fresh one. Its two
    clauses on public values (the face's own test; the rounds can be made) are premises: they are
    clauses of that sub-protocol's own test on public values.
  `freeNo_mono`: the free entries' numbers rise. `ownAt_ok`: so all entries handed out lie inside
    the table and in front of the pad where the entry behind the last one does.
  **`homesB_formula`**: the layer's clause on the homes, at the homes as
    E2E/KeyShapeCallerClosed.lean writes them: E2E/KeyShapeFirst.lean's `zip_homesFrom` and
    E2E/KeyLookupAround.lean's `homes_size`: CALLED.
  **`layer_closed`**: the layer's guard. Left as premises for an evaluation at written sizes: a
    public test on the own message's blocks; the lengths of the claims' points; the homes of the
    hidden values that the claims on keys name (two a part).
  `runL`, `runL_cons`, `runL_append`: guards in a row.
  `linkT`, **`link_closed`**: A LOOKUP's LINK, ALL SIX GUARDS IN A ROW: the shape behind, written:
    the two ledgers moved on; a count of rows and the claims' slots more.

Limits.
- Enough, not needed.
- What the hearing leaves of the ledger (`lookUpd`) and of what was heard (`heardOf`) stay formulas.


-/
import E2E.KeyShapeCallerClosed
import E2E.KeyShapeLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params Fmt.Places
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First.Shape (freeB sizedB)
open VerifiableInference.Desc.K3 (Face faceOfLkp fromKeys homesFrom homes)
open VerifiableInference.Desc.Key (lookupPlace)
open ProofFile.Honest.K3.Shape (lookUpd)
open AtPublicFiles.KeyShape (Sh₁ Pub1 gHear gLayer lookAt msgOf freshLed heardOf homesB ownOk sizeB padP
  blocksB slotsAt zip_homesFrom)

variable {Bk : Type} (Q : Pub1)

/-! ## The hearing -/

theorem freeB_fresh (n : Nat) : freeB (freshLed n) 0 n = true := by
  have e1 : sizedB (freshLed n) = true := by
    show (n == n && n == n && (List.replicate n false).length == n) = true
    rw [List.length_replicate]
    simp
  have e2 : (((freshLed n).got.drop 0).take n).all (!·) = true := by
    show (((List.replicate n false).drop 0).take n).all (!·) = true
    rw [List.all_eq_true]
    intro x hx
    have hx' : x ∈ List.replicate n false := List.mem_of_mem_take hx
    rw [(List.mem_replicate.1 hx').2]
    rfl
  unfold freeB
  rw [e1, e2]
  show (true && decide (0 + n ≤ n) && true) = true
  simp

/-- **The hearing's guard, closed.** -/
theorem hear_closed (i : Nat) (a : Sh₁ Bk)
    (hled : a.2.look.led = some (some (freshLed (faceOfLkp (lookAt Q.one i)).slots)))
    (hok : (faceOfLkp (lookAt Q.one i)).ok = true)
    (hes : (lookupPlace Q.set i (lookAt Q.one i)).entries.isSome = true)
    (hp : 1 ≤ (faceOfLkp (lookAt Q.one i)).parts.length) (hk : a.2.look.keys.length = i) :
    gHear Q i a = .ok (a.1, { a.2 with look := { a.2.look with
      led := some (some (lookUpd (faceOfLkp (lookAt Q.one i))
        (freshLed (faceOfLkp (lookAt Q.one i)).slots)))
      heard := some (heardOf (faceOfLkp (lookAt Q.one i))) } }) := by
  unfold gHear
  dsimp only
  rw [hled]
  dsimp only
  rw [if_pos (by
    rw [hok, hes, hk, freeB_fresh]
    show (true && true && decide (1 ≤ _) && i == i && true && (0 : Nat) == 0 &&
      (faceOfLkp (lookAt Q.one i)).slots == (faceOfLkp (lookAt Q.one i)).slots) = true
    simp [hp])]

/-! ## The homes -/

/-- The free entries' numbers rise. -/
theorem freeNo_mono {m : Nat} (hm : 0 < m) {j j' : Nat} (h : j ≤ j') :
    freeNo m j ≤ freeNo m j' := by
  unfold freeNo entryNo freeAt
  dsimp only
  have hq := le_two_pow_logUp m
  have hd : j / m ≤ j' / m := Nat.div_le_div_right h
  rcases Nat.lt_or_ge (j / m) (j' / m) with c | c
  · have h1 : j % m < m := Nat.mod_lt _ hm
    have h2 : 2 ^ logUp m * (j / m + 1) ≤ 2 ^ logUp m * (j' / m) := Nat.mul_le_mul_left _ c
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  · have e : j / m = j' / m := Nat.le_antisymm hd c
    have h1 : m * (j / m) + j % m = j := Nat.div_add_mod j m
    have h2 : m * (j' / m) + j' % m = j' := Nat.div_add_mod j' m
    rw [e] at h1 ⊢
    omega

/-- All entries of the own message that are handed out lie inside its table and in front of its pad,
where the entry behind the last one does. Enough, not needed. -/
theorem ownAt_ok (i : Nat) (l : Ledger) (k : Nat) (hm : 0 < l.rows)
    (hb : freeNo l.rows (k + ((faceOfLkp (lookAt Q.one i)).slots -
      2 * (faceOfLkp (lookAt Q.one i)).parts.length)) < min (sizeB Q.one) (padP Q.one)) :
    ∀ s ∈ ownAt Q i l k, ownOk Q.one s = true := by
  intro s hs
  unfold ownAt at hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' := List.mem_range.1 hj
  have hle := freeNo_mono hm (j := k + j) (j' := k + ((faceOfLkp (lookAt Q.one i)).slots -
    2 * (faceOfLkp (lookAt Q.one i)).parts.length)) (by omega)
  have h1 : freeNo l.rows (k + j) < sizeB Q.one := by omega
  have h2 : freeNo l.rows (k + j) < padP Q.one := by omega
  unfold ownOk
  simp [h1, h2]

/-- **The layer's clause on the homes, at the homes' formula.** -/
theorem homesB_formula (i idx : Nat) (l₁ : Ledger) (k₁ : Nat) (l₂ : Ledger) (k₂ : Nat)
    (hm : 0 < l₁.rows)
    (hb : freeNo l₁.rows (k₁ + ((faceOfLkp (lookAt Q.one i)).slots -
      2 * (faceOfLkp (lookAt Q.one i)).parts.length)) < min (sizeB Q.one) (padP Q.one))
    (hp : ∀ v ∈ (faceOfLkp (lookAt Q.one i)).parts, 1 ≤ v) :
    homesB Q.one (faceOfLkp (lookAt Q.one i))
      (homesFrom (fromKeys (faceOfLkp (lookAt Q.one i))) (ownAt Q i l₁ k₁)
        (idxAt Q i idx l₂ k₂)) = true := by
  have hlen : (homesFrom (fromKeys (faceOfLkp (lookAt Q.one i))) (ownAt Q i l₁ k₁)
      (idxAt Q i idx l₂ k₂)).length = (faceOfLkp (lookAt Q.one i)).slots := by
    have := AtPublicFiles.KeyLookup.homes_size hp (o := ownAt Q i l₁ k₁) (k := idxAt Q i idx l₂ k₂)
      (by unfold ownAt; rw [List.length_map, List.length_map, List.length_range])
      (by unfold idxAt; rw [List.length_map, List.length_map, List.length_range])
    unfold homes at this
    rwa [List.size_toArray] at this
  unfold homesB
  rw [hlen, zip_homesFrom (ownOk Q.one) _ _ _ (ownAt_ok Q i l₁ k₁ hm hb)]
  simp

/-! ## The layer -/

/-- **The layer's guard, closed.** W: the lookup's public values; L: whatever the open ledger's
shape is; sl: the homes of the hidden values that the claims on keys name. -/
theorem layer_closed (i : Nat) (a : Sh₁ Bk) (W : WfLookup)
    (L : VerifiableInference.Desc.First.Shape.LedSh) (sl : List (List Slot))
    (hW : Q.one.ranges.lookups[i]? = some W) (hled : a.2.look.led = some (some L))
    (hh : a.2.look.heard = some (heardOf (faceOfLkp (lookAt Q.one i))))
    (hk : a.2.look.keys.length = i)
    (hhome : homesB Q.one (faceOfLkp (lookAt Q.one i)) a.2.look.home = true)
    (hpl : a.2.look.plain = true) (hko : a.2.look.keysOk = true) (hbl : blocksB Q.one i = true)
    (hpts : ((heardOf (faceOfLkp (lookAt Q.one i))).keys.map (·.1) ==
      W.parts.map fun p => (Wf.matrixOf Q.one.lin).kCol + p.logPlaces) = true)
    (hsl : ((heardOf (faceOfLkp (lookAt Q.one i))).keys.mapM fun k =>
      slotsAt a.2.look.home k.2) = some sl) :
    gLayer Q i a = .ok (a.1, { a.2 with look := { a.2.look with
      led := some none
      heard := some { heardOf (faceOfLkp (lookAt Q.one i)) with mark := false }
      rows := a.2.look.rows ++ [(heardOf (faceOfLkp (lookAt Q.one i))).rows + 3]
      keys := a.2.look.keys ++ [sl] } }) := by
  unfold gLayer
  dsimp only
  rw [hW, hled, hh]
  dsimp only
  rw [if_pos (by
    rw [hk, hhome, AtPublicFiles.KeyLookup.fromKeys_length, hpl, hko, hbl, hpts]
    show (true && i == i && true && (faceOfLkp (lookAt Q.one i)).slots ==
      (faceOfLkp (lookAt Q.one i)).slots && true && true && true && true) = true
    simp), hsl]

/-! ## A whole link -/

/-- Guards in a row. -/
def runL {Sh : Type} (gs : List (Sh → Except String Sh)) (a : Sh) : Except String Sh :=
  gs.foldl (fun x g => x.bind g) (.ok a)

theorem runL_cons {Sh : Type} (g : Sh → Except String Sh) (gs : List (Sh → Except String Sh))
    (a b : Sh) (h : g a = .ok b) : runL (g :: gs) a = runL gs b := by
  show gs.foldl _ ((Except.ok a).bind g) = _
  show gs.foldl _ (g a) = _
  rw [h]
  rfl

theorem runL_append {Sh : Type} (gs hs : List (Sh → Except String Sh)) (a b : Sh)
    (h : runL gs a = .ok b) : runL (gs ++ hs) a = runL hs b := by
  unfold runL at h ⊢
  rw [List.foldl_append, h]

/-- The shape behind the hearing, written. -/
def hearT (i : Nat) (a : Sh₁ Bk) : Sh₁ Bk :=
  (a.1, { a.2 with look := { a.2.look with
    led := some (some (lookUpd (faceOfLkp (lookAt Q.one i))
      (freshLed (faceOfLkp (lookAt Q.one i)).slots)))
    heard := some (heardOf (faceOfLkp (lookAt Q.one i))) } })

/-- **The shape behind a lookup's link**, written. -/
def linkT (i : Nat) (a : Sh₁ Bk) (l₁ : Ledger) (k₁ : Nat) (l₂ : Ledger) (k₂ : Nat)
    (sl : List (List Slot)) : Sh₁ Bk :=
  ((callerT Q i a l₁ k₁ l₂ k₂).1, { a.2 with look := { a.2.look with
    led := none, heard := none, home := []
    rows := a.2.look.rows ++ [(heardOf (faceOfLkp (lookAt Q.one i))).rows + 3]
    keys := a.2.look.keys ++ [sl] } })

/-- **A LOOKUP's LINK, ALL SIX GUARDS IN A ROW, CLOSED.** -/
theorem link_closed (i : Nat) (a : Sh₁ Bk) (l₁ : Ledger) (k₁ : Nat) (l₂ : Ledger) (k₂ : Nat)
    (W : WfLookup) (sl : List (List Slot))
    (ht : a.2.tidy = true) (hled : a.2.look.led.isNone = true) (hk : a.2.look.keys.length = i)
    (hne : a.2.idx ≠ msgOf Q.one)
    (h1 : (a.1.st.oracles[msgOf Q.one]?).bind (·.ledger) = some l₁) (s1 : InStep l₁ k₁)
    (n1 : (faceOfLkp (lookAt Q.one i)).slots - 2 * (faceOfLkp (lookAt Q.one i)).parts.length ≤
      l₁.left)
    (h2 : (a.1.st.oracles[a.2.idx]?).bind (·.ledger) = some l₂) (s2 : InStep l₂ k₂)
    (n2 : 2 * (faceOfLkp (lookAt Q.one i)).parts.length ≤ l₂.left)
    (hp : ∀ v ∈ (faceOfLkp (lookAt Q.one i)).parts, 1 ≤ v)
    (hok : (faceOfLkp (lookAt Q.one i)).ok = true)
    (hes : (lookupPlace Q.set i (lookAt Q.one i)).entries.isSome = true)
    (hp1 : 1 ≤ (faceOfLkp (lookAt Q.one i)).parts.length)
    (hW : Q.one.ranges.lookups[i]? = some W)
    (hb : freeNo l₁.rows (k₁ + ((faceOfLkp (lookAt Q.one i)).slots -
      2 * (faceOfLkp (lookAt Q.one i)).parts.length)) < min (sizeB Q.one) (padP Q.one))
    (hpl : a.2.look.plain = true) (hko : a.2.look.keysOk = true) (hbl : blocksB Q.one i = true)
    (hpts : ((heardOf (faceOfLkp (lookAt Q.one i))).keys.map (·.1) ==
      W.parts.map fun p => (Wf.matrixOf Q.one.lin).kCol + p.logPlaces) = true)
    (hsl : ((heardOf (faceOfLkp (lookAt Q.one i))).keys.mapM fun k =>
      slotsAt (callerT Q i a l₁ k₁ l₂ k₂).2.look.home k.2) = some sl) :
    runL (AtPublicFiles.KeyShape.gLink Q i) a = .ok (linkT Q i a l₁ k₁ l₂ k₂ sl) := by
  have c1 : AtPublicFiles.KeyShape.gLaid a = .ok a := by
    unfold AtPublicFiles.KeyShape.gLaid
    rw [if_pos hled]
  have c2 := caller_closed Q i a l₁ k₁ l₂ k₂ ht hled hk hne h1 s1 n1 h2 s2 n2 hp
  have c3 : gHear Q i (callerT Q i a l₁ k₁ l₂ k₂) = .ok (hearT Q i (callerT Q i a l₁ k₁ l₂ k₂)) :=
    hear_closed Q i (callerT Q i a l₁ k₁ l₂ k₂) rfl hok hes hp1 hk
  have c4 := layer_closed Q i (hearT Q i (callerT Q i a l₁ k₁ l₂ k₂)) W _ sl hW rfl rfl hk
    (homesB_formula Q i a.2.idx l₁ k₁ l₂ k₂ s1.2.1 hb hp) hpl hko hbl hpts hsl
  unfold AtPublicFiles.KeyShape.gLink
  rw [runL_cons _ _ _ _ c1, runL_cons _ _ _ _ c2, runL_cons _ _ _ _ c3, runL_cons _ _ _ _ c4,
    runL_cons Except.ok _ _ _ rfl, runL_cons AtPublicFiles.KeyShape.gCleared _ _ _ rfl]
  rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.freeB_fresh
#print axioms AtPublicFiles.AtFiles.hear_closed
#print axioms AtPublicFiles.AtFiles.freeNo_mono
#print axioms AtPublicFiles.AtFiles.ownAt_ok
#print axioms AtPublicFiles.AtFiles.homesB_formula
#print axioms AtPublicFiles.AtFiles.layer_closed
#print axioms AtPublicFiles.AtFiles.runL_cons
#print axioms AtPublicFiles.AtFiles.runL_append
#print axioms AtPublicFiles.AtFiles.link_closed
